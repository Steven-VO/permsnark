// permcanon.cpp -- filter permutation words: keep one per isomorphism class
// and/or only the cyclically 5-edge-connected graphs.
//
// Input: permutation words as written by "permsnark -o perm", one per line
// (p(0) p(1) ... p(n-1)), standing for the permutation graph PG(p) of order
// 2n.  Output: the lines that pass the selected tests.  Each line is decided
// on its own, so the input may come in any order and in any number of pieces.
//
// -Y keeps exactly the lines "permsnark -Y -o perm" would have written: p is
// canonical iff p(0) = 0 and its difference list D(p) is lexicographically
// minimal among the 8n rotations of the eight lists of every labelling along
// every permutation 2-factor of PG(p) (see "Strong canonicity" in
// permsnark.cpp).  Two permutation graphs are isomorphic iff one arises from
// the other by a relabelling along such a 2-factor, so for the complete weak
// output of a run the result is one word per isomorphism class.  The blue
// cycle through vertex 0 is grown as in permsnark.cpp; the search stops at the
// first labelling that is smaller than D(p).
//
// -C keeps the cyclically 5-edge-connected graphs.  For n >= 5 a cyclic
// 4-edge-cut of PG(p) is exactly a *block*: an interval of 2..n-2 consecutive
// positions whose values form a cyclic interval too.  Blocks come in
// complementary pairs, so the intervals that do not wrap around suffice.
// Blocks of length 2 are 4-cycles, so -C implies girth >= 5.  For n < 5, -C
// keeps nothing.
//
// Build:  make permcanon              (runtime -n in [NMIN, NMAX])
// Usage:  ... | ./permcanon [-Y] [-C] [-n n] [-t threads] > filtered.txt
//         -Y (the default) keeps one word per isomorphism class, -C keeps the
//         cyclically 5-edge-connected words, -Y -C does both;
//         without -n the length of the first line decides
//
// Copyright (C) 2026 Steven Van Overberghe, Ghent University
// SPDX-License-Identifier: GPL-3.0-or-later
//
// This program is free software: you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option)
// any later version.  This program is distributed in the hope that it will be
// useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the file LICENSE
// or <https://www.gnu.org/licenses/>.

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <type_traits>
#include <vector>

using u8 = uint8_t;
using u64 = uint64_t;

#ifndef NMIN
#define NMIN 3
#endif
#ifndef NMAX
#define NMAX 32
#endif

// ---------------------------------------------------------------------------
// Shared input and output.  The reader hands out blocks of complete lines; the
// order in which the workers get them, and hence the order of the output, is
// arbitrary (as with permsnark's per-thread buffers).
struct Reader {
    static constexpr size_t CHUNK = size_t(1) << 22;
    std::mutex mu;
    std::string tail;               // incomplete last line of the previous block
    bool eof = false;
    bool next(std::string& buf) {
        std::lock_guard<std::mutex> lock(mu);
        if (eof && tail.empty()) return false;
        buf.assign(tail);
        tail.clear();
        while (!eof) {
            const size_t old = buf.size();
            buf.resize(old + CHUNK);
            const size_t got = fread(&buf[old], 1, CHUNK, stdin);
            buf.resize(old + got);
            if (got < CHUNK) {                               // short read: end of input (or an error)
                if (ferror(stdin)) { perror("permcanon: reading stdin"); exit(3); }
                eof = true; break;
            }
            const size_t nl = buf.find_last_of('\n');
            if (nl != std::string::npos) { tail.assign(buf, nl + 1, std::string::npos); buf.resize(nl + 1); break; }
        }
        return !buf.empty();
    }
};

struct Writer {
    std::mutex mu;
    void flush(std::string& buf) {
        if (buf.empty()) return;
        std::lock_guard<std::mutex> lock(mu);
        if (fwrite(buf.data(), 1, buf.size(), stdout) != buf.size()) { perror("permcanon: writing stdout"); exit(3); }
        buf.clear();
    }
};

// ---------------------------------------------------------------------------
// The test for one permutation.  N is the cycle length (order 2N).
template<int N>
struct Canon {
    static_assert(N >= 3 && N <= 63, "n must lie in [3, 63]");
    static constexpr int n = N;
    using VB = std::conditional_t<(2 * N <= 64), u64, unsigned __int128>;   // vertex bitset
    static constexpr VB ALLV = (2 * N == 64) ? ~VB(0) : ((VB(1) << (2 * N)) - 1);

    u8 p[N];                  // the permutation of the line
    u8 D[N];                  // its difference list
    VB adj[2 * N];            // adjacency bitsets of PG(p)
    VB cyc[2 * N];            // the two cycles alone (constant part of adj)
    bool rejected_ = false;   // a labelling smaller than D(p) has been found

    Canon() {
        for (int v = 0; v < 2 * n; ++v) cyc[v] = 0;
        for (int i = 0; i < n; ++i) {
            const int j = (i + 1) % n;
            cyc[i] |= VB(1) << j;             cyc[j] |= VB(1) << i;
            cyc[n + i] |= VB(1) << (n + j);   cyc[n + j] |= VB(1) << (n + i);
        }
    }

    // ---- small helpers -----------------------------------------------------
    static inline int wrap(int v) { return v >= n ? v - n : v; }
    static inline int wrapDown(int v) { return v < 0 ? v + n : v; }
    static inline int lowBit(VB w) {
        if constexpr (sizeof(VB) == 8) return __builtin_ctzll((u64)w);
        else { const u64 lo = (u64)w; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((u64)(w >> 64)); }
    }
    static inline int popVB(VB w) {
        if constexpr (sizeof(VB) == 8) return __builtin_popcountll((u64)w);
        else return __builtin_popcountll((u64)w) + __builtin_popcountll((u64)(w >> 64));
    }
    // The neighbour of cur inside cls other than prev (cur has exactly two in cls).
    inline int nextIn(VB cls, int cur, int prev) const {
        const VB nb = adj[cur] & cls;
        const int a = lowBit(nb);
        const int b = lowBit(nb & ~(VB(1) << a));
        return a == prev ? b : a;
    }
    // Does cls (n vertices) induce a single cycle?
    bool classIsCycle(VB cls) const {
        const int start = lowBit(cls);
        int prev = -1, cur = start, cnt = 0;
        do {
            if (popVB(adj[cur] & cls) != 2) return false;
            const int nxt = nextIn(cls, cur, prev);
            prev = cur; cur = nxt; ++cnt;
        } while (cur != start && cnt < n);
        return cur == start && cnt == n;
    }

    // ---- cyclic 5-edge-connectivity ----------------------------------------
    // No block: no interval [i, j] of 2 <= j-i+1 <= n-2 positions whose values
    // form one cyclic run.  runs(M) = popcount(M | rotl(M)) - popcount(M).
    bool isCyc5() const {
        if (n < 5) return false;                       // no cyclic 4-edge-cut to speak of
        constexpr u64 FULL = (n == 64) ? ~u64(0) : ((u64(1) << n) - 1);
        for (int i = 0; i + 1 < n; ++i) {
            u64 M = u64(1) << p[i];
            const int jmax = std::min(n - 1, i + n - 3);   // j - i + 1 <= n - 2
            for (int j = i + 1; j <= jmax; ++j) {
                M |= u64(1) << p[j];
                const u64 up = ((M << 1) | (M >> (n - 1))) & FULL;
                if (__builtin_popcountll(M | up) - (j - i + 1) == 1) return false;
            }
        }
        return true;
    }

    // ---- parsing -----------------------------------------------------------
    // "0 3 11 ..." -> p, with a check that it is a permutation of [n].
    bool parse(const char* s, const char* e) {
        u64 seen = 0;
        int cnt = 0;
        while (s < e) {
            while (s < e && (*s == ' ' || *s == '\t' || *s == '\r')) ++s;
            if (s == e) break;
            if (*s < '0' || *s > '9') return false;
            int v = 0;
            while (s < e && *s >= '0' && *s <= '9') { v = 10 * v + (*s++ - '0'); if (v > n) return false; }
            if (v >= n || cnt >= n || (seen >> v) & 1) return false;
            seen |= u64(1) << v;
            p[cnt++] = (u8)v;
        }
        return cnt == n;
    }

    // ---- the test ----------------------------------------------------------
    // Is some rotation of the eight lists of the labelling q smaller than D(p)?
    bool orbitSmaller(const u8* q) const {
        int Dq[N], Eq[N], qinv[N];
        for (int i = 0; i < n; ++i) qinv[q[i]] = i;
        for (int k = 0; k + 1 < n; ++k) Dq[k] = wrapDown(q[k + 1] - q[k]);
        Dq[n - 1] = wrapDown(q[0] - q[n - 1]);
        for (int j = 0; j < n; ++j) { const int j1 = wrap(j + 1); Eq[j] = wrapDown(qinv[j1] - qinv[j]); }
        for (int list = 0; list < 2; ++list) {
            const int* X = list ? Eq : Dq;
            for (int s = 0; s < n; ++s) for (int bwd = 0; bwd < 2; ++bwd) for (int neg = 0; neg < 2; ++neg) {
                int k = s;
                for (int i = 0; i < n; ++i) {
                    int v = X[k];
                    if (neg) v = n - v;
                    if (v != D[i]) { if (v < D[i]) return true; break; }
                    k = bwd ? (k == 0 ? n - 1 : k - 1) : (k == n - 1 ? 0 : k + 1);
                }
            }
        }
        return false;
    }
    // A permutation 2-factor with blue cycle 'blue': label the blue cycle from
    // vertex 0, the red cycle from the red neighbour of vertex 0, and compare.
    void use2Factor(VB blue) {
        const VB red = ALLV & ~blue;
        int bl[N], rlab[2 * N];
        u8 q[N];
        int prev = -1, cur = 0;
        for (int i = 0; i < n; ++i) { bl[i] = cur; const int nxt = nextIn(blue, cur, prev); prev = cur; cur = nxt; }
        cur = lowBit(adj[bl[0]] & red); prev = -1;
        for (int i = 0; i < n; ++i) { rlab[cur] = i; const int nxt = nextIn(red, cur, prev); prev = cur; cur = nxt; }
        for (int i = 0; i < n; ++i) q[i] = (u8)rlab[lowBit(adj[bl[i]] & red)];
        if (orbitSmaller(q)) rejected_ = true;
    }
    // Extend the blue path (startV ... end) by one vertex.  forb: vertices that
    // cannot be blue; crossed: red vertices that already have a blue neighbour.
    void grow(VB path, int end, int startV, int len, VB forb, VB crossed) {
        const VB endFree = adj[end] & ~path;                    // the undecided neighbours of end
        VB cand = endFree & ~forb;
        while (cand) {
            const int w = lowBit(cand); cand &= cand - 1;
            const VB wb = VB(1) << w;
            const VB nbInPath = adj[w] & path;
            if (len + 1 < n) {
                if (nbInPath != (VB(1) << end)) continue;         // chord
                const VB t = endFree & ~wb;                       // end is left: its other neighbour is red
                if (t & crossed) continue;                        // that vertex would have two blue neighbours
                VB nforb = forb | t;
                if (t) {                                          // a red vertex with a blue neighbour has two red ones
                    const VB tn = adj[lowBit(t)] & ~path;
                    if (tn & wb) continue;                        // w itself would have to be red
                    nforb |= tn;
                }
                // enough undecided vertices for the rest of the blue cycle, at most n red ones
                if (popVB(ALLV & ~(path | wb) & ~nforb) < n - len - 1 || popVB(nforb) > n) continue;
                grow(path | wb, w, startV, len + 1, nforb, crossed | t);
                if (rejected_) return;
            } else if (nbInPath == ((VB(1) << end) | (VB(1) << startV))) {
                const VB blue = path | wb;
                if (classIsCycle(ALLV & ~blue)) { use2Factor(blue); if (rejected_) return; }
            }
        }
    }
    // All permutation 2-factors, each exactly once: vertex 0 lies on one of the
    // two cycles and has exactly one red neighbour r there; the three choices of
    // r fix the two blue neighbours of 0 and force r's other neighbours red.
    void allTwoFactors() {
        VB opts = adj[0];
        while (opts) {
            const int r = lowBit(opts); opts &= opts - 1;
            const VB rest = adj[0] & ~(VB(1) << r);
            const int a = lowBit(rest), b = lowBit(rest & (rest - 1));
            const VB path = VB(1) | (VB(1) << a) | (VB(1) << b);
            if (n == 3) {                                         // the blue cycle is closed already
                if ((adj[a] >> b) & 1 && classIsCycle(ALLV & ~path)) use2Factor(path);
            } else if (!((adj[a] >> b) & 1)) {                    // a - b would be a chord
                const VB tn = adj[r] & ~VB(1);                    // r is red and 0 is blue:
                if (!(tn & path)) grow(path, b, a, 3, (VB(1) << r) | tn, VB(1) << r);
            }
            if (rejected_) return;
        }
    }
    // Is the parsed permutation strongly canonical?
    bool isCanonical() {
        if (p[0] != 0) return false;           // one labelling per orbit: p(0) = 0
        for (int i = 0; i + 1 < n; ++i) D[i] = (u8)wrapDown(p[i + 1] - p[i]);
        D[n - 1] = (u8)wrapDown(p[0] - p[n - 1]);
        for (int v = 0; v < 2 * n; ++v) adj[v] = cyc[v];
        for (int i = 0; i < n; ++i) { adj[i] |= VB(1) << (N + p[i]); adj[N + p[i]] |= VB(1) << i; }
        rejected_ = false;
        allTwoFactors();
        return !rejected_;
    }
};

// ---------------------------------------------------------------------------
// Workers.
struct Options {
    int n = 0, threads = 1;
    bool canon = false;        // -Y: keep only the strongly canonical words
    bool cyc5 = false;         // -C: keep only the cyclically 5-edge-connected ones
};

struct Totals {
    std::mutex mu;
    u64 read = 0, kept = 0;
    void add(u64 r, u64 k) { std::lock_guard<std::mutex> lock(mu); read += r; kept += k; }
};

template<int N>
void worker(const Options& opt, Reader& rd, Writer& wr, Totals& tot) {
    Canon<N> c;
    std::string buf, out;
    u64 nread = 0, nkept = 0;
    while (rd.next(buf)) {
        const char* s = buf.data();
        const char* const e = s + buf.size();
        while (s < e) {
            const char* le = (const char*)memchr(s, '\n', (size_t)(e - s));
            const char* const ls = s;
            s = le ? le + 1 : e;
            if (!le) le = e;
            if (le == ls) continue;                              // empty line
            if (!c.parse(ls, le)) {
                fprintf(stderr, "permcanon: not a permutation of [%d]: %.*s\n", N, (int)(le - ls), ls);
                exit(2);
            }
            ++nread;
            // The cheap test first: it throws away nearly everything.
            if (opt.cyc5 && !c.isCyc5()) continue;
            if (opt.canon && !c.isCanonical()) continue;
            ++nkept; out.append(ls, (size_t)(le - ls)); out += '\n';
        }
        if (out.size() > (size_t(1) << 20)) wr.flush(out);
    }
    wr.flush(out);
    tot.add(nread, nkept);
}

template<int N>
void dispatchN(const Options& opt, Reader& rd, Writer& wr, Totals& tot) {
    if (N == opt.n) {
        if (opt.threads == 1) { worker<N>(opt, rd, wr, tot); return; }
        std::vector<std::thread> th;
        for (int t = 0; t < opt.threads; ++t) th.emplace_back([&] { worker<N>(opt, rd, wr, tot); });
        for (auto& x : th) x.join();
        return;
    }
    if constexpr (N < NMAX) return dispatchN<N + 1>(opt, rd, wr, tot);
    fprintf(stderr, "permcanon: n = %d is not compiled in (NMIN = %d, NMAX = %d)\n", opt.n, NMIN, NMAX);
    exit(1);
}

static void usage() {
    fprintf(stderr,
        "usage: permcanon [-Y] [-C] [-n <n>] [-t <threads>] < in.perm > out.perm\n"
        "  reads permutation words (permsnark -o perm) from stdin and writes the\n"
        "  words that pass the selected tests to stdout\n"
        "  -Y            keep only the words canonical in the strong sense, i.e. one\n"
        "                per isomorphism class (the default if neither -Y nor -C)\n"
        "  -C            keep only the cyclically 5-edge-connected graphs (no block;\n"
        "                implies girth >= 5).  -Y -C applies both tests\n"
        "  -n <n>        length of the two cycles, %d <= n <= %d (default: from the first line)\n"
        "  -t <threads>  number of threads (default 1)\n", NMIN, NMAX);
    exit(1);
}

int main(int argc, char** argv) {
    Options opt;
    for (int i = 1; i < argc; ++i) {
        const std::string a = argv[i];
        auto next = [&]() -> const char* { if (i + 1 >= argc) usage(); return argv[++i]; };
        if (a == "-n") opt.n = atoi(next());
        else if (a == "-t") opt.threads = atoi(next());
        else if (a == "-Y") opt.canon = true;
        else if (a == "-C") opt.cyc5 = true;
        else usage();
    }
    if (!opt.canon && !opt.cyc5) opt.canon = true;            // -Y is the default
    int& n = opt.n;
    if (opt.threads < 1 || n < 0 || (n && (n < NMIN || n > NMAX))) usage();

    Reader rd;
    Writer wr;
    Totals tot;
    if (!n) {                                   // the number of words on the first line
        std::string first;
        if (!rd.next(first)) { fprintf(stderr, "permcanon: empty input\n"); return 0; }
        const size_t nl = first.find('\n');
        const std::string line = first.substr(0, nl == std::string::npos ? first.size() : nl);
        bool in = false;
        for (char ch : line) {
            if (ch >= '0' && ch <= '9') { if (!in) ++n; in = true; }
            else in = false;
        }
        if (n < NMIN || n > NMAX) {
            fprintf(stderr, "permcanon: cannot read n from the first line (got %d, compiled for %d..%d)\n", n, NMIN, NMAX);
            return 1;
        }
        rd.tail.insert(0, first);               // put the block back
    }

    const auto t0 = std::chrono::steady_clock::now();
    dispatchN<NMIN>(opt, rd, wr, tot);
    if (fflush(stdout) != 0) { perror("permcanon: writing stdout"); return 3; }
    const double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    const char* what = opt.canon ? (opt.cyc5 ? "cyclically 5-edge-connected, strongly canonical" : "strongly canonical")
                                 : "cyclically 5-edge-connected";
    fprintf(stderr, "n=%d order=%d: kept %llu of %llu permutation word%s (%s), %.3fs, %d thread%s\n",
            n, 2 * n, (unsigned long long)tot.kept, (unsigned long long)tot.read, tot.read == 1 ? "" : "s",
            what, secs, opt.threads, opt.threads == 1 ? "" : "s");
    return 0;
}
