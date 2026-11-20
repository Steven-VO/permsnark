// permsnark.cpp -- exhaustive generation of permutation graphs.  Version 4.0
//
// A permutation graph of order 2n is a cubic graph on the vertex set [2n] in
// which 0..n-1 and n..2n-1 induce chordless cycles (in that order) and the
// remaining n edges ("spokes") form a perfect matching.  Such a graph is PG(p)
// for a permutation p of [n]: vertex i is joined to n + p(i).
//
// The program is based on the orderly algorithm of
//   J. Goedgebeur, J. Renders and S. Van Overberghe, Generation of cycle
//   permutation graphs and permutation snarks, Mathematics of Computation
//   (2026), doi:10.1090/mcom/4247.
// By default it outputs one permutation from every orbit of the group Gamma
// (order 8n^2) of relabellings that preserve the two cycles (the *weak*
// variant): p is canonical iff p(0) = 0 and its difference list
// D(i) = p(i+1) - p(i) mod n is lexicographically minimal among the 8n
// rotations of D, -D, rev D, -rev D and of the same four lists for the inverse
// permutation.  The test is incremental (see "live rotations" below).
//
//   -S  only permutation snarks.  A cubic graph is 3-edge-colourable iff it
//       has an even 2-factor, and a 2-factor of a partial graph remains one in
//       every completion, so a node is pruned as soon as its graph has an even
//       2-factor (section "Snarks").
//   -H  only non-hamiltonian graphs, in the same way with "hamiltonian cycle"
//       instead of "even 2-factor".
//   -C  only cyclically 5-edge-connected graphs (section "Cyclic 5-edge-
//       connectivity").
//   -Y  one graph per isomorphism class (the *strong* variant): p is also
//       compared with the labellings along the other permutation 2-factors of
//       the graph (section "Strong canonicity").
//
// Build:  make permsnark_15   (compiled for the single value n = 15)
// Usage:  ./permsnark_15 [-g girth] [-S|-H] [-C] [-Y] [-t threads] [-r res -m mod]
//                        [-s level] [-o g6|perm]
//
// n, the girth mode, the snark and strong modes and the recursion level are
// template parameters; all per-node data lives in fixed-size arrays.
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
#define NMAX 16
#endif

// ---------------------------------------------------------------------------
// Runtime options and shared output.
struct Options {
    int n = 0;
    int girth = 3;          // generate graphs of girth >= girth
    int threads = 1;
    int res = 0, mod = 1;   // external splitting: residue class of the split counter
    int splitLevel = -1;    // recursion level at which the split is applied (-1: auto)
    int outMode = 0;        // 0: count only, 1: graph6, 2: permutation words
    bool snark = false;     // only permutation snarks (forces girth >= 5, n odd)
    bool nonham = false;    // only non-hamiltonian graphs (forces girth >= 5)
    bool cyc5 = false;      // only cyclically 5-edge-connected graphs (forces girth >= 5)
    bool strong = false;    // strong canonicity: one output per isomorphism class (-Y)
};

struct SharedOutput {
    std::mutex mu;
    void flush(std::string& buf) {
        std::lock_guard<std::mutex> lock(mu);
        fwrite(buf.data(), 1, buf.size(), stdout);
        buf.clear();
    }
};

// ---------------------------------------------------------------------------
// The generator.
//
//  N  : length of the two cycles (order 2N)
//  GM : girth mode.  0: no extra test (for girth <= 6 the bound
//       D(0) >= girth - 3 suffices).  7, 8: girth >= 7 / >= 8; the short
//       cycles through two spokes are excluded by position domains.  9: girth
//       >= 9 (runtime value); in addition a BFS in the current graph.
//  SNARK : prune every node whose graph has an even 2-factor (-S) or, with
//          nonham_ (-H), a hamiltonian cycle (see "Snarks").
//  STRONG: one output per isomorphism class instead of one per orbit of Gamma
//          (see "Strong canonicity").
template<int N, int GM, bool SNARK, bool STRONG>
struct Generator {
    static_assert(N >= 3 && N <= 63, "n must lie in [3, 63]");
    static constexpr int n = N;
    static constexpr u8 UNK = 0xFF;                        // "undefined" marker
    static constexpr u64 FULL = (1ULL << N) - 1;           // all values [n]
    static constexpr bool needGraph = (GM >= 9) || STRONG;   // adjacency bitsets needed
    using VB = std::conditional_t<(2 * N <= 64), u64, unsigned __int128>;  // vertex bitset

    // ---- live rotations ----------------------------------------------------
    // A rotation that agrees with D on every entry known so far is "live"; it
    // is compared further only when an entry it needs becomes known.
    //  * D-forward rotations all wait for the first unknown entry of D, so
    //    they bound the next difference from below (or above, if negated).
    //  * D-backward rotations are compared on their palindrome part and then
    //    wait for D(n-1) = n - p(n-1); this restricts the value that can be
    //    placed last (lastMask).
    //  * An E-rotation (on the inverse) has matched D[0..d-1] and next compares
    //    D[d] with (+-)E[e], e running forwards (flags & BWD == 0) or
    //    backwards.  It waits for E[e] (in the list of position e) or for D[d]
    //    (in waitD[L]).
    enum : u8 { BWD = 1, NEG = 2 };
    struct Match { u8 e, d, flags, pad; };
    struct MatchList { int cnt; Match m[4 * N]; };
    struct Node { u8 e, d, flags, pad; int16_t next, pad2; };   // waiting-list node
    static constexpr int POOL = 4 * N * N + 4 * N;
    // live D-forward rotations, packed as s | (neg << 7)
    struct IdList { int cnt; u8 v[N]; };
    enum { REJECT = -1, STALL_E = 0, STALL_D = 1, DROP = 2 };

    // ---- search state ------------------------------------------------------
    // In snark mode p and pinv are stored twice (p[q + n] = p[q]) so that the
    // 2-factor trace can index them with unwrapped positions and values.
    static constexpr int PLEN = SNARK ? 2 * N : N;
    u8 p[PLEN];         // p[0..L-1] known at level L
    u8 pinv[PLEN];      // inverse permutation, UNK for unused values
    inline void putP(int q, int x)    { p[q] = (u8)x;    if constexpr (SNARK) p[q + N] = (u8)x; }
    inline void putPinv(int v, int q) { pinv[v] = (u8)q; if constexpr (SNARK) pinv[v + N] = (u8)q; }
    u8 D[N];            // difference list of p, D[i] = p[i+1] - p[i] mod n
    u64 freeVals;       // bit v set iff value v is still unused
    int D0, nD0;        // D[0] and n - D[0]
    IdList id[N];       // id[L]: live D-forward rotations once D[0..L-1] are known
    MatchList waitD[N]; // waitD[L]: E-rotations waiting for D[L] (E[e] known)
    Node pool[POOL];    // nodes of the waiting lists, allocated like a stack
    int poolTop;
    int16_t headE[N];   // headE[j]: list of E-rotations waiting for E[j], -1 if empty
    u64 waitMask;       // bit j set iff headE[j] >= 0
    u8 rev[2 * N];      // live D-backward rotations (stack, packed like IdList)
    int revCnt;
    u64 lastMask[N];    // lastMask[L]: values that may still be placed at position n-1
    u64 rangeBase_;     // bits [D0, n-D0]: admissible differences (rotate by p[L-1] for values)
    u64 dSpecialBase_;  // bits D0 and n-D0
    // Girth >= 7 only: posDom[v] = positions where the free value v can still
    // be placed without violating D, E in [D0, n-D0] or closing a cycle of
    // length < girth through two spokes.  Each of these conditions says that
    // the value w +- b may not lie within circular distance r(b) of the
    // position of w, with r(1) = D0-1 (E-range), r(b) = 1 for b < D0 (D-range)
    // and r(b) = girth-3-b (a cycle through two spokes with arcs a, b has
    // length a+b+2).  The old masks go on a trail.
    static constexpr bool useDom = (GM >= 7);
    u64 posDom[N];
    u64 arcBase_[N];                // arcBase_[r]: positions within circular distance <= r of 0
    u64 domTrail[N][2 * N];
    u8 domTrailV[N][2 * N];
    int domTrailCnt[N];
    VB adj[2 * N];      // adjacency bitsets, only maintained if needGraph

    // ---- parameters and results --------------------------------------------
    int girth_ = 3;
    bool nonham_ = false;          // SNARK: prune hamiltonian cycles (-H) instead of even 2-factors (-S)
    bool cyc5_ = false;            // prune blocks (cyclic 4-edge-cuts), see blockForbid()
    int res_ = 0, mod_ = 1, splitLevel_ = -1;
    u64 splitCounter_ = 0;
    int outMode_ = 0;
    std::string outBuf_;
    SharedOutput* out_ = nullptr;
    std::vector<u8> g6Template_;   // graph6 body containing the cycle edges only

    u64 count = 0;                 // number of canonical permutations found

    // =======================================================================
    // Small helpers
    // =======================================================================
    static inline int circ(int v) {            // circular distance of a value in [n]
        return v <= n - v ? v : n - v;
    }
    static inline u64 bit(int v) { return 1ULL << v; }
    static inline int wrap(int v) { return v >= n ? v - n : v; }        // v in [0, 2n)
    static inline int wrapDown(int v) { return v < 0 ? v + n : v; }     // v in [-n, n)
    static inline u64 neighbourBits(int v) { return bit(wrap(v + 1)) | bit(wrapDown(v - 1)); }
    static inline u64 rotl1(u64 m) { return ((m << 1) | (m >> (n - 1))) & FULL; }
    static inline u64 rotl(u64 m, int r) { return ((m << r) | (m >> (n - r))) & FULL; }   // 0 <= r < n

    // Value x has been placed at position q: shrink the domains of x +- b.
    inline void placeDom(int q, int x) {
        const int G = (GM == 9) ? girth_ : GM;
        int cnt = 0;
        u64* tr = domTrail[q]; u8* tv = domTrailV[q];
        for (int b = 1; b < D0; ++b) {                         // D0 >= G-3
            const int r = (b == 1) ? D0 - 1 : std::max(G - 3 - b, 1);
            const u64 arc = rotl(arcBase_[r], q);
            const int w1 = wrap(x + b), w2 = wrapDown(x - b);
            tv[cnt] = (u8)w1; tr[cnt++] = posDom[w1]; posDom[w1] &= ~arc;
            tv[cnt] = (u8)w2; tr[cnt++] = posDom[w2]; posDom[w2] &= ~arc;
        }
        domTrailCnt[q] = cnt;
    }
    inline void undoDom(int q) {
        for (int k = domTrailCnt[q] - 1; k >= 0; --k) posDom[domTrailV[q][k]] = domTrail[q][k];
    }
    // After placing p[L]: does every remaining value still have a position in
    // L+1..n-1, can some value be placed last (lm = lastMask[L]), and -- for the
    // two values left at level N-3 -- are they far enough apart to be adjacent?
    template<int L>
    inline bool domainsOK(u64 freeAfter, u64 lm) const {
        const u64 rem = FULL & ~((2ULL << L) - 1);
        u64 anyLast = 0, fv = freeAfter;
        while (fv) {
            const int v = __builtin_ctzll(fv);
            fv &= fv - 1;
            const u64 dom = posDom[v] & rem;
            if (!dom) return false;
            anyLast |= (dom >> (n - 1)) & (lm >> v);
        }
        if (!(anyLast & 1)) return false;
        if constexpr (L == N - 3) {
            const int a = __builtin_ctzll(freeAfter), b = __builtin_ctzll(freeAfter & (freeAfter - 1));
            if (circ(b - a) < D0) return false;
        }
        return true;
    }

    // Bitset of the values (base + d) mod n for d in [lo, hi].
    static inline u64 rangeMask(int lo, int hi, int base) {
        u64 m = ((1ULL << (hi - lo + 1)) - 1) << lo;              // hi <= n-1 <= 62
        m = (m << base) | (m >> (n - base));                      // rotate within n bits
        return m & FULL;
    }

    // E[j] = pinv[j+1] - pinv[j] mod n, or -1 if one of them is still unknown.
    // The inverse difference list is never stored: it is read off pinv.
    inline int Eval(int j) const {
        const u8 a = pinv[j], b = pinv[j == n - 1 ? 0 : j + 1];
        if ((a | b) & 0x80) return -1;
        const int v = b - a;
        return v < 0 ? v + n : v;
    }

    // Compare D[from..to) with the D-forward rotation starting at s (negated if
    // neg): entries D[(s+i) mod n].  Returns -1 if the rotation is smaller, +1 if
    // larger, 0 if equal on the whole range.
    template<bool neg>
    inline int cmpFwd(int s, int from, int to) const {
        int j = s + from; if (j >= n) j -= n;
        for (int i = from; i < to; ++i) {
            int v = D[j]; if constexpr (neg) v = n - v;
            if (v != D[i]) return v < D[i] ? -1 : 1;
            if (++j == n) j = 0;
        }
        return 0;
    }
    // Same for the D-backward rotation starting at s: entries D[(s-i) mod n].
    template<bool neg>
    inline int cmpBwd(int s, int from, int to) const {
        int j = s - from; if (j < 0) j += n;
        for (int i = from; i < to; ++i) {
            int v = D[j]; if constexpr (neg) v = n - v;
            if (v != D[i]) return v < D[i] ? -1 : 1;
            if (--j < 0) j = n - 1;
        }
        return 0;
    }

    // Advance a live E-rotation as far as D (known up to knownD entries) and the
    // inverse differences allow.
    inline int advance(Match& m, int knownD) const {
        while (m.d < knownD) {
            int ev = Eval(m.e);
            if (ev < 0) return STALL_E;
            if (m.flags & NEG) ev = n - ev;
            if (ev != D[m.d]) return ev < D[m.d] ? REJECT : DROP;
            ++m.d;
            if (m.flags & BWD) m.e = (m.e == 0) ? n - 1 : m.e - 1;
            else               m.e = (m.e == n - 1) ? 0 : m.e + 1;
        }
        return m.d == n ? DROP : STALL_D;   // a complete match is an automorphism
    }
    // Put a rotation where it belongs after advancing.  false: reject.
    inline bool settle(const Match& m, int r, MatchList* lv) {
        if (r == REJECT) return false;
        if (r == STALL_E) {
            Node& nd = pool[poolTop];
            nd.e = m.e; nd.d = m.d; nd.flags = m.flags;
            nd.next = headE[m.e];
            headE[m.e] = (int16_t)poolTop++;
            waitMask |= bit(m.e);
        } else if (r == STALL_D) {
            lv->m[lv->cnt++] = m;
        }
        return true;
    }
    // E[j] has just become known: advance every rotation waiting for it.  The
    // list itself is left untouched (nothing reads it while E[j] is known, and
    // it is valid again after backtracking); new stalls allocate new nodes.
    inline bool wake(int j, int knownD, MatchList* lv) {
        for (int k = headE[j]; k >= 0; k = pool[k].next) {
            Match m{pool[k].e, pool[k].d, pool[k].flags, 0};
            if (!settle(m, advance(m, knownD), lv)) return false;
        }
        return true;
    }
    inline void undoPool(int mark) {
        while (poolTop > mark) {
            --poolTop;
            const int e = pool[poolTop].e;
            headE[e] = pool[poolTop].next;
            if (headE[e] < 0) waitMask &= ~bit(e);
        }
    }

    // E[j] has just become known with value ev in {D0, n-D0}: the forward and
    // backward rotations starting at j pass their first comparison; advance them.
    bool startE(int j, int ev, int knownD, MatchList* lv) {
        const u8 fl = (ev == D0) ? 0 : NEG;
        Match f{(u8)(j == n - 1 ? 0 : j + 1), 1, fl, 0};
        if (!settle(f, advance(f, knownD), lv)) return false;
        Match b{(u8)(j == 0 ? n - 1 : j - 1), 1, (u8)(fl | BWD), 0};
        return settle(b, advance(b, knownD), lv);
    }

    // New D-forward / D-backward rotation starting at s, all entries known.
    inline bool newFwd(int s) const {
        const int v = D[s];
        if (v == D0)  return cmpFwd<false>(s, 1, n) >= 0;
        if (v == nD0) return cmpFwd<true>(s, 1, n) >= 0;
        return true;
    }
    inline bool newBwd(int s) const {
        const int v = D[s];
        if (v == D0)  return cmpBwd<false>(s, 1, n) >= 0;
        if (v == nD0) return cmpBwd<true>(s, 1, n) >= 0;
        return true;
    }

    // =======================================================================
    // Girth
    // =======================================================================
    // Girth mode 7/8: all cycles of length < girth through two spokes are
    // excluded by the position domains (posDom); no per-candidate test needed.
    // Girth mode 9: bitset of the values x with dist(L, n+x) <= girth-2 in the
    // current graph (before the spoke at L is added).
    static inline int lowBit(VB w) {
        if constexpr (sizeof(VB) == 8) return __builtin_ctzll((u64)w);
        else { const u64 lo = (u64)w; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((u64)(w >> 64)); }
    }
    inline u64 badValues(int L) const {
        VB ball = VB(1) << L, frontier = ball;
        for (int step = 1; step <= girth_ - 2; ++step) {
            VB nxt = 0;
            while (frontier) {
                const int v = lowBit(frontier);
                frontier &= frontier - 1;
                nxt |= adj[v];
            }
            nxt &= ~ball;
            if (!nxt) break;
            ball |= nxt;
            frontier = nxt;
        }
        return (u64)(ball >> N) & FULL;
    }
    inline void addSpoke(int i, int x) { adj[i] |= VB(1) << (N + x); adj[N + x] |= VB(1) << i; }
    inline void delSpoke(int i, int x) { adj[i] &= ~(VB(1) << (N + x)); adj[N + x] &= ~(VB(1) << i); }

    // =======================================================================
    // Snarks: even 2-factors.  Non-hamiltonian graphs: hamiltonian cycles.
    // =======================================================================
    // A node is pruned as soon as its graph has a "bad" 2-factor: an even one
    // (-S) or a hamiltonian cycle (-H, nonham_).  Only the test of a single
    // 2-factor differs (badTwoFactor, fourSpokesBad).
    //
    // Let F0 be the two standard cycles.  A 2-factor F' of (a subgraph of)
    // PG(p) is determined by the set S of spokes it contains: a vertex whose
    // spoke is in F' drops one of its two cycle edges, and the other end of that
    // edge must then have its spoke in F' as well.  So F0 (+) F' is a union of
    // vertex-disjoint *alternating cycles*: spoke, cycle edge, spoke, ...
    // Each alternating cycle determines its own dropped edges, so for even n
    // the 2-factors containing all spokes are found as well.
    //
    // Only spokes are added, so at level L only 2-factors through the new spoke
    // can be new.  Those with a single alternating cycle are found before p[L]
    // is chosen: the cycle contains the edge {L-1, L}, so it is grown from the
    // spoke at L-1 through placed spokes and closes at a value adjacent to a
    // free value y; y is forbidden at position L iff the resulting 2-factor is
    // bad.  Unions of two or more alternating cycles are only checked at the
    // leaf (exact test).
    //
    // dropPos has bit q iff the cycle edge {q, q+1} is dropped, dropVal
    // likewise for {v, v+1}; the endpoints of S are then dropPos | rotl1(dropPos)
    // and dropVal | rotl1(dropVal).
    static inline int distUp(u64 mm, int q)   { return __builtin_ctzll(mm >> (q + 1)) + 1; }
    static inline int distDown(u64 mm, int q) { return q + n - (63 - __builtin_clzll(mm & ((1ULL << (q + n)) - 1))); }
    // Next S-element from q (in [0, n)) in the direction given by down (1:
    // downwards) on the doubled mask mm (bits 0..2n-1): returns the distance and
    // stores the element, unwrapped in [0, 2n), in r.
    static inline int step(u64 mm, int q, int down, int& r) {
        const int du = distUp(mm, q), dd = distDown(mm, q);
        const int m = -down;                                 // all ones if downwards
        r = q + (du ^ ((du ^ (n - dd)) & m));                // q + du  or  q + n - dd
        return du ^ ((du ^ dd) & m);
    }
    // Is the 2-factor F' given by S bad, i.e. are all its cycles even (-S) or
    // is it a single cycle (-H)?  From an S-position q follow cycle 1 away from
    // q's matched neighbour to the next S-position r, take the spoke to p[r],
    // follow cycle 2 to the next S-value w, take the spoke to pinv[w], and so
    // on; every spoke is traversed exactly once.  F' is hamiltonian iff the
    // first traced cycle uses every spoke of S (S is nonempty, so every vertex
    // lies on a cycle through S).
    static_assert(N <= 32 || !SNARK, "the 2-factor trace uses doubled 64-bit masks (n <= 32)");
    __attribute__((noinline))
    bool badTwoFactor(u64 dropPos, u64 dropVal) const {
        const u64 posS = dropPos | rotl1(dropPos), valS = dropVal | rotl1(dropVal);
        const u64 pp = posS | (posS << n), vv = valS | (valS << n);
        u64 rem = pp;                                        // both copies are cleared
        while (rem) {
            const int q0 = __builtin_ctzll(rem);
            int q = q0, len = 0;
            do {
                int r, w;
                len += step(pp, q, (dropPos >> q) & 1, r);   // matched with q+1: leave downwards
                const u64 br = bit(r);
                rem &= ~(br | (br << n) | (br >> n));
                const int v = p[r];
                len += step(vv, v, (dropVal >> v) & 1, w);
                len += 2;
                q = pinv[w];
                rem &= ~(bit(q) | bit(q + n));
            } while (q != q0);
            if (nonham_) return rem == 0;                    // hamiltonian iff one cycle
            if (len & 1) return false;
        }
        return true;
    }

    // Grow the alternating cycle at value v (its spoke is in S, v still needs
    // its matched neighbour on cycle 2) through the placed positions 0..L-1;
    // a free value closes the cycle as p[L].  snCand_: the values of interest,
    // snForbid_: the result.
    u64 snCand_ = 0, snForbid_ = 0;
    template<int L>
    void growFwd(int v, u64 dropPos, u64 dropVal) {
        if (!(snCand_ & ~snForbid_)) return;                        // nothing left to forbid
        const u64 posS = dropPos | rotl1(dropPos), valS = dropVal | rotl1(dropVal);
        for (int dir = 0; dir < 2; ++dir) {
            const int v2 = dir ? wrapDown(v - 1) : wrap(v + 1);
            if ((valS >> v2) & 1) continue;
            const u64 dv = dropVal | bit(dir ? v2 : v);            // cycle edge {v, v2}
            const int q2 = pinv[v2];
            if (q2 == UNK) {                                        // closes with p[L] = v2
                if (((snCand_ & ~snForbid_) >> v2) & 1) {
                    bool bad;
                    if (__builtin_popcountll(dropPos) == 2) {       // four spokes: closed formula
                        bad = fourSpokesBad<L>(dropPos, dropVal, v, dir);
                    } else {
                        putP(L, v2); putPinv(v2, L);
                        bad = badTwoFactor(dropPos, dv);
                        putPinv(v2, UNK);
                    }
                    if (bad) snForbid_ |= bit(v2);
                }
                continue;
            }
            // the spoke (q2, v2) joins S; q2 is matched with q2 + 1 or q2 - 1
            if (q2 + 1 < L && !((posS >> (q2 + 1)) & 1)) growFwd<L>(p[q2 + 1], dropPos | bit(q2), dv);
            if (q2 >= 1 && !((posS >> (q2 - 1)) & 1))     growFwd<L>(p[q2 - 1], dropPos | bit(q2 - 1), dv);
        }
    }
    // An alternating cycle with four spokes, decided without a trace: the
    // spokes are (L, y), (L-1, v0), (q1, v1 = v0 + s1), (q2 = q1 + t, v), with
    // y = v + s2.  For t = -1, and for t = +1 with s1 = s2, F' is a
    // hamiltonian cycle (even).  For t = +1, s1 != s2 it has two cycles
    // (not hamiltonian); the one through the position arc [L .. q1] (length
    // q1 + n - L + 1) and the value arc that contains y (length g + 1,
    // g = (v - v0 - 2) mod n if s1 = +1, (v0 - v - 2) mod n if s1 = -1) is
    // even iff q1 - L + g + 1 is even.
    template<int L>
    inline bool fourSpokesBad(u64 dropPos, u64 dropVal, int v, int dir) const {
        const int v0 = p[L - 1];
        const bool s1up = (dropVal >> v0) & 1;                    // dropped edge {v0, v0+1}: v1 = v0 + 1
        const int q1 = pinv[s1up ? wrap(v0 + 1) : wrapDown(v0 - 1)];
        const int a = __builtin_ctzll(dropPos & ~bit(L - 1));   // lower position of the pair {q1, q2}
        const bool s2up = (dir == 0);                             // y = v + 1
        if (a != q1 || s1up == s2up) return true;                // t = -1, or s1 = s2: hamiltonian
        if (nonham_) return false;                                // two cycles
        const int g = wrapDown(wrapDown((s1up ? v - v0 : v0 - v) - 2));
        return ((q1 - L + g + 1) & 1) == 0;
    }
    // The values y in cand for which p[L] = y completes a bad 2-factor with a
    // single alternating cycle (it contains the cycle edge {L-1, L}).
    template<int L>
    u64 snarkForbid(u64 cand) {
        snCand_ = cand; snForbid_ = 0;
        growFwd<L>(p[L - 1], bit(L - 1), 0);
        return snForbid_;
    }

    // Grow the alternating cycle at value v; it closes when it reaches the value
    // start, whose spoke opened the cycle together with its matched position.
    // usable: spokes (by position) that may still join -- for a partial graph
    // the unplaced positions are simply not usable.  UNIONS: at every closed
    // cycle also try to add further disjoint cycles (exhaustive search).
    template<bool UNIONS>
    bool growLeaf(int v, int start, u64 usable, u64 dropPos, u64 dropVal) {
        for (int dir = 0; dir < 2; ++dir) {
            const int v2 = dir ? wrapDown(v - 1) : wrap(v + 1);
            const u64 dv = dropVal | bit(dir ? v2 : v);
            if (v2 == start) {
                if (badTwoFactor(dropPos, dv)) return true;
                if constexpr (UNIONS) { if (unions(usable, dropPos, dv)) return true; }
                continue;
            }
            const int q2 = pinv[v2];
            if (q2 == UNK || !((usable >> q2) & 1)) continue; // unplaced, decided out, or in S
            const u64 us = usable & ~bit(q2);
            const int qa = wrap(q2 + 1), qb = wrapDown(q2 - 1);
            if (((us >> qa) & 1) && growLeaf<UNIONS>(p[qa], start, us & ~bit(qa), dropPos | bit(q2), dv)) return true;
            if (((us >> qb) & 1) && growLeaf<UNIONS>(p[qb], start, us & ~bit(qb), dropPos | bit(qb), dv)) return true;
        }
        return false;
    }
    // Exhaustive: every union of disjoint alternating cycles among the undecided
    // spokes (lowest position first: in S with its cycle, or out) is tested as a
    // 2-factor when its last cycle closes.  Returns true if a bad one exists.
    bool unions(u64 undecided, u64 dropPos, u64 dropVal) {
        while (undecided) {
            const int q = __builtin_ctzll(undecided);
            undecided &= ~bit(q);
            const int qa = wrap(q + 1), qb = wrapDown(q - 1);
            if (((undecided >> qa) & 1) && growLeaf<true>(p[qa], p[q], undecided & ~bit(qa), dropPos | bit(q), dropVal)) return true;
            if (((undecided >> qb) & 1) && growLeaf<true>(p[qb], p[q], undecided & ~bit(qb), dropPos | bit(qb), dropVal)) return true;
            // spoke q not in S: continue with the next undecided spoke
        }
        return false;
    }
    // Exact test at the leaf (p complete): does PG(p) have a bad 2-factor (an
    // even one / a hamiltonian cycle)?  The single alternating cycles through
    // the last spoke come first (these are the only single cycles the forward
    // DFS has not seen), then all unions.
    bool leafHasBadTwoFactor() {
        const int x = p[n - 1];
        const u64 rest = FULL & ~bit(n - 1);
        return growLeaf<false>(p[n - 2], x, rest & ~bit(n - 2), bit(n - 2), 0) ||
               growLeaf<false>(p[0], x, rest & ~bit(0), bit(n - 1), 0) ||
               unions(FULL, 0, 0);
    }

    // =======================================================================
    // Cyclic 5-edge-connectivity
    // =======================================================================
    // A cyclic 4-edge-cut of PG(p) (n >= 5) is exactly a *block*: a cyclic
    // interval A of 2..n-2 consecutive positions whose values p(A) form a cyclic
    // interval too (both sides of a 4-edge-cut meet each standard cycle in one
    // arc, and no spoke crosses; smaller cyclic cuts do not exist).  Blocks
    // come in complementary pairs, one of which does not contain both n-1 and
    // 0, so it suffices to test, when p[L] is chosen, the intervals [i, L] --
    // the leaf needs no test.  Before the choice: x would complete the block
    // [i, L] iff the value set M of [i, L-1] is one cyclic run (x adjacent to
    // it) or has exactly one gap of size one (x fills it).
    template<int L>
    u64 blockForbid() const {
        u64 forbid = 0, M = 0;
        for (int i = L - 1; i >= 0 && L - i + 1 <= n - 2; --i) {
            M |= bit(p[i]);
            const u64 up = rotl1(M), down = ((M >> 1) | (M << (n - 1))) & FULL;
            const int runs = __builtin_popcountll(M | up) - (L - i);
            if (runs == 1)      forbid |= (up & ~M) | (down & ~M);   // the two neighbours of the run
            else if (runs == 2) forbid |= up & down & ~M;            // the gap of size one, if any
        }
        return forbid;
    }

    // =======================================================================
    // Strong canonicity
    // =======================================================================
    // p is canonical iff D(p) is minimal among the 8n rotations of the eight
    // lists of every labelling along every permutation 2-factor of PG(p); the
    // standard 2-factor is the weak test above.  As in the paper, a labelling
    // that is smaller on the entries both lists know extends to a smaller
    // complete labelling, so the test can be applied to partial permutations.
    //
    // The other permutation 2-factors are kept on a stack along the recursion;
    // a new one must contain the new spoke (L, x).  It is found by growing the
    // *blue* cycle (the one through position L) as a chordless path from the
    // forced part 0, n-1, ..., L+1, L, n+x.  Free values and their neighbours
    // are red; a path vertex has its third neighbour red; a red vertex has at
    // most one blue neighbour; positions L-1, L-2 and the value p(L-1) are red.
    // At closure the red complement must induce one cycle.  A stored 2-factor
    // keeps the labels of its red cycle and its labelling q along the blue
    // cycle, which gets one more entry per level.
    struct TwoFactor { VB blue; u8 rlabV[N]; u8 q[N]; };   // rlabV[v]: label of value v on the red cycle
    static constexpr int TFMAX = 64;                       // max. number of stored 2-factors
    TwoFactor tf[STRONG ? TFMAX : 1];
    int tfCnt = 0;
    bool strong_ = false;
    static constexpr VB ALLV = (2 * N == 64) ? ~VB(0) : ((VB(1) << (2 * N)) - 1);
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
    // Extend the blue path (from startV to end) by one vertex.  forb: vertices
    // that cannot be blue; crossed: red vertices that already have a blue neighbour.
    void growBlue(VB path, int end, int startV, int len, VB forb, VB crossed, int L) {
        const VB endFree = adj[end] & ~path;                    // the 1 or 2 undecided neighbours of end
        VB cand = endFree & ~forb;
        while (cand) {
            const int w = lowBit(cand); cand &= cand - 1;
            const VB wb = VB(1) << w;
            const VB nbInPath = adj[w] & path;
            if (len + 1 < n) {
                if (nbInPath != (VB(1) << end)) continue;         // chord
                const VB t = endFree & ~wb;                       // end is left along the path: its other neighbour is red
                if (t & crossed) continue;                        // that vertex would have two blue neighbours
                VB nforb = forb | t;
                if (t) {                                          // a red vertex with a blue neighbour has two red ones
                    const VB tn = adj[lowBit(t)] & ~path;
                    if (tn & wb) continue;                        // w itself would have to be red
                    nforb |= tn;
                }
                // enough undecided vertices for the rest of the blue cycle, at most n red ones
                if (popVB(ALLV & ~(path | wb) & ~nforb) < n - len - 1 || popVB(nforb) > n) continue;
                growBlue(path | wb, w, startV, len + 1, nforb, crossed | t, L);
            } else if (nbInPath == ((VB(1) << end) | (VB(1) << startV))) {
                const VB blue = path | wb;
                if (classIsCycle(ALLV & ~blue)) addTwoFactor(blue, L);
            }
        }
    }
    // Start the growth by choosing the neighbour c of startV through which the
    // cycle will close; the other neighbour of startV is then red.
    void startBlue(VB path, int end, int startV, int len, VB forb, VB crossed, int L) {
        VB opts = adj[startV] & ~path & ~forb;
        while (opts) {
            const int c = lowBit(opts); opts &= opts - 1;
            const VB cb = VB(1) << c;
            const VB inPath = adj[c] & path;
            if (len + 1 == n) {                                                    // c closes the cycle at once
                if (inPath == ((VB(1) << startV) | (VB(1) << end)) && classIsCycle(ALLV & ~(path | cb))) addTwoFactor(path | cb, L);
                continue;
            }
            if (inPath != (VB(1) << startV)) continue;                             // chord
            const VB t = adj[startV] & ~path & ~cb;                               // the other neighbour: red
            if (t & crossed) continue;
            VB nforb = forb | t;
            if (t) { const VB tn = adj[lowBit(t)] & ~path; if (tn & cb) continue; nforb |= tn; }
            if (nforb & (VB(1) << end)) continue;
            growBlue(path | cb, end, c, len + 1, nforb, crossed | t, L);
        }
    }
    // Store the 2-factor with blue cycle 'blue' (found at level L): red labels
    // of the values and the labelling q[0..L] along it.
    void addTwoFactor(VB blue, int L) {
        if (tfCnt == TFMAX) { fprintf(stderr, "too many permutation 2-factors (TFMAX = %d)\n", TFMAX); exit(2); }
        TwoFactor& f = tf[tfCnt++];
        f.blue = blue;
        const VB red = ALLV & ~blue;
        int bl[N], rlab[2 * N];
        int prev, cur;
        if (L <= n - 2) { cur = 0; prev = n - 1; } else { cur = n - 1; prev = -1; }   // blue cycle from 0 away from n-1
        for (int i = 0; i <= L; ++i) { bl[i] = cur; const int nxt = nextIn(blue, cur, prev); prev = cur; cur = nxt; }
        cur = lowBit(adj[bl[0]] & red); prev = -1;                                     // red cycle from the red neighbour of bl[0]
        for (int i = 0; i < n; ++i) { rlab[cur] = i; const int nxt = nextIn(red, cur, prev); prev = cur; cur = nxt; }
        for (int v = 0; v < n; ++v) f.rlabV[v] = (u8)((red >> (N + v)) & 1 ? rlab[N + v] : 0);
        for (int i = 0; i <= L; ++i) f.q[i] = (u8)rlab[lowBit(adj[bl[i]] & red)];
    }
    // Is some rotation of the eight lists of q (defined on [0, L]) smaller than
    // D(p) on the entries both know?
    bool orbitSmaller(const u8* q, int L) const {
        int Dq[N], Eq[N], qinv[N];
        for (int k = 0; k < n; ++k) { Dq[k] = -1; Eq[k] = -1; qinv[k] = -1; }
        for (int i = 0; i <= L; ++i) qinv[q[i]] = i;
        for (int k = 0; k < L; ++k) Dq[k] = wrapDown(q[k + 1] - q[k]);
        if (L == n - 1) Dq[n - 1] = wrapDown(q[0] - q[n - 1]);
        for (int j = 0; j < n; ++j) { const int j1 = wrap(j + 1); if (qinv[j] >= 0 && qinv[j1] >= 0) Eq[j] = wrapDown(qinv[j1] - qinv[j]); }
        const int known = (L == n - 1) ? n : L;
        for (int list = 0; list < 2; ++list) {
            const int* X = list ? Eq : Dq;
            for (int s = 0; s < n; ++s) for (int bwd = 0; bwd < 2; ++bwd) for (int neg = 0; neg < 2; ++neg) {
                int k = s;
                for (int i = 0; i < known; ++i) {
                    int v = X[k];
                    if (v < 0) break;                                     // unknown: stalls
                    if (neg) v = n - v;
                    if (v != D[i]) { if (v < D[i]) return true; break; }
                    k = bwd ? (k == 0 ? n - 1 : k - 1) : (k == n - 1 ? 0 : k + 1);
                }
            }
        }
        return false;
    }
    // The strong test after placing (L, x): adjacency updated, freeMask = free values.
    template<int L>
    bool strongOK(int x, u64 freeMask) {
        // stored 2-factors: position L was a degree-2 blue vertex when they were
        // found, so its red neighbour is now the value x
        for (int k = 0; k < tfCnt; ++k) tf[k].q[L] = tf[k].rlabV[x];
        if constexpr (L <= N - 2) {
            // A new 2-factor needs x-1, x+1 placed, a red arc
            // of length >= 2 before L (hence L >= 3), and one of x-1, x+1 blue:
            // free values, their neighbours and p(L-1) are red.
            const int xm = wrapDown(x - 1), xp = wrap(x + 1);
            const u64 redVals = freeMask | rotl1(freeMask) | (((freeMask >> 1) | (freeMask << (n - 1))) & FULL) | bit(p[L - 1]);
            if (L >= 3 && pinv[xm] != UNK && pinv[xp] != UNK && ((redVals >> xm) & 1) + ((redVals >> xp) & 1) < 2) {
                VB path = VB(1) | (VB(1) << (N + x)), forb = 0;
                for (int q = L; q < n; ++q) path |= VB(1) << q;
                u64 rv = redVals;
                while (rv) { const int v = __builtin_ctzll(rv); rv &= rv - 1; forb |= VB(1) << (N + v); }
                forb |= (VB(1) << (L - 1)) | (VB(1) << (L - 2));
                startBlue(path, N + x, 0, n - L + 2, forb, VB(1) << (L - 1), L);
            }
        } else {
            startBlue((VB(1) << (N - 1)) | (VB(1) << (N + x)), N + x, N - 1, 2, 0, 0, L);
        }
        for (int k = 0; k < tfCnt; ++k)
            if (orbitSmaller(tf[k].q, L)) return false;
        return true;
    }

    // =======================================================================
    // Output
    // =======================================================================
    void prepareGraph6() {
        const int V = 2 * n;
        const int bits = V * (V - 1) / 2;
        g6Template_.assign((bits + 5) / 6, 0);
        auto set = [&](int i, int j) {          // i < j
            const int k = j * (j - 1) / 2 + i;
            g6Template_[k / 6] |= (u8)(1 << (5 - k % 6));
        };
        for (int i = 0; i + 1 < n; ++i) { set(i, i + 1); set(n + i, n + i + 1); }
        set(0, n - 1); set(n, 2 * n - 1);
    }
    void emit() {
        if (outMode_ == 1) {
            const int V = 2 * n;
            u8 body[(V * (V - 1) / 2 + 5) / 6 + 1];
            std::memcpy(body, g6Template_.data(), g6Template_.size());
            for (int i = 0; i < n; ++i) {
                const int j = n + p[i];
                const int k = j * (j - 1) / 2 + i;
                body[k / 6] |= (u8)(1 << (5 - k % 6));
            }
            if (V <= 62) outBuf_ += (char)(63 + V);
            else { outBuf_ += (char)126; outBuf_ += (char)(63 + (V >> 12)); outBuf_ += (char)(63 + ((V >> 6) & 63)); outBuf_ += (char)(63 + (V & 63)); }
            for (size_t k = 0; k < g6Template_.size(); ++k) outBuf_ += (char)(63 + body[k]);
            outBuf_ += '\n';
        } else {
            char tmp[8];
            for (int i = 0; i < n; ++i) { int l = snprintf(tmp, sizeof tmp, i ? " %d" : "%d", (int)p[i]); outBuf_.append(tmp, l); }
            outBuf_ += '\n';
        }
        if (outBuf_.size() > (1 << 20)) out_->flush(outBuf_);
    }

    // =======================================================================
    // The search
    // =======================================================================
    // rec<L>: choose p[L].  Known: p[0..L-1], D[0..L-2], id[L-1], waitD[L-1],
    // the waiting lists headE, lastMask[L-1], rev (all live D-backward
    // rotations, stalled at D[n-1]).  Levels N-2 and N-1 are handled together
    // by bottom2(), which is inlined into rec<N-3>.
    template<int L>
    void rec() {
        if constexpr (L == N - 2) {
            bottom2();
        } else if constexpr (L == N - 1) {
            leaf3();                                  // only reached for n = 3
        } else {
            if (L == splitLevel_) {
                if ((splitCounter_++ % (u64)mod_) != (u64)res_) return;
            }

            // Some free value has to be placed last; the live D-backward rotations
            // (stalled at D[n-1] = -p[n-1]) restrict which values qualify.
            if (!(freeVals & lastMask[L - 1])) return;

            // --- candidate values from the live D-forward rotations -----------
            // Each live rotation s is stalled at D[L-1] vs D[L-1-s]: it gives a
            // lower bound (plain) or an upper bound (negated) on D[L-1].  The new
            // rotation starting at L-1 gives D0 <= D[L-1] <= n - D0.
            const int base = p[L - 1];
            const IdList& idPrev = id[L - 1];
            u64 cand;
            if (idPrev.cnt == 0) {
                cand = freeVals & rotl(rangeBase_, base);
            } else {
                int lo = D0, hi = nD0;
                for (int k = 0; k < idPrev.cnt; ++k) {
                    const u8 v = idPrev.v[k];
                    const int val = D[L - 1 - (v & 0x7F)];
                    if (v & 0x80) hi = std::min(hi, n - val); else lo = std::max(lo, val);
                }
                if (lo > hi) return;
                cand = freeVals & rangeMask(lo, hi, base);
            }
            if constexpr (GM >= 9) cand &= ~badValues(L);

            if constexpr (useDom) {
                // --- forward checking: every free value needs a position, and
                // some free value must be admissible last.  The candidates for
                // position L are read off the domains (which contain the D- and
                // E-range conditions and all two-spoke short cycles).
                const u64 remPos = FULL & ~((1ULL << L) - 1);
                const u64 lm = lastMask[L - 1];
                u64 cd = 0, anyLast = 0, fv = freeVals;
                while (fv) {
                    const int v = __builtin_ctzll(fv);
                    fv &= fv - 1;
                    const u64 dom = posDom[v] & remPos;
                    if (!dom) return;
                    cd |= ((dom >> L) & 1) << v;
                    anyLast |= (dom >> (n - 1)) & (lm >> v);
                }
                if (!(anyLast & 1)) return;
                cand &= cd;
            } else {
                // --- E-range as a forbidden set: E[x-1] = L - pinv[x-1] and
                // E[x] = pinv[x+1] - L must lie in [D0, n-D0], i.e. x-1 and x+1 may
                // not sit at a position within circular distance < D0 of L.  (This
                // also excludes the cycles of length <= girth-1 through the new spoke
                // and the spoke at x-1 or x+1.)
                u64 F = 0;
                for (int q = std::max(0, L - D0 + 1); q < L; ++q) F |= neighbourBits(p[q]);
                for (int q = 0; q < L + D0 - n; ++q)               F |= neighbourBits(p[q]);
                cand &= ~F;
            }
            // --- cyclic 5-edge-connectivity: values that would complete a block --
            if (cyc5_) cand &= ~blockForbid<L>();
            // --- snarks: values that would complete an even 2-factor -----------
            if constexpr (SNARK) {
                if (cand) cand &= ~snarkForbid<L>(cand);
            }

            IdList& idCur = id[L];
            const MatchList& wdPrev = waitD[L - 1];
            MatchList& wdCur = waitD[L];
            // The D-backward rotation pushed at the previous level (s = L-2, if
            // any) is stalled at D[L-1] vs D[n-1]; D[L-1] is chosen now.
            const bool revTop = revCnt > 0 && (rev[revCnt - 1] & 0x7F) == L - 2;
            const bool revTopNeg = revTop && (rev[revCnt - 1] & 0x80);

            // --- values that need more than the state update ------------------
            // (i) D[L-1] in {D0, n-D0}: a new rotation starts at L-1;
            // (ii) E[x-1] or E[x] in {D0, n-D0}: a new E-rotation starts, which
            //      happens for x-1 = p[L-D0], x-1 = p[L-(n-D0)], x+1 = p[L+D0-n],
            //      x+1 = p[L-D0];
            // (iii) a rotation is waiting for E[x-1] or E[x];
            // (iv) if some rotation waits for D[L-1] all values are special.
            u64 special;
            if (idPrev.cnt | wdPrev.cnt) special = FULL;
            else {
                special = rotl(dSpecialBase_, base);
                if (L >= D0)      special |= neighbourBits(p[L - D0]);
                if (L >= nD0)     special |= bit(wrap(p[L - nD0] + 1));
                if (L + D0 >= n)  special |= bit(wrapDown(p[L + D0 - n] - 1));
                special |= waitMask | rotl1(waitMask);
            }

            while (cand) {
                const int x = __builtin_ctzll(cand);
                cand &= cand - 1;
                int d = x - base; if (d < 0) d += n;          // D[L-1], in [lo, hi]

                // --- admissible last values ---------------------------------------
                u64 lm = lastMask[L - 1];
                if (revTop) lm &= revTopNeg ? (FULL & ~((1ULL << d) - 1)) : ((2ULL << (n - d)) - 1);
                const u64 freeAfter = freeVals & ~bit(x);
                if (!(freeAfter & lm)) continue;
                lastMask[L] = lm;
                D[L - 1] = (u8)d;

                // --- forward checking (girth >= 7): shrink the domains now and
                //     give up before any bookkeeping if a value has no position
                if constexpr (useDom) {
                    placeDom(L, x);
                    if (!domainsOK<L>(freeAfter, lm)) { undoDom(L); continue; }
                }

                if (!((special >> x) & 1)) {
                    // --- fast path: no rotation is affected beyond the bookkeeping
                    idCur.cnt = 0;
                    wdCur.cnt = 0;
                    putP(L, x); putPinv(x, L); freeVals = freeAfter;
                    if constexpr (needGraph) addSpoke(L, x);
                    descend<L>();
                    if constexpr (needGraph) delSpoke(L, x);
                    freeVals |= bit(x); putPinv(x, UNK);
                    if constexpr (useDom) undoDom(L);
                    continue;
                }

                // --- D-forward rotations: keep the live ones that still match ---
                idCur.cnt = 0;
                for (int k = 0; k < idPrev.cnt; ++k) {
                    const u8 v = idPrev.v[k];
                    const int val = (v & 0x80) ? n - d : d;
                    if (val == D[L - 1 - (v & 0x7F)]) idCur.v[idCur.cnt++] = v;
                }
                // --- new rotations starting at L-1 (forward: live; backward: the
                //     palindrome part D[i] vs D[L-1-i] is decided now, the rest
                //     stalls at D[n-1]) ---------------------------------------
                bool pushedRev = false;
                bool ok = newDRotation<L>(d, idCur, pushedRev);
                const int poolMark = poolTop;
                putPinv(x, L);                      // makes E[x-1], E[x] readable
                if (ok) {
                    // --- E-rotations --------------------------------------------
                    const int xm = wrapDown(x - 1), xp = wrap(x + 1);
                    const u8 q1 = pinv[xm], q2 = pinv[xp];
                    const int e1 = (q1 != UNK) ? L - q1 : -1;        // E[x-1], in range by construction
                    const int e2 = (q2 != UNK) ? q2 + (n - L) : -1;  // E[x]
                    wdCur.cnt = 0;
                    ok = processE<L>(x, xm, e1, e2, wdPrev, wdCur);
                }
                if (ok) {
                    putP(L, x);
                    freeVals = freeAfter;
                    if constexpr (needGraph) addSpoke(L, x);
                    descend<L>();
                    if constexpr (needGraph) delSpoke(L, x);
                    freeVals |= bit(x);
                }
                undoPool(poolMark);
                putPinv(x, UNK);
                if (pushedRev) --revCnt;
                if constexpr (useDom) undoDom(L);
            }
        }
    }

    // Recurse from level L: the last two levels are inlined into rec<N-3>.
    template<int L>
    inline void descend() {
        if constexpr (STRONG) {
            const int mark = tfCnt;
            if (!strongOK<L>(p[L], freeVals)) { tfCnt = mark; return; }
            if constexpr (L + 1 == N - 2) bottom2(); else rec<L + 1>();
            tfCnt = mark;
            return;
        }
        if constexpr (L + 1 == N - 2) bottom2(); else rec<L + 1>();
    }

    // D[L-1] = d has just been chosen.  If d is D0 (or n-D0) the forward
    // rotation starting at L-1 becomes live and the backward one is compared on
    // its palindrome part D[i] vs D[L-1-i]; the rest of it stalls at D[n-1].
    // Returns false if the backward rotation is smaller.
    template<int L>
    inline bool newDRotation(int d, IdList& idCur, bool& pushedRev) {
        if (d == D0) {
            idCur.v[idCur.cnt++] = (u8)(L - 1);
            const int c = cmpBwd<false>(L - 1, 1, L / 2);
            if (c < 0) return false;
            if (c == 0) { rev[revCnt++] = (u8)(L - 1); pushedRev = true; }
        } else if (d == nD0) {
            idCur.v[idCur.cnt++] = (u8)((L - 1) | 0x80);
            const int c = cmpBwd<true>(L - 1, 1, (L - 1) / 2 + 1);
            if (c < 0) return false;
            if (c == 0) { rev[revCnt++] = (u8)((L - 1) | 0x80); pushedRev = true; }
        }
        return true;
    }

    // p[L] = x has just been placed (pinv[x] set).  Advance the E-rotations
    // waiting for D[L-1], for E[x-1] and for E[x], and start the ones at x-1 and
    // x if E[x-1] = e1 or E[x] = e2 equals D0 or n-D0 (e1/e2 < 0: unknown).
    template<int L>
    inline bool processE(int x, int xm, int e1, int e2, const MatchList& wdPrev, MatchList& wdCur) {
        for (int k = 0; k < wdPrev.cnt; ++k) {
            Match m = wdPrev.m[k];
            if (!settle(m, advance(m, L), &wdCur)) return false;
        }
        if (e1 >= 0 && headE[xm] >= 0 && !wake(xm, L, &wdCur)) return false;
        if (e2 >= 0 && headE[x] >= 0  && !wake(x, L, &wdCur))  return false;
        if ((e1 == D0 || e1 == nD0) && !startE(xm, e1, L, &wdCur)) return false;
        if ((e2 == D0 || e2 == nD0) && !startE(x, e2, L, &wdCur))  return false;
        return true;
    }

    // Levels N-2 and N-1 together: the two remaining values are placed at the
    // positions N-2 and N-1 in both orders.
    __attribute__((always_inline))
    void bottom2() {
        constexpr int L = N - 2;
        const u64 lm0 = lastMask[L - 1];
        if (!(freeVals & lm0)) return;
        const int base = p[L - 1];
        const IdList& idPrev = id[L - 1];
        int lo = D0, hi = nD0;
        for (int k = 0; k < idPrev.cnt; ++k) {
            const u8 v = idPrev.v[k];
            const int val = D[L - 1 - (v & 0x7F)];
            if (v & 0x80) hi = std::min(hi, n - val); else lo = std::max(lo, val);
        }
        if (lo > hi) return;
        const int a = __builtin_ctzll(freeVals);
        const int b = __builtin_ctzll(freeVals & ~bit(a));
        const bool revTop = revCnt > 0 && (rev[revCnt - 1] & 0x7F) == L - 2;
        const bool revTopNeg = revTop && (rev[revCnt - 1] & 0x80);
        u64 badY = 0;
        if constexpr (GM >= 9) badY = badValues(L);
        if (cyc5_) badY |= blockForbid<L>();
        if constexpr (SNARK) badY |= snarkForbid<L>(freeVals);
        IdList& idCur = id[L];
        const MatchList& wdPrev = waitD[L - 1];
        MatchList& wdCur = waitD[L];

        for (int t = 0; t < 2; ++t) {
            const int y = t ? b : a, x = t ? a : b;             // y at N-2, x at N-1
            int d = y - base; if (d < 0) d += n;                // D[N-3]
            if (d < lo || d > hi) continue;
            if ((badY >> y) & 1) continue;
            u64 lm = lm0;
            if (revTop) lm &= revTopNeg ? (FULL & ~((1ULL << d) - 1)) : ((2ULL << (n - d)) - 1);
            if (!((lm >> x) & 1)) continue;
            int d1 = x - y; if (d1 < 0) d1 += n;                // D[N-2]
            if (d1 < D0 || d1 > nD0) continue;
            const int d2 = n - x;                               // D[N-1], in range by lm
            const int ym = wrapDown(y - 1), yp = wrap(y + 1);
            const u8 q1 = pinv[ym], q2 = pinv[yp];
            const int e1 = (q1 != UNK) ? L - q1 : -1;           // E[y-1]
            const int e2 = (q2 != UNK) ? q2 + (n - L) : -1;     // E[y]
            const int xm = wrapDown(x - 1), xp = wrap(x + 1);
            const int f1 = (N - 1) - (xm == y ? L : (int)pinv[xm]);   // E[x-1]
            const int f2 = (xp == y ? L : (int)pinv[xp]) + 1;         // E[x]
            if constexpr (useDom) {
                // The domains hold every constraint from the placed values; the
                // only one missing is between y and x themselves (d1, above).
                if (!((posDom[y] >> L) & 1) || !((posDom[x] >> (N - 1)) & 1)) continue;
            } else {
                // E-range of the spoke at N-2 (x is the only other unplaced value)
                // and of the spoke at N-1 (all its neighbours are placed, y at L).
                if (e1 >= 0 && (e1 < D0 || e1 > nD0)) continue;
                if (e2 >= 0 && (e2 < D0 || e2 > nD0)) continue;
                if (f1 < D0 || f1 > nD0 || f2 < D0 || f2 > nD0) continue;
            }

            // --- bookkeeping of level N-2 ----------------------------------------
            D[L - 1] = (u8)d;
            idCur.cnt = 0;
            for (int k = 0; k < idPrev.cnt; ++k) {
                const u8 v = idPrev.v[k];
                const int val = (v & 0x80) ? n - d : d;
                if (val == D[L - 1 - (v & 0x7F)]) idCur.v[idCur.cnt++] = v;
            }
            bool pushedRev = false;
            if (!newDRotation<L>(d, idCur, pushedRev)) continue;
            putPinv(y, L);
            putP(L, y);
            const int poolMark = poolTop;
            wdCur.cnt = 0;
            bool ok = processE<L>(y, ym, e1, e2, wdPrev, wdCur);
            int tfMark = 0;
            bool spokeAdded = false;
            if constexpr (STRONG) {
                tfMark = tfCnt;
                if (ok) { addSpoke(L, y); spokeAdded = true; if (!strongOK<L>(y, bit(x))) ok = false; }
            }

            // --- the leaf --------------------------------------------------------
            if (ok) {
                if constexpr (GM >= 9) { if (!spokeAdded) { addSpoke(L, y); spokeAdded = true; } if ((badValues(N - 1) >> x) & 1) ok = false; }
                if (ok) {
                    D[L] = (u8)d1;
                    D[L + 1] = (u8)d2;
                    putPinv(x, N - 1);
                    putP(N - 1, x);
                    if (finalChecks(x, xm, d1, d2, f1, f2)) {
                        bool accept = true;
                        if constexpr (SNARK) accept = !leafHasBadTwoFactor();    // exact test
                        if constexpr (STRONG) {
                            if (accept) {
                                const int mark2 = tfCnt;
                                addSpoke(N - 1, x);
                                accept = strongOK<N - 1>(x, 0);
                                delSpoke(N - 1, x);
                                tfCnt = mark2;
                            }
                        }
                        if (accept) { ++count; if (outMode_) emit(); }
                    }
                    putPinv(x, UNK);
                }
            }
            if constexpr (needGraph) { if (spokeAdded) delSpoke(L, y); }
            if constexpr (STRONG) tfCnt = tfMark;
            undoPool(poolMark);
            putPinv(y, UNK);
            if (pushedRev) --revCnt;
        }
    }

    // Complete the comparison of every live rotation once p is complete;
    // E-rotations only wait at E[x-1], E[x] (the only entries that were
    // unknown) or for D[N-2].  D[N-1] = d2 >= D[1] is guaranteed by lastMask.
    __attribute__((always_inline))
    bool finalChecks(int x, int xm, int d1, int d2, int e1, int e2) const {
        // D-backward: the reflection (s = 0) continues if D[1] == D[n-1].
        if (d2 == D[1] && cmpBwd<false>(0, 2, n) < 0) return false;
        for (int k = 1; k < revCnt; ++k) {
            const u8 v = rev[k]; const int s = v & 0x7F;
            const int c = (v & 0x80) ? cmpBwd<true>(s, s + 1, n) : cmpBwd<false>(s, s + 1, n);
            if (c < 0) return false;
        }
        // New D-rotations at N-2 and N-1 (forward and backward).
        if (d1 == D0)       { if (cmpFwd<false>(N - 2, 1, n) < 0 || cmpBwd<false>(N - 2, 1, n) < 0) return false; }
        else if (d1 == nD0) { if (cmpFwd<true>(N - 2, 1, n) < 0  || cmpBwd<true>(N - 2, 1, n) < 0)  return false; }
        if (d2 == D0)       { if (cmpFwd<false>(N - 1, 1, n) < 0 || cmpBwd<false>(N - 1, 1, n) < 0) return false; }
        else if (d2 == nD0) { if (cmpFwd<true>(N - 1, 1, n) < 0  || cmpBwd<true>(N - 1, 1, n) < 0)  return false; }
        // D-forward: live rotations (stalled at D[N-2]).
        const IdList& idp = id[N - 2];
        for (int k = 0; k < idp.cnt; ++k) {
            const u8 v = idp.v[k]; const int s = v & 0x7F;
            const int c = (v & 0x80) ? cmpFwd<true>(s, N - 2 - s, n) : cmpFwd<false>(s, N - 2 - s, n);
            if (c < 0) return false;
        }
        // E-rotations.
        const MatchList& wd = waitD[N - 2];
        for (int k = 0; k < wd.cnt; ++k) { Match m = wd.m[k]; if (advance(m, n) == REJECT) return false; }
        for (int k = headE[xm]; k >= 0; k = pool[k].next) { Match m{pool[k].e, pool[k].d, pool[k].flags, 0}; if (advance(m, n) == REJECT) return false; }
        for (int k = headE[x];  k >= 0; k = pool[k].next) { Match m{pool[k].e, pool[k].d, pool[k].flags, 0}; if (advance(m, n) == REJECT) return false; }
        if ((e1 == D0 || e1 == nD0) && !finalStartE(xm, e1)) return false;
        if ((e2 == D0 || e2 == nD0) && !finalStartE(x, e2)) return false;
        return true;
    }
    bool finalStartE(int j, int ev) const {
        const u8 fl = (ev == D0) ? 0 : NEG;
        Match f{(u8)(j == n - 1 ? 0 : j + 1), 1, fl, 0};
        if (advance(f, n) == REJECT) return false;
        Match b{(u8)(j == 0 ? n - 1 : j - 1), 1, (u8)(fl | BWD), 0};
        return advance(b, n) != REJECT;
    }

    // n = 3 only: p = (0, 1, 2) is the single candidate.
    void leaf3() {
        const int x = __builtin_ctzll(freeVals);
        int d1 = x - p[N - 2]; if (d1 < 0) d1 += n;
        const int d2 = n - x;
        if (d1 < D0 || d1 > nD0 || d2 < D0 || d2 > nD0) return;
        const int xm = wrapDown(x - 1), xp = wrap(x + 1);
        const int e1 = (N - 1) - pinv[xm], e2 = pinv[xp] + 1;
        if (e1 < D0 || e1 > nD0 || e2 < D0 || e2 > nD0) return;
        D[N - 2] = (u8)d1; D[N - 1] = (u8)d2; putPinv(x, N - 1);
        if (finalChecks(x, xm, d1, d2, e1, e2)) { ++count; if (outMode_) { putP(N - 1, x); emit(); } }
        putPinv(x, UNK);
    }

    // =======================================================================
    // Driver
    // =======================================================================
    void run(const Options& opt, int res, int mod, SharedOutput* out) {
        girth_ = opt.girth; res_ = res; mod_ = mod; splitLevel_ = opt.splitLevel;
        outMode_ = opt.outMode; out_ = out; cyc5_ = opt.cyc5; strong_ = opt.strong;
        nonham_ = opt.nonham && !opt.snark;                 // snarks are non-hamiltonian: -S wins
        tfCnt = 0;
        if (outMode_ == 1) prepareGraph6();
        if (mod <= 1) splitLevel_ = -1;
        if (opt.girth >= 4 && n == 3) return;               // the prism has girth 3
        if constexpr (SNARK) { if (!nonham_ && n % 2 == 0) return; }   // F0 itself is an even 2-factor (but not hamiltonian)
        if (n < 6 && mod > 1) { if (res != 0) return; mod_ = 1; splitLevel_ = -1; }   // nothing to split

        // p(1) = D(0) is the minimum circular difference; girth >= g forces it to
        // be >= g-3 (a difference of circular value c gives a cycle of length c+3).
        const int d0min = std::max(1, opt.girth - 3);
        const int d0max = (n - 1) / 2;                        // D(0) = n/2 is impossible

        if constexpr (needGraph) {
            for (int v = 0; v < 2 * n; ++v) adj[v] = 0;
            for (int i = 0; i < n; ++i) {
                const int j = (i + 1) % n;
                adj[i] |= VB(1) << j;         adj[j] |= VB(1) << i;
                adj[n + i] |= VB(1) << (n + j); adj[n + j] |= VB(1) << (n + i);
            }
        }
        for (int d0 = d0min; d0 <= d0max; ++d0) {
            std::memset(pinv, UNK, sizeof pinv);
            std::memset(p, 0, sizeof p);
            std::memset(D, 0, sizeof D);
            putP(0, 0); putPinv(0, 0);
            putP(1, d0); putPinv(d0, 1);
            D[0] = (u8)d0; D0 = d0; nD0 = n - d0;
            rangeBase_ = (2ULL << nD0) - 1 - ((1ULL << d0) - 1);
            dSpecialBase_ = bit(d0) | bit(nD0);
            freeVals = FULL & ~bit(0) & ~bit(d0);
            id[1].cnt = 0;
            waitD[1].cnt = 0;
            poolTop = 0;
            waitMask = 0;
            for (int j = 0; j < n; ++j) headE[j] = -1;
            revCnt = 0;
            rev[revCnt++] = 0;                                // D-backward rotation at 0 is always live
            lastMask[1] = (2ULL << nD0) - 1 - ((1ULL << d0) - 1); // D[n-1] = n - p[n-1] in [D0, n-D0]
            if (d0 == 1) {                                    // E[0] = pinv[1] - pinv[0] = 1 = D0
                if (!startE(0, 1, 1, &waitD[1])) continue;
            }
            if constexpr (needGraph) { addSpoke(0, 0); addSpoke(1, d0); }
            if constexpr (useDom) {
                for (int r = 0; r < n; ++r) {
                    u64 m = 0;
                    for (int t = -r; t <= r; ++t) m |= bit(((t % n) + n) % n);
                    arcBase_[r] = m;
                }
                for (int v = 0; v < n; ++v) posDom[v] = FULL & ~1ULL;   // position 0 is taken
                placeDom(0, 0);
                placeDom(1, d0);
            }
            rec<2>();
            if constexpr (needGraph) { delSpoke(0, 0); delSpoke(1, d0); }
        }
        if (!outBuf_.empty()) out_->flush(outBuf_);
    }
};

// ---------------------------------------------------------------------------
// Runtime dispatch over n and the girth mode.
// Returns the number of graphs found.
template<int N, int GM, bool SNARK, bool STRONG>
u64 runThreads(const Options& opt) {
    SharedOutput out;
    const int T = std::max(1, opt.threads);
    using G = Generator<N, GM, SNARK, STRONG>;
    std::vector<std::unique_ptr<G>> gens;
    std::vector<std::thread> threads;
    for (int t = 0; t < T; ++t) gens.emplace_back(new G());
    for (int t = 0; t < T; ++t) {
        G* g = gens[t].get();
        const int res = opt.res * T + t, mod = opt.mod * T;
        threads.emplace_back([g, &opt, res, mod, &out] { g->run(opt, res, mod, &out); });
    }
    for (auto& th : threads) th.join();
    u64 count = 0;
    for (auto& g : gens) count += g->count;
    return count;
}

template<int N, bool SNARK, bool STRONG>
u64 runGirth(const Options& opt) {
    if (opt.girth <= 6) return runThreads<N, 0, SNARK, STRONG>(opt);
    if (opt.girth == 7) return runThreads<N, 7, SNARK, STRONG>(opt);
    if (opt.girth == 8) return runThreads<N, 8, SNARK, STRONG>(opt);
    return runThreads<N, 9, SNARK, STRONG>(opt);
}
template<int N, bool SNARK>
u64 runStrong(const Options& opt) {
    return opt.strong ? runGirth<N, SNARK, true>(opt) : runGirth<N, SNARK, false>(opt);
}

template<int N>
u64 dispatchN(const Options& opt) {
    if (N == opt.n) {
        if (!opt.snark && !opt.nonham) return runStrong<N, false>(opt);
        if constexpr (N <= 32) return runStrong<N, true>(opt);   // even n: no snarks (run() returns at once)
        fprintf(stderr, "snarks / non-hamiltonian graphs are only supported for n <= 32\n");
        exit(1);
    }
    if constexpr (N < NMAX) return dispatchN<N + 1>(opt);
    fprintf(stderr, "n = %d is not compiled in (NMIN = %d, NMAX = %d)\n", opt.n, NMIN, NMAX);
    exit(1);
}

static void usage() {
    fprintf(stderr,
        "usage: permsnark -n <n> [options]\n"
        "  -n <n>        length of the two cycles (order 2n), %d <= n <= %d\n"
        "                (may be omitted if the binary is compiled for a single n)\n"
        "  -g <girth>    only graphs of girth >= girth (default: all graphs)\n"
        "  -S            only permutation snarks (implies girth >= 5; none for even n)\n"
        "  -H            only non-hamiltonian graphs (implies girth >= 5; -S -H = -S)\n"
        "  -C            only cyclically 5-edge-connected graphs (implies girth >= 5)\n"
        "  -t <threads>  number of threads (default 1)\n"
        "  -r <res> -m <mod>  only the part res of mod (for splitting over machines)\n"
        "  -s <level>    recursion level of the split (default: auto)\n"
        "  -o g6|perm    write graphs in graph6 format / permutations to stdout\n"
        "  -Y            strong canonicity: exactly one graph per isomorphism class\n", NMIN, NMAX);
    exit(1);
}

int main(int argc, char** argv) {
    Options opt;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        auto next = [&]() -> const char* { if (i + 1 >= argc) usage(); return argv[++i]; };
        if (a == "-n") opt.n = atoi(next());
        else if (a == "-g") opt.girth = atoi(next());
        else if (a == "-t") opt.threads = atoi(next());
        else if (a == "-r") opt.res = atoi(next());
        else if (a == "-m") opt.mod = atoi(next());
        else if (a == "-s") opt.splitLevel = atoi(next());
        else if (a == "-o") { std::string m = next(); opt.outMode = (m == "g6") ? 1 : (m == "perm") ? 2 : 0; if (!opt.outMode) usage(); }
        else if (a == "-S") opt.snark = true;
        else if (a == "-H") opt.nonham = true;
        else if (a == "-C") opt.cyc5 = true;
        else if (a == "-Y") opt.strong = true;
        else usage();
    }
    if (opt.n == 0 && NMIN == NMAX) opt.n = NMIN;
    if (opt.n < NMIN || opt.n > NMAX || opt.threads < 1 || opt.mod < 1 || opt.res < 0 || opt.res >= opt.mod) usage();
    if (opt.snark) opt.nonham = false;                                // every snark is non-hamiltonian
    if (opt.snark || opt.nonham || opt.cyc5) opt.girth = std::max(opt.girth, 5);   // a 4-cycle yields a hamiltonian cycle / a cyclic 4-edge-cut
    if (opt.splitLevel < 0) {
        // default: split where the tree is wide enough but the redundant part above is small
        opt.splitLevel = std::min(opt.n - 3, std::max(2, opt.n / 2 - 1));
    }
    opt.splitLevel = std::min(opt.splitLevel, opt.n - 3);

    const auto t0 = std::chrono::steady_clock::now();
    const u64 count = dispatchN<NMIN>(opt);
    const double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    // The girth bound is only mentioned if it excludes graphs: for n >= 4 every
    // permutation graph has girth >= 4, and the graphs of -S, -H, -C have girth >= 5.
    const int ownGirth = (opt.snark || opt.nonham || opt.cyc5) ? 5 : (opt.n == 3 ? 3 : 4);
    std::string what = opt.cyc5 ? "cyclically 5-edge-connected " : "";
    if (opt.nonham) what += "non-hamiltonian ";
    what += opt.snark ? "permutation snark" : "permutation graph";
    if (count != 1) what += 's';
    if (opt.girth > ownGirth) what += " of girth >= " + std::to_string(opt.girth);
    what += opt.strong ? " (one per isomorphism class)" : " (weakly canonical)";
    if (opt.mod > 1) what += ", part " + std::to_string(opt.res) + " of " + std::to_string(opt.mod);
    fprintf(stderr, "n=%d order=%d: %llu %s, %.3fs, %d thread%s\n", opt.n, 2 * opt.n,
            (unsigned long long)count, what.c_str(), secs, opt.threads, opt.threads == 1 ? "" : "s");
    return 0;
}
