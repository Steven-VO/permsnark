// perm2g6.cpp -- convert permutation words into graph6.
//
// Input: permutation words as written by "permsnark -o perm", one per line
// (n numbers separated by blanks, p(0) p(1) ... p(n-1)).  Output: the same
// graphs in graph6 format, one line each, in the same order -- exactly what
// "permsnark -o g6" writes for the same search.
//
// The word p stands for the permutation graph PG(p) of order 2n: the vertices
// 0..n-1 and n..2n-1 induce the two chordless n-cycles and vertex i is joined
// to vertex n + p(i) by a spoke.  graph6 (McKay) writes the upper triangle of
// the adjacency matrix column by column: bit k of the bit string, counted from
// the left, is the entry (i, j) with k = j(j-1)/2 + i, i < j; the bits are
// packed six per byte and shifted by 63, preceded by the order (one byte
// 63 + V for V <= 62, else '~' and three such bytes).  The n(n-1) cycle
// entries do not depend on p, so only the n spoke bits are set per line.
//
// Build:  make perm2g6
// Usage:  ... | ./perm2g6 [-n n] > out.g6
//         (without -n the length of the first line decides; -q suppresses the
//         summary on stderr)
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

#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

using u8 = uint8_t;
using u64 = uint64_t;

static constexpr int NMAXV = 1000;              // largest order we bother with

int main(int argc, char** argv) {
    int n = 0;
    bool quiet = false;
    for (int i = 1; i < argc; ++i) {
        const std::string a = argv[i];
        if (a == "-n" && i + 1 < argc) n = atoi(argv[++i]);
        else if (a == "-q") quiet = true;
        else {
            fprintf(stderr, "usage: perm2g6 [-n <n>] [-q] < in.perm > out.g6\n"
                            "  reads permutation words (permsnark -o perm) from stdin and writes\n"
                            "  the permutation graphs PG(p) of order 2n in graph6 to stdout\n"
                            "  -n <n>  length of the two cycles (default: from the first line)\n"
                            "  -q      no summary on stderr\n");
            return 1;
        }
    }
    if (n < 0 || (n && n < 3) || 2 * n > NMAXV) { fprintf(stderr, "perm2g6: n out of range (3 <= n <= %d)\n", NMAXV / 2); return 1; }

    std::string in, out;
    std::vector<u8> tmpl;                       // the cycle edges (constant part)
    std::vector<u8> body;
    std::string prefix;
    const auto t0 = std::chrono::steady_clock::now();

    // The graph6 template of the two n-cycles, and the order prefix.
    auto setup = [&]() {
        const int V = 2 * n;
        const int bits = V * (V - 1) / 2;
        tmpl.assign((size_t)(bits + 5) / 6, 0);
        auto set = [&](int i, int j) {           // i < j
            const int k = j * (j - 1) / 2 + i;
            tmpl[(size_t)k / 6] |= (u8)(1 << (5 - k % 6));
        };
        for (int i = 0; i + 1 < n; ++i) { set(i, i + 1); set(n + i, n + i + 1); }
        set(0, n - 1); set(n, 2 * n - 1);
        prefix.clear();
        if (V <= 62) prefix += (char)(63 + V);
        else { prefix += (char)126; prefix += (char)(63 + (V >> 12)); prefix += (char)(63 + ((V >> 6) & 63)); prefix += (char)(63 + (V & 63)); }
        body.resize(tmpl.size());
    };
    if (n) setup();

    const size_t CHUNK = size_t(1) << 22;
    std::string buf(CHUNK, '\0');
    std::string tail;
    u64 lines = 0;
    int p[NMAXV / 2];

    auto flush = [&]() {
        if (out.empty()) return;
        if (fwrite(out.data(), 1, out.size(), stdout) != out.size()) { perror("perm2g6: writing stdout"); exit(3); }
        out.clear();
    };

    for (;;) {
        const size_t got = fread(&buf[0], 1, CHUNK, stdin);
        if (got == 0 && ferror(stdin)) { perror("perm2g6: reading stdin"); return 3; }
        tail.append(buf.data(), got);
        const bool last = (got == 0);
        size_t pos = 0;
        for (;;) {
            const size_t nl = tail.find('\n', pos);
            size_t end;
            if (nl == std::string::npos) {
                if (!last || pos >= tail.size()) break;
                end = tail.size();                       // a last line without newline
            } else end = nl;
            const size_t lineStart = pos;
            const char* s = tail.data() + pos;
            const char* const e = tail.data() + end;
            pos = (nl == std::string::npos) ? tail.size() : nl + 1;
            if (s == e) continue;                        // empty line

            // --- parse the word ---
            int cnt = 0;
            bool ok = true;
            while (s < e && ok) {
                while (s < e && (*s == ' ' || *s == '\t' || *s == '\r')) ++s;
                if (s == e) break;
                if (*s < '0' || *s > '9') { ok = false; break; }
                int v = 0;
                while (s < e && *s >= '0' && *s <= '9') { v = 10 * v + (*s++ - '0'); if (v > NMAXV) { ok = false; break; } }
                if (cnt >= NMAXV / 2) { ok = false; break; }
                p[cnt++] = v;
            }
            if (!n && ok && cnt) {                       // the first line fixes n
                n = cnt;
                if (n < 3 || 2 * n > NMAXV) { fprintf(stderr, "perm2g6: n = %d is out of range (3 <= n <= %d)\n", n, NMAXV / 2); return 1; }
                setup();
            }
            if (!ok || cnt != n) {
                if (n) fprintf(stderr, "perm2g6: not a permutation word of length %d: %.*s\n",
                               n, (int)(end - lineStart), tail.data() + lineStart);
                else   fprintf(stderr, "perm2g6: not a permutation word: %.*s\n",
                               (int)(end - lineStart), tail.data() + lineStart);
                return 2;
            }
            bool seen[NMAXV / 2] = {};                   // a permutation of [n]?
            bool perm = true;
            for (int i = 0; i < n && perm; ++i) {
                if (p[i] >= n || seen[p[i]]) perm = false;
                else seen[p[i]] = true;
            }
            if (!perm) {
                fprintf(stderr, "perm2g6: not a permutation of [%d]: %.*s\n",
                        n, (int)(end - lineStart), tail.data() + lineStart);
                return 2;
            }

            // --- encode ---
            memcpy(body.data(), tmpl.data(), tmpl.size());
            for (int i = 0; i < n; ++i) {
                const int j = n + p[i];
                const int k = j * (j - 1) / 2 + i;
                body[(size_t)k / 6] |= (u8)(1 << (5 - k % 6));
            }
            out += prefix;
            for (size_t k = 0; k < body.size(); ++k) out += (char)(63 + body[k]);
            out += '\n';
            ++lines;
            if (out.size() > (size_t(1) << 20)) flush();
        }
        tail.erase(0, pos);
        if (last) break;
    }
    flush();
    if (fflush(stdout) != 0) { perror("perm2g6: writing stdout"); return 3; }
    if (!quiet) {
        const double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        if (!n) fprintf(stderr, "perm2g6: empty input\n");
        else fprintf(stderr, "n=%d order=%d: wrote %llu graph%s in graph6, %.3fs\n",
                     n, 2 * n, (unsigned long long)lines, lines == 1 ? "" : "s", secs);
    }
    return 0;
}
