# permsnark

Exhaustive generation of permutation graphs and permutation snarks.

A *permutation graph* of order 2n is a cubic graph with a 2-factor that
consists of two chordless n-cycles. Number the vertices so that 0, 1, ..., n-1
and n, ..., 2n-1 are the two cycles; the remaining n edges ("spokes") form a
perfect matching, so the graph is PG(p) for a permutation p of {0, ..., n-1},
with vertex i joined to n + p(i). A *permutation snark* is a permutation
graph that is not 3-edge-colourable.

There are three programs:

* `permsnark` generates the permutation graphs of a given order, optionally
  only the snarks, the non-hamiltonian ones, the cyclically 5-edge-connected
  ones or those of a given minimum girth.
* `permcanon` filters a list of permutations: it keeps one per isomorphism
  class and/or only the cyclically 5-edge-connected graphs.
* `perm2g6` converts permutations to graph6.

The programs are based on the algorithm of

> J. Goedgebeur, J. Renders and S. Van Overberghe, Generation of cycle
> permutation graphs and permutation snarks, *Mathematics of Computation*
> (2026), [doi:10.1090/mcom/4247](https://doi.org/10.1090/mcom/4247).

If you use them in your research, please cite that paper.

## Building

You need a C++20 compiler and `make`. The code has been tested on Linux with
g++ 13 and clang++ 18.

```
make permsnark_17        # permsnark for n = 17 (order 34), about one minute
make N=17                # the same
make                     # permcanon and perm2g6
```

`permsnark` is specialised at compile time for one value of n, so you build
one binary per order. Builds for different orders are independent, so
`make -j3 permsnark_15 permsnark_16 permsnark_17` runs them in parallel.

Build options (they can be combined):

* `PORTABLE=1`: leave out `-march=native`, so the binary also runs on other CPUs.
* `CNMAX=k`: the largest n `permcanon` accepts (default 32, at most 63).
* `CXX=clang++`: clang++ 18 compiles `permsnark` about twice as fast as g++ 13
  (30 s instead of 60 s per order); the resulting binaries run within about 5 %
  of each other.

## permsnark

```
./permsnark_13                 # all permutation graphs of order 26, up to weak canonicity
./permsnark_13 -Y              # the same, one graph per isomorphism class
./permsnark_15 -g 5 -t 4       # girth >= 5, four threads
./permsnark_17 -S -t 4         # the permutation snarks of order 34
./permsnark_17 -H -t 4         # the non-hamiltonian permutation graphs of order 34
./permsnark_13 -o g6 > pg26.g6 # write the graphs in graph6 format
./permsnark_19 -S -r 3 -m 8    # part 3 of 8, for splitting a run over machines
```

Without `-Y`, the program writes one permutation from every orbit of the group of
relabellings that preserve the two cycles (order 8n^2). This is the *weak*
variant: isomorphic graphs can still appear more than once, when a graph has
more than one 2-factor made of two chordless n-cycles. With `-Y`, the *strong*
variant writes exactly one graph per isomorphism class.

| option          | meaning                                                                   |
|-----------------|---------------------------------------------------------------------------|
| `-n n`          | cycle length; can be left out, the binary knows its n                     |
| `-g g`          | only graphs of girth >= g (default: all graphs)                           |
| `-S`            | only permutation snarks (implies girth >= 5; n odd, n <= 32)              |
| `-H`            | only non-hamiltonian graphs (implies girth >= 5; n <= 32; `-S -H` is `-S`) |
| `-C`            | only cyclically 5-edge-connected graphs (implies girth >= 5)              |
| `-Y`            | strong canonicity: exactly one graph per isomorphism class                |
| `-t k`          | number of threads (default 1)                                             |
| `-r res -m mod` | only part `res` of `mod` (0 <= res < mod), for splitting a run            |
| `-s level`      | recursion level at which the work is split (default: automatic)           |
| `-o g6\|perm`   | write the graphs to stdout in graph6, or as permutations                  |

The count and the running time go to stderr. With `-o`, the graphs go to
stdout, in no particular order when more than one thread is used. With
`-o perm`, each line is a permutation `p(0) p(1) ... p(n-1)`, with p(0) = 0.

The parts of a split run (`-r`/`-m`) are disjoint, and together they give
exactly the output of the full run. Threads split the work in the same way.

## permcanon

`permcanon` reads permutations (one per line, as written by `permsnark -o perm`)
from stdin and writes the ones that pass the selected tests to stdout:

* `-Y` (the default): keep the permutations that are canonical in the strong
  sense, i.e. exactly the ones `permsnark -Y -o perm` would have written. If
  the input is the complete weak output of a run, the result is one
  permutation per isomorphism class.
* `-C`: keep only the cyclically 5-edge-connected graphs, i.e. exactly the ones
  `permsnark -C -o perm` would have written.
* `-Y -C`: apply both tests. `-C` runs first because it is much cheaper.

Each line is decided on its own, without comparing it to other lines. So the
input can come in any order and in any number of pieces, memory use stays
constant, and the output files of a split run can be filtered independently.
One consequence is that a line occurring twice in the input is also written
twice.

This is meant for large runs: run the weak variant, which is somewhat faster
than `-Y`, and filter its output afterwards. Unlike `shortg`, `permcanon` does
not need the whole set at once.

```
./permsnark_17 -S -o perm | ./permcanon           # 33 767 snarks -> 10 771 classes
./permsnark_17 -S -o perm | ./permcanon -C -Y     # -> the 12 cyclically 5-edge-connected ones
zcat part_*.gz | ./permcanon -t 4 | gzip > canonical.gz
```

Options: `-Y`, `-C` (see above); `-n n` sets the cycle length (by default it is
taken from the first line); `-t k` sets the number of threads.

## perm2g6

`perm2g6` reads permutations from stdin and writes the graphs PG(p) in
[graph6](https://users.cecs.anu.edu.au/~bdm/data/formats.html) format to
stdout, one per line and in the same order. Its output is identical to what
`permsnark -o g6` writes. Here n is a runtime value, so any order up to
1000 vertices works.

```
./permsnark_17 -S -o perm | ./permcanon -C -Y | ./perm2g6 > snarks34.g6
```

Options: `-n n` sets the cycle length (by default it is taken from the first
line); `-q` suppresses the summary on stderr.

At order 50 a graph6 line is about three times as long as the permutation. For
large runs, store the permutations and convert them only when you need graph6.

## Reference counts

To check a build:

| command                        | result                              |
|--------------------------------|-------------------------------------|
| `./permsnark_13`               | 4 622 509 (weak)                    |
| `./permsnark_13 -Y`            | 4 535 796 isomorphism classes       |
| `./permsnark_13 -S -Y`         | 64 permutation snarks               |
| `./permsnark_13 -H`            | 174 (weak)                          |
| `./permsnark_17 -S`            | 33 767 (weak)                       |
| `./permsnark_17 -S -Y`         | 10 771 permutation snarks           |
| `./permsnark_17 -S -C -Y`      | 12                                  |
| `./permsnark_17 -H`            | 33 790 (weak)                       |

## Author and license

Steven Van Overberghe, Ghent University.
Claude (Anthropic) was used to optimise the code.

permsnark is free software, released under the GNU General Public License,
version 3 or later; see [LICENSE](LICENSE).
