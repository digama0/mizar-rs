# Mizar proof checker

This is a (still experimental) proof checker for the [Mizar language](http://mizar.org).
To compile the project, get Rust 1.67 or later (https://rustup.rs) and then build using
`cargo build --release`.

The program works on a patched version of the Mizar Mathematical Library.
To get it, run `./download-mml.sh`, which will download the MML into the `miz/`
directory and apply the patch.
```sh
./download-mml.sh
```
Alternatively you can symlink `miz/` to your local mizar installation.

The first thing you will want to do is compile the `prel/` files which represent the
the theory exports for each article. This breaks the dependencies between files and
allows everything to be processed in parallel.
```shell
$ time ./analyze-mml.sh
Executed in   34.97 secs    fish           external
   usr time  156.45 secs  462.00 micros  156.44 secs
   sys time    3.04 secs   93.00 micros    3.04 secs
```

You can then test the checker on the MML. You should get a result like this:
```shell
$ time cargo run --release
   6: xfamily  in 0.004s
   2: boole    in 0.005s
   0: tarski   in 0.006s
  10: subset   in 0.006s
...
1411: integr25 in 7.381s
1406: integr24 in 17.492s
1410: glib_015 in 15.041s
1408: field_9  in 30.482s
1367: wallace1 in 92.534s
flex expansion bug: 6
success: 1215274
________________________________________________________
Executed in  755.23 secs    fish           external
   usr time   88.83 mins  415.00 micros   88.83 mins
   sys time    0.20 mins   78.00 micros    0.20 mins
```

Here is a performance comparison of running the original Mizar checker vs the new `mizar-rs` checker on the entire MML, on 8 cores:

|                               | `mizar-rs` | `verifier` | speedup |
|-------------------------------|------------|------------|---------|
| real time, analyzer           | 2.42 min   | 18.28 min  | 7.56x   |
| CPU time, analyzer            | 13.14 min  | 66.25 min  | 5.04x   |
| real time, checker            | 11.33 min  | 57.37 min  | 5.06x   |
| CPU time, checker             | 73.70 min  | 417.57 min | 5.67x   |
| real time, analyzer + checker | 11.71 min  | 71.38 min  | 6.10x   |
| CPU time, analyzer + checker  | 81.93 min  | 490.55 min | 5.99x   |

Note that, compared to `verifier`, `mizar-rs` benefits more from running both parts together rather than separately (the `analyzer + checker` row is less than `analyzer` plus `checker`), because `mizar-rs` does not do two passes.
See [#2](https://github.com/digama0/mizar-rs/issues/2#issuecomment-1467281905) for more detailed plots and per-file measurements.

Here some additional mizar-rs modes, together with the time taken to check the MML on 8 threads:

|                            | command    | real time | CPU time   |
|----------------------------|------------|-----------|------------|
| accom + export             | `-ex`      | 28.88 sec | 3.44 min   |
| export                     | `-PMex`    | 31.22 sec | 3.71 min   |
| accom + analyzer           | `-a`       | 1.75 min  | 12.99 min  |
| analyzer                   | `-PMa`     | 1.70 min  | 12.83 min  |
| checker                    | `-PMc`     | 11.33 min | 73.70 min  |
| accom + analyzer + checker |  (default) | 11.86 min | 88.87 min  |
| analyzer + checker         | `-PM`      | 12.45 min | 91.84 min  |

* The "export" mode also includes running the analyzer in "quick" mode, which does just enough analysis to construct theorem statements. This constructs the `prel/` data for dependent articles, and represents the not-trivially-parallelizable part of MML processing when generating data files from scratch.

* The "accom" mode (which can be mixed with any of the others) uses the `prel/` files directly to import dependencies, rather than using the files prepared by Mizar's `accom` tool. As the numbers show, the cost of this extra processing is sometimes negative, because we are reading fewer files total and doing less XML parsing.

## Usage and configuration

The `mizar-rs --help` output is replicated here for convenience:
```
Mizar verifier toolchain. Common usage cases:

  * mizar-rs -dex --overwrite-prel
    Read the MML .miz files and generate the prel/ folder
  * mizar-rs
    Parse and compile the whole MML from scratch
  * mizar-rs nat_4 --one-file
    Parse and compile only article nat_4
  * mizar-rs nat_4 14 --unify-insts
    Give debugging info regarding the item at line 14 of article nat_4

Usage: mizar-rs [OPTIONS] [FILE] [FIRST_VERBOSE_LINE]

Arguments:
  [FILE]
          The name of the first file to process, or the index of the file in `mml.lar`

  [FIRST_VERBOSE_LINE]
          The line on which to turn on verbose mode

Options:
  -h, --help
          Print help (see a summary with '-h')

  -V, --version
          Print version

Pass selection options:
  -c, --checker
          Enables (only) the checker, checking 'by' proofs straight from .xml

  -C, --no-checker
          Disables the checker, checking the proof skeleton but not individual by steps

  -a, --analyzer
          Enables (only) the analyzer, checking the proof skeleton but not individual by steps

  -A, --no-analyzer
          Disables the analyzer

  -e, --export
          Enables (only) the exporter, doing the minimal amount of work to produce theorem statements

  -E, --no-export
          Disables the exporter

  -v, --verify-export
          Check that the exported statements exactly match the `miz/mizshare/prel/` directory

  -x, --xml-export
          Produce exported statements to the `miz/prel/` directory (requires `-e`)

  -M, --no-accom
          Disables the accomodator. (requires `-P`)

  -P, --no-parser
          Disables the parser, reading .wsx files instead of .miz

  -N, --no-nameck
          Disables name resolution, reading .msx instead of .wsx (requires `-P`)

  -d, --dep-order
          Strictly follow dependency order, instead of using `prel/`

  -j, --parallelism <PARALLELISM>
          The number of threads to use (currently only file level parallelism is supported)

          [default: 8]

      --orig-mizar
          Use `mizar-rs` as a frontend for the original mizar `verifier`

      --one-item[=<ONE_ITEM>]
          Exit after processing the first verbose item

          [default: true]

      --one-file[=<ONE_FILE>]
          Exit after processing the first selected file

          [default: false]

      --skip-to-verbose[=<SKIP_TO_VERBOSE>]
          Disable the checker while not in verbose mode

          [default: false]

Other options:
      --panic-on-fail[=<PANIC_ON_FAIL>]
          Panic on the first error

          [default: false]

      --overwrite-prel[=<OVERWRITE_PREL>]
          Write exported statements to `miz/mizshare/prel/` instead of `miz/prel/`, overwriting the originals

          [default: false]

      --no-cache
          Always read cross-article theorems from `prel/` instead of from memory

      --no-progress
          Don't show the fancy progress bar

Debugging tools:
      --top-item-header[=<TOP_ITEM_HEADER>]
          Print a header at every top level item

          [default: false]

      --always-verbose-item[=<ALWAYS_VERBOSE_ITEM>]
          Print the full AST for each item, even when not in verbose mode

          [default: false]

      --item-header[=<ITEM_HEADER>]
          Print a header at each item

          [default: false]

      --checker-inputs[=<CHECKER_INPUTS>]
          Print the checker input facts in verbose mode

          [default: false]

      --checker-header[=<CHECKER_HEADER>]
          Print the checker header in verbose mode

          [default: false]

      --checker-conjuncts[=<CHECKER_CONJUNCTS>]
          Print the processed checker conjuncts in verbose mode

          [default: false]

      --checker-result[=<CHECKER_RESULT>]
          Print the checker result in verbose mode

          [default: false]

      --unify-header[=<UNIFY_HEADER>]
          Print the input to the unifier module in verbose mode

          [default: false]

      --unify-insts[=<UNIFY_INSTS>]
          Print the instantiation produced by the unifier in verbose mode

          [default: false]

      --dump [<DUMP>...]
          Dump the contents of various system components, or `--dump` without arguments to print everything

          [possible values: config, constructors, requirements, notations, clusters, definitions, libraries, formatter]

Bugs and unsound flags:
      --legacy-flex-handling[=<LEGACY_FLEX_HANDLING>]
          This is an UNSOUND FLAG that enables checking of `P[a] & ... & P[b]` equality by checking only the endpoints `P[a]` and `P[b]`. This is needed to check some MML proofs

          [default: true]

      --attr-sort-bug[=<ATTR_SORT_BUG>]
          This is buggy behavior, but not unsound. It is required to interpret some MML files

          [default: true]
```

## Formatter configuration

There is some additional configuration at the top of [format.rs](src/format.rs) which
controls how expressions are printed.

```rust
enable_formatter: true,
```
This one sounds odd but it is possible to disable the formatter in the sense that it will
not attempt to load symbols and constructor names. So instead of printing
`c2 " is Element of bool [:c1, c0:]` it will show `F11(c2) is M2 of F18(F19(c1, c0))`.

```rust
show_infer: false,
show_only_infer: false,
```
These control whether to show "infer constants" as `e`, `?3=e` or `?3`, assuming
constant `?3` is defined to be `e`.

```rust
show_priv: false,
```
This shows private functors/predicates as `$F2(x + 1, y):=(x + 1 - y)` or `$F2(x + 1, y)`.

```rust
show_marks: false,
```
This shows EqMark nodes in an expression in the style `3'(x + y)`.

```rust
show_invisible: false,
```
This controls whether to show all arguments to a functor or just the ones marked "visible".
For example `incl A` (where `A is Subset of Y`) has one visible argument but
`Y` is an invisible argument; when this option is enabled it will be shown as `incl(Y, A)`
instead. (Because the formats which specify how many arguments of a function go left and
how many go to the right, and these have to match the number of visible arguments, enabling
this option causes such functions to be displayed in prefix style.)

```rust
show_orig: false,
```
This is a slightly more readable version of `ENABLE_FORMATTER = false`. It shows the numbers
for each constructor in brackets after it. So the example from before would be shown as
`c2 "[11] is Element[2] of bool[18] [:[19] c1, c0:]`. Besides being useful in cross-referencing
with Mizar numbers, it also makes it clear when overloading or redefinitions are involved,
since these can appear the same but have different constructor numbers.

```rust
upper_clusters: false,
both_clusters: false,
```
This shows the inferred cluster attributes after each type.
Upper clusters are marked with a `+`. Example:
* Default (lower clusters only):
  ```
  Function-like quasi_total Element of bool [:{}, b1:]
  ```
* Upper clusters only:
  ```
  +Relation-like +non-empty +empty-yielding +{}-defined +b1-valued +Function-like
  +one-to-one +constant +functional +empty +trivial
  +non proper +total +quasi_total Element of bool [:{}, b1:]
  ```
* Both clusters:
  ```
  Function-like quasi_total +Relation-like +non-empty +empty-yielding
  +{}-defined +b1-valued +Function-like +one-to-one +constant +functional +empty +trivial
  +non proper +total +quasi_total Element of bool [:{}, b1:]
  ```

```rust
negation_sugar: true,
```
This controls whether to heuristically use `→`,`∨`,`∧` and `∀`/`∃` to minimize the number
of explicit `¬` symbols, or whether to use negations precisely as they are represented
internally and use only `∧` and `∀`.

* With negation sugar:
  ```
  ∃ b0: Relation-like Function-like set st
    ((proj1 b0) = S0()) ∧
      (∀ b1: object holds
        (b1 in S0()) → ((SP0[b1] → ((b0 . b1) = S2(b1))) ∧ (SP0[b1] ∨ ((b0 . b1) = S3(b1)))))
  ```
* No negation sugar:
  ```
  ¬(∀ b0: Relation-like Function-like set holds
    ¬(((proj1 b0) = S0()) ∧
      (∀ b1: object holds
        ¬((b1 in S0()) ∧
          ¬(¬(SP0[b1] ∧ ¬((b0 . b1) = S2(b1))) ∧ ¬(¬SP0[b1] ∧ ¬((b0 . b1) = S3(b1))))))))
  ```

*Note: Currently we are making no attempt to make these expressions re-parsable by Mizar.
They are intended purely for presentation purposes.*

## Future directions

Right now this project contains the checker and analyzer parts of the Mizar system, but
with a bit more work the parser too can be incorporated and then this will be a fully
fledged potential `mizf` replacement. Besides this, a major component that has not yet
been started is proof export; this will require a bit of design work but should help
to address the soundness issues in the current architecture.

## License

This project is based on the [Mizar system](https://github.com/MizarProject/system),
and is distributed under the terms of the GPLv3 license. See [LICENSE](LICENSE) for more information.

## Contributing

Contributions are most welcome. Please post issues for any bugs you find or submit PRs for improvements.
I (@digama0) hope that this tool and its open development process can improve the state of Mizar tooling
for everyone.
