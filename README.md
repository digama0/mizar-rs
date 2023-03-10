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

For testing the new checker on the MML, you need the `.xml` files for each mizar file,
which is not distributed by default. The following command will run the (original)
Mizar `accom` and `verifier -a` commands on everything, producing all the extra
files needed for processing. (Hopefully soon it will only be necessary to run
the parser to generate the `.msx` file, once the analyzer is tested and working.
But if you want to use the new checker alone you will need to run the old analyzer
because there are no plans for the new analyzer to generate `.xml` files.)
Note that this takes a while: it uses [GNU parallel](https://www.gnu.org/software/parallel/)
if available so you are encouraged to install that if you don't already have it.
```shell
$ time ./analyze-mml.sh
Executed in   19.62 mins    fish           external
   usr time   82.16 mins  530.00 micros   82.16 mins
   sys time    1.49 mins  209.00 micros    1.49 mins
```
After "unpacking" the MML grows to 12.7G, so beware if you are short on space.

You can then test the checker on the MML. You should get a result like this:
```shell
$ time cargo run --release
0: tarski
1: xboole_0
2: boole
...
1411: integr25
expected failure: 3
flex expansion bug: 6
success: 1215271
________________________________________________________
Executed in  710.71 secs    fish           external
   usr time   76.82 mins    0.00 micros   76.82 mins
   sys time    0.25 mins  301.00 micros    0.25 mins
```

Here is a performance comparison of running the original Mizar checker vs the new `mizar-rs` checker on the entire MML:

|           | `mizar-rs` | `verifier -c` | speedup |
|-----------|------------|---------------|---------|
| real time | 11.84 min  | 57.37 min     | 4.84x   |
| CPU time  | 76.82 min  | 417.57 min    | 5.49x   |

## Configuration

Currently all configuration is stored in the code itself. Most flags are in
[main.rs](src/main.rs) at the start of `main()`, and can be used to debug why a proof fails:
```rust
top_item_header: false,
always_verbose_item: false,
item_header: DEBUG,
checker_inputs: DEBUG,
checker_header: DEBUG,
checker_conjuncts: false,
checker_result: false,
unify_header: false,
unify_insts: false,
```

There are also options to dump various parts of the input state:
```rust
dump_constructors: false,
dump_requirements: false,
dump_definitions: false,
dump_libraries: false,
dump_formatter: false,
```

This is equivalent to the `-a` and `-c` flags in Mizar. You will want to use this
if you want to test the new analyzer (which is still experimental).
```rust
analyzer_enabled: false,
checker_enabled: true,
```

When this is enabled, the new checker is disabled completely and the only thing
that remains of the program is the top loop which dispatches file tasks, shelling
out to `mizbin/verifier`. This is used for timing comparisons.
```rust
const ORIG_MIZAR: bool = false;
```

These flags cover behavior which is known to be buggy but require more substantial
patching of MML:
```rust
legacy_flex_handling: true,
flex_expansion_bug: true,
attr_sort_bug: true,

const EXPECTED_ERRORS: &[(&str, usize)] =
  // These failures are caused by a bug in the statement of FLEXARY1:def 9
  // which requires a patch to Mizar, at least as long as we are using the Mizar analyzer
  &[("eulrpart", 153), ("eulrpart", 154), ("eulrpart", 628)];
```

This is used for zooming in on a particular proof or file. The number of each file
is printed in release mode, and you can use `FIRST_FILE` to start processing from there
and `ONE_FILE` to process only that file. The `FIRST_VERBOSE` options enable the
`vprintln` verbose debug logging, so you can see exactly how a particular proof proceeds.
```rust
const FIRST_FILE: usize = 0;
const ONE_FILE: bool = false;
panic_on_fail: DEBUG,
first_verbose_top_item: None,
first_verbose_item: None,
one_item: false,
first_verbose_checker: None,
skip_to_verbose: DEBUG,
```

The `parallelism` option controls how many parallel threads are used. Adjust this to taste.
```rust
parallelism: if DEBUG || ONE_FILE { 1 } else { 8 },
```

Original Mizar `verifier -c`:
```
________________________________________________________
Executed in   57.37 mins    fish           external
   usr time  417.57 mins  644.00 micros  417.57 mins
   sys time    1.26 mins    0.00 micros    1.26 mins
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
