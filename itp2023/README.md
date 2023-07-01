# Addendum / reproducibility for ITP 2023 paper

* The line counts for PC Mizar are given in [mizar-line-counts.txt](mizar-line-counts.txt),
where a line with `-` represents a file which is required for the checker to
function, and a line with `+` represents a file which is required for the
analyzer + checker. The precise line counts come from version
[`baeed3ca`](https://github.com/MizarProject/system/commit/baeed3ca)
of the Mizar system.

* The instructions for building the project itself, including the MML patches,
  can be found at [README.md](/README.md). For the head-to-head against PC Mizar,
  we compared the default configuration against one with `--orig-mizar`,
  which uses the same thread scheduling code but calls Mizar instead of using
  the internal checker, so that they would both benefit from the same level
  of parallelism.

* The folders `false1/`, `false2/`, `false3/`, `false4/`, `runnerup/` contain
  all the soundness bugs described in the paper. You can test whether your
  installation of Mizar contains the bug by seeing whether
  `mizf false1/false1.miz` checks or not.

# Addendum / reproducibility for Mizar 50 paper

The full MML patch file can be found at [mml.patch](/mml.patch), which you can
apply to version 5.74.1441 of the MML by running `./download-mml.sh`.

The patch file was primarily contributed in five parts:

* [the original file, after upgrading to MML v5.74.1441](https://github.com/digama0/mizar-rs/blob/2a4dd301/mml.patch).
  This contains two kinds of modification:
  * The insertion of `requirements BOOLE` to make the proof check with the
    new verifier
  * The new verifier does not support `scheme P; <lines> end;`, it requires
    the form `scheme P proof <lines> end;`. This is a relatively simple modification
    which I think is reasonable to upstream as it makes the grammar more regular,
    but it is largely cosmetic.

* [improved XPRIMET1 proof](https://github.com/digama0/mizar-rs/commit/cd4fa10d)
* [improved NUMBER04 proof](https://github.com/digama0/mizar-rs/commit/e1638f91)
* [improved XPRIMES1, XPRIMES2 proof](https://github.com/digama0/mizar-rs/commit/49d66ac3)
* [improved NUMBER07 proof](https://github.com/digama0/mizar-rs/commit/0f249eff)

The last 4 have more description of the individual changes on the commit logs.

As above, see [README.md](/README.md) for information on how to set up `mizar-rs`.
To time the particular files discussed here, you will want to use one of the patch
files in the mentioned commits to get a suitable version of the MML for testing,
and then run `cargo build --release` and then
`time target/release/mizar-rs <N> --one-file` where `N` is the ordinal of this file
in the `mml.lar` file:

* XPRIMET1: `time target/release/mizar-rs 287 --one-file`
* NUMBER04: `time target/release/mizar-rs 1433 --one-file`
* XPRIMES1: `time target/release/mizar-rs 1425 --one-file`
* XPRIMES2: `time target/release/mizar-rs 1426 --one-file`
* NUMBER07: `time target/release/mizar-rs 1442 --one-file`

To run a comparison test using PC Mizar you can either run the same command with
`--orig-mizar` to use `mizar-rs` as a shim for `verifier`, or just run e.g.
`time env MIZFILES=miz/mizshare miz/mizbin/verifier miz/mizshare/mml/xprimet1.miz`
directly.
