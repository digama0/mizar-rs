# Addendum / reproducibility for ITP 2023 paper (extended)

* The line counts for PC Mizar are given in [mizar-line-counts.txt](mizar-line-counts.txt),
  where a line with `-` represents a file which is required for the checker to
  function, and a line with `+` represents a file which is required for the
  analyzer + checker. The precise line counts come from version
  [`baeed3ca`](https://github.com/MizarProject/system/commit/baeed3ca)
  of the Mizar system.

* The line counts for `mizar-rs` are given in
  [mizar-rs-line-counts.txt](mizar-rs-line-counts.txt), along with the categorization
  used in the paper.

* The instructions for building the project itself, including the MML patches,
  can be found at [README.md](/README.md). For the head-to-head against PC Mizar,
  we compared the default configuration against one with `--orig-mizar`,
  which uses the same thread scheduling code but calls Mizar instead of using
  the internal checker, so that they would both benefit from the same level
  of parallelism.

* The folders `false1/`, `false2/`, `false3/`, `false4/`, `runnerup/` contain
  all the soundness bugs described in the paper. You can test whether your
  installation of Mizar contains the bug by seeing whether
  `mizf false1/false1.miz` checks or not. In our tests, all 5 bugs reproduce
  on 8.1.12, and only `runnerup/` reproduces in 8.1.14 (which fixed the
  soundness bugs in response to the first version of this paper).

* Logs from the benchmark run can be found at `bench-logs/`.
