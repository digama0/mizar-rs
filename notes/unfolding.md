# `unfolding` proof step — feature parity

Reference: A. Grabowski, A. Kornilowicz, *Implementing More Explicit Definitional
Expansions in Mizar*, ITP 2023 (LIPIcs 268). The Pascal implementation source is
**not public** (mainline Mizar has no unfolding as of 2026-04; the
`arturkornilowicz/unfolding` repo and the uwb project page are the paper's *dataset*
only — 2776 `.den` expansion-position records + 378 study `.miz` + `syntax.txt` +
`appendix.pdf`, no source). So we work spec-driven, with the `.den` files as a
behavioral oracle for the core expansion.

## Semantics (paper §254)

`unfolding` makes Mizar's *existing* definitional-expansion mechanism explicit: when a
statement does not match the current goal, the verifier searches the `definitions`
directive for a definiens matching the goal and replaces the goal. `unfolding R1, R2;`
names which definitions to expand, in order, left-to-right. Only **atomic** formulae
are expandable.

Grammar (`syntax.txt`): `Unfolding = "unfolding" References ";"`.

## Error codes (appendix)

| condition | code |
|---|---|
| references missing (`unfolding;`) | 308 |
| ref is not a `def` (`RELAT_1:3`) | 288 |
| def not imported in `definitions` directive | 144, 203 |
| def number too big / inaccessible | 199 |
| expanded def does not match thesis | 67 |
| thesis is not atomic/expandable | 61 |

## Lifecycle in mizar-rs (on `main`)

- **parse** `.miz` (`parser/miz.rs`): `unfolding` -> `ItemKind::Unfold(refs)` — DONE.
- **algorithm** (`analyze.rs` `unfold` + `try_unfold`): peel thesis to atom, match
  definiendum, expand definiens (handles cases/otherwise/assumptions) — DONE, shared
  with the automatic-expansion path.
- **errors** (`analyze.rs::unfold`): `panic!` (reporting is on the `errors` branch)
  now carrying the appendix codes+messages — 288 (theorem ref where a def is
  required), 199 (unresolved/inaccessible), 67 (definiens does not match), 61
  (non-atomic thesis) — DONE.
- **`-X` writer** (`write.rs::unfold`): emits `<Unfolding><Ref.../>...</Unfolding>`
  then, like take/thus, the post-expansion `<Thesis>` (state -> after_reasoning) —
  DONE.
- **analyzed reader** (`parser/article.rs`): `b"Unfolding"` -> `Item::Unfold` via the
  existing `parse_references`; in the reasoning-loop skeleton group so it reads the
  trailing `<Thesis>` — DONE.
- **analyzed Item** (`types.rs`): `Item::Unfold(Vec<Reference>)` — DONE.
- **checker read** (`reader.rs`): no-op like `Take` (re-verifies justifications, not
  thesis reconstruction) — DONE.
- **`.msx` reader** (`parser/msm.rs`): reads `<Unfolding>` + `<*-Reference>` — DONE.
- **reconstruction** (`analyze.rs` `ReconstructThesis::unfold`): keeps its `panic!`.
  Like `take`, `unfolding` never occurs in a diffuse (`now`) block, so this is a
  genuine invariant, not a gap — DONE (assessed).
- **JSON** (`parser/json.rs`): `fix_references` — DONE.

## Verified

- Minimal proof `X c= Y` unfolding `TARSKI:def 3` to its membership form: checks
  (`success: 1`); `-X` emits well-formed XML with `<Unfolding><Ref nr="3"
  articlenr="1" kind="D"/></Unfolding><Thesis>…`; round-trips through
  `--xml-internals-self-test` (exit 0, no mismatch).
- Each error code fires on a crafted input (288/199/67/61).
- MML unaffected: tarski 23, xboole_0 81, subset_1 379, zfmisc_1 728; round-trip
  clean.

## Not done / caveats

- The `.wsx`/`.msx` *writer* form (`<Definition-Reference>`/`<Local-Reference>` from
  the paper) is only the *reader* side here; mizar-rs writes the analyzed `<Ref>`
  form. No behavioural difference for `-X`.
- No public reference implementation to diff against; core expansion validated only
  via the shared `try_unfold` (used by automatic expansion across the whole MML) and
  the crafted proofs. The `.den` oracle (2776 expansion positions) is available for a
  deeper cross-check but not yet run.
