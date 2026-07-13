# CLAUDE.md — Pancyclicity-in-4-connected-planar-graphs

## Project

Lean 4 formalization of the author's pancyclicity results for 4-connected
planar graphs (Bondy/Malkevitch context; target theorem
`malkevitch_conjecture` in CycleSpectrum.lean, intentionally sorried). Author:
math PhD, learning Lean hands-on via agent sessions. Exact paper statements
live in the blueprint TeX under `blueprint/` — never invent them.

## Layout

- `C4_free/Foundations/` — embedding infrastructure (CombMap, PlaneGraph,
  OuterplaneGraph, KConnected, FiveBlocks, HamiltonianDecomp). Diverged copy
  of the sibling repo's Foundations; unification is deferred, do not attempt.
- `C4_free/Axioms.lean` — deep external hammers only (Tutte 1956; Sanders,
  J. Graph Theory 24(4):341–345, 1997; Whitney). Bucket H.
- `C4_free/CycleSpectrum.lean`, `NoFourCycles.lean` — main development.
- `GraphFamily` (Gk, Theorem 1.3's extremal family) is QUARANTINED — moved to
  `docs/deferred/GraphFamily.lean.disabled`, out of the import chain. Do not
  reinstate without implementing one of the two options in
  docs/graphfamily_options.md (concrete construction, or a hypothesis-taking
  structure).
- README ledger tracks every assumed result (buckets H/P/T; D retired along
  with the quarantine — see README's Deferred section). Keep it in sync with
  any sorry/axiom change, same commit.

## Non-negotiable conventions

- **Never introduce `axiom`.** Assumed facts are `theorem foo : T := sorry`
  with doc comment: citation if external, ledger bucket, reason assumed.
- **Never leave the author with a proof he can't explain.** After completing
  any proof, provide a line-by-line explanation of why each tactic closes its
  goal.
- **No committed agent monologue.** Exploratory reasoning stays out of source;
  unproved subgoals become named, doc-commented sorried lemmas.
- **`lake build` green after every task**; revert and report if unfixable
  within the session.
- **Stop-and-report over improvising.**
- **Session log:** end every session by appending a dated summary to
  `docs/session_log.md` (append only), commit, push.
- **Prover log:** every stuck/failed proof attempt gets one line in
  `docs/prover_log.md` (date, lemma, model/tool, outcome). Failures are
  benchmark data — record them.
- Small commits, descriptive messages. Search Mathlib and Foundations/ before
  defining anything new. Single-session scoping.

## CI notes (hard-won, do not regress)

- `lint: true` removed from blueprint.yml (no lint driver registered); do not
  re-add without registering one.
- Root module must stay `lake exe mk_all` canonical; never track scratch
  .lean files — .gitignore them.
- Concurrency groups are scoped per-workflow (blueprint-/build- prefixes);
  shared groups silently cancel each other on push.

## Current milestone

1. ~~Blueprint site live and linked in README.~~ Done 2026-07-07.
2. ~~GraphFamily decision executed.~~ Done 2026-07-13: quarantined per author
   decision — file moved to docs/deferred/GraphFamily.lean.disabled, out of
   the import chain, README ledger at 0 axioms.
3. First proof: `triangular_faces_diagonal_ne` (freshly extracted, CombMap
   level) — then weekly-lemma pipeline on bucket-P items.
