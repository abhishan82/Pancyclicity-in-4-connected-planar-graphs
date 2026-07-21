# Session Log

Dated summaries of agent work sessions on this repo. Newest entries at the top.

## 2026-07-21 — Thread `hn : 5 ≤ Fintype.card V` through the triangular-faces chain

**Context**: follow-up to the 2026-07-16 disproof of `triangular_faces_diagonal_ne`
(K₃ counterexample). While discussing where that lemma sits in the paper's
proof (it's step 3 of Proposition 6.1's proof, `edge_bound_no_four_cycles`),
the author pointed out that `edge_bound_no_four_cycles` already carries
`hn : 5 ≤ Fintype.card V` — it just never gets passed down through
`triangular_faces_edge_disjoint` into `triangular_faces_diagonal_ne`, neither
of which accepted it. So the fix isn't introducing a new assumption, it's
correctly plumbing one that was already true at the only real call site.

**Done**:
1. Added `hn : 5 ≤ Fintype.card V` to `triangular_faces_diagonal_ne`'s
   signature; doc comment updated with a dated correction note pointing at
   the K₃ counterexample and clarifying this is a threading fix, not new
   math, and that sufficiency (does `n ≥ 5` actually complete the proof?) is
   still open.
2. Added the same hypothesis to `triangular_faces_edge_disjoint` (its only
   purpose there is to pass it through) and updated its one internal call to
   `triangular_faces_diagonal_ne` to supply `hn`.
3. Updated `edge_bound_no_four_cycles`'s call to `triangular_faces_edge_disjoint`
   to pass its own (already-present) `hn`.
4. Verified: `grep` confirms no other call sites of either lemma exist.
   `lake build` green, 1315 jobs, same single `sorry` as before (statement
   changed, proof still deferred).
5. Logged the correction in `docs/prover_log.md` (2026-07-21 entry, distinct
   from the 2026-07-16 disproof — append-only, nothing edited).
6. Rewrote `docs/next_session.md`: threading is done, so next session's task
   is now just the proof attempt under the corrected (hopefully true)
   statement, with the sufficiency question flagged explicitly as something
   that attempt needs to resolve, not assume.

**State at end of session**: `main` pushed (pending), `lake build` green,
`triangular_faces_diagonal_ne` and `triangular_faces_edge_disjoint` both now
require `n ≥ 5`, both still `sorry`/depend-on-`sorry` respectively.

## 2026-07-16 — triangular_faces_diagonal_ne disproved (K₃ counterexample)

**Context**: session-startup task from `docs/next_session.md` (queued
2026-07-13): prove `triangular_faces_diagonal_ne`, no new axioms/sorries,
statement unchanged, search Mathlib/Foundations first, stop-and-report after
3 distinct failed strategies.

**Done**:
1. Before writing any tactics, worked through the lemma's actual mathematical
   content by hand: it claims that gluing two triangular faces along a dart
   forces their two "opposite" corner vertices to differ. Suspected a
   degenerate small-graph case could violate this (the inner/outer faces of
   a bare triangle share every edge, and the "opposite" vertex is the same
   one in both, since there are only 3 vertices total).
2. Verified the suspicion formally rather than trusting hand-analysis: built
   `K₃` (`Fin 3`, complete graph) as an explicit `G.PlaneGraph` in a scratch
   file (rotation system = swap the 2 darts at each vertex per vertex;
   `Euler formula` and `face_orbit_simple` both `decide`d). Its unique
   embedding has exactly 2 faces, both triangular, sharing all 3 edges.
3. Instantiated `triangular_faces_diagonal_ne`'s exact 10 hypotheses with
   concrete witnesses from this model and proved, as one `decide`d
   conjunction, that every hypothesis holds **and** the conclusion's
   negation holds (i.e. the conclusion is false). `#print axioms` on this
   confirmed **zero `sorryAx`** — a genuine, sorry-free disproof, not an
   artifact of the lemma's own `sorry`.
4. Diagnosis: the lemma (and its only caller, `triangular_faces_edge_disjoint`)
   has no vertex-count hypothesis excluding this case. Every sibling lemma in
   `NoFourCycles.lean` carries `hn : 5 ≤ Fintype.card V`; these two don't.
   Fixing this requires a statement change (adding that hypothesis and
   threading it through the call site) — out of scope for this session's
   "statement unchanged" constraint.
5. Deleted the scratch verification file (never committed, per the
   no-scratch-files rule). Logged the full counterexample in
   `docs/prover_log.md` (2026-07-16 entry).
6. Presented findings to the author with three options (fix now / defer to
   next session / other). Author chose defer. Seeded `docs/next_session.md`
   with a pre-authorized statement-change task: add
   `hn : 5 ≤ Fintype.card V` to both lemmas, verify `lake build` green, then
   attempt the proof under the corrected statement.

**State at end of session**: no changes to `C4_free/` source this session —
the finding is a disproof of the existing statement, not a fix. `lake build`
unaffected (not rebuilt, no source touched). `docs/prover_log.md`,
`docs/next_session.md` updated; this entry appended.

## 2026-07-13 — Quarantine GraphFamily.lean; repo now axiom-free

**Context**: author's decision from `docs/graphfamily_options.md` (Task 6):
quarantine `Gk` rather than pursue a concrete construction or a
hypothesis-bundling structure right now.

**Done**:
1. Confirmed via repo-wide grep (`Gk\b|GkVertex|gkSrc|gkTgt|GraphFamily`
   across `C4_free/`) that nothing outside `GraphFamily.lean` itself
   referenced any of it — matches the earlier Task 6 finding, so quarantining
   costs nothing downstream in the Lean code.
2. Moved `C4_free/GraphFamily.lean` to
   `docs/deferred/GraphFamily.lean.disabled` (`.disabled` extension keeps
   Lake from compiling it) with a header comment explaining why it's
   quarantined and how to reinstate it. Removed `import C4_free.GraphFamily`
   from `C4_free.lean` via `lake exe mk_all` (regenerated cleanly, no other
   changes). `lake build` stays green (1315 jobs).
3. Quarantining broke `lake exe checkdecls` again: 3 blueprint `\lean{}` refs
   (`Pancyclicity.GraphFamily.Gk`, `.isKConnected_four`, `.cycle_count_exact`,
   for `def:gk_construction`/`lem:gk_properties`/`thm:tightness`) pointed at
   declarations that no longer compile. Not explicitly asked for, but left
   unfixed would have regressed the blueprint deploy pipeline from the
   previous session — removed those 3 `\lean{}` lines from `content.tex` and
   `blueprint/lean_decls`, added a short remark to `def:gk_construction`
   noting the quarantine and pointing at `docs/graphfamily_options.md`. Left
   the mathematical content (statements) of all three nodes untouched, just
   unlinked. Verified `checkdecls` (zero missing), `leanblueprint pdf`,
   `leanblueprint web` all green.
4. Updated the README ledger: axiom count now **0** (bucket D retired), added
   a "Deferred" section explaining the quarantine and linking
   `docs/graphfamily_options.md`, updated the architecture diagram and the
   Theorem 1.3 bullet to flag it as currently unlinked to Lean.
5. Final repo-wide check: `grep -rn "^axiom" C4_free/` → 0 hits. 16 `sorry`s,
   matching the ledger. (The quarantined file still contains its axioms
   textually, preserved for reinstatement — Lake just never sees them.)
6. Updated `CLAUDE.md`'s Layout section and Current milestone (items 1 and 2
   now marked done, dated).

**State at end of session**: `main` pushed, `lake build` green, blueprint
pipeline green, repo has zero `axiom` declarations in the compiled tree.

## 2026-07-07 (continued) — checkdecls root cause found; blueprint deployed successfully

**Context**: continuation of the same-day session below. User provided the raw
CI log for the "Compile blueprint and documentation" failure that the
previous entry couldn't get past unauthenticated.

**Done**:
1. Raw log showed the real failure: `lake exe checkdecls blueprint/lean_decls`
   (part of `docgen-action`'s blueprint step) listed 31 `\lean{...}` targets
   in `content.tex` as missing declarations — not the pdf/Jekyll legs
   suspected earlier.
2. Diagnosed all 31: confirmed via namespace `grep` across `Foundations/*.lean`
   and `NoFourCycles.lean` that every one lives inside `namespace SimpleGraph`
   (directly or via `SimpleGraph.PlaneGraph`/`SimpleGraph.OuterplaneGraph`).
   26 were simple missing-`SimpleGraph.`-prefix fixes, plus one non-prefix
   correction (`PlaneGraph.Face` is actually `SimpleGraph.SurfaceGraph.Face`
   — `Face` lives on the more general `SurfaceGraph` that `PlaneGraph` is an
   `abbrev` over). Verified locally (`checkdecls`, `leanblueprint pdf`,
   `leanblueprint web`) before pushing. Commit `95c05e3`.
3. Remaining 5 (`OuterplaneGraph.chord`, and 4 items under
   `PlaneGraph.HamiltonianDecomp.{weight_w,sum_weight_eq,weight_wprime,
   sum_wprime_eq}`) looked like renames from actual implementation rather
   than typos, so produced a side-by-side verification table (blueprint TeX
   statement vs. candidate Lean declaration vs. semantic-gap note) instead of
   guessing — flagged a missed grep earlier (`OuterplaneGraph.IsChord` does
   exist; a word-boundary regex just didn't match inside `IsChord`) and two
   real conventions worth noting (per-side vs. joint phrasing for `w`;
   dart-indexed-with-`/2` vs. edge-indexed for `w'`).
4. Author confirmed all 5 identifications. Retargeted `\lean{}` refs
   (`content.tex` + `blueprint/lean_decls`) to `OuterplaneGraph.IsChord`,
   `OuterplaneGraph.faceWeight`, `OuterplaneGraph.sum_faceWeight_eq`,
   `PlaneGraph.edgeDartWeight`, `PlaneGraph.sum_edgeDartWeight_eq` (all under
   `SimpleGraph.`), added one remark sentence each to the `weight_wprime` and
   `cor:wprime_sum` TeX nodes about the dart/edge convention (math content
   unchanged). Verified all three locally again, all green. Commit `c829079`.
5. Pushed, watched the full run (`28867560862`) — **succeeded end-to-end for
   the first time**, ~27 minutes (first real `doc-gen4`/Jekyll build against
   Mathlib, no warm cache). Confirmed live: site root, `/blueprint/`,
   dependency graph (renders, 52 graph-node elements, not an empty shell),
   `blueprint.pdf`, `/docs/` — all HTTP 200.
6. Updated README's Blueprint section with direct links to the live home
   page, blueprint, dependency graph, PDF, and API docs (was previously an
   aspirational single link written before Pages was enabled). Commit
   `d248b62`.

**State at end of session**: `main` at `d248b62` (pushed). Blueprint deploys
successfully on every push to `main` going forward. No open CI issues.

## 2026-07-07 — CI fixes: lint driver, concurrency collision, mk_all, blueprint-compile

**Context**: following up on Task 3's finding that `blueprint.yml` had never
successfully deployed the blueprint to Pages. User merged the two open
dependabot PRs and enabled Pages (Source: GitHub Actions) between sessions.

**Done**:
1. `git pull origin main` diverged from 4 unpushed local commits (previous
   session's Tasks 2/4/5/6) vs the two PR merges on `origin/main`. Merged
   (no conflicts), verified `lake build` green, pushed as `518cc1b`.
2. Watched the resulting `blueprint.yml` run via the public Actions API — it
   was cancelled 1 second after starting. Root cause: `blueprint.yml` and
   `build-project.yml` both used the literal concurrency group
   `${{ github.ref }}`; concurrency groups aren't implicitly scoped per
   workflow, so a same-push trigger of both let one cancel the other's run.
3. Applied two fixes, one commit each:
   - `08707fe`: `blueprint.yml`'s `lean-action` step had `lint: true` with no
     lint-driver target configured in `lakefile.toml`, causing every run to
     fail at "Build and lint project" (`lake check-lint failed: could not
     find a lint driver`) before ever reaching the blueprint-compile step.
     Set `lint: false` (`build-project.yml` already runs a full `lake build`).
   - `a6ea104`: scoped concurrency groups per-workflow
     (`blueprint-${{ github.ref }}` / `build-${{ github.ref }}`). Checked
     `create-release.yml`/`update.yml` — neither has a concurrency block, so
     only these two needed the change.
4. Pushed, watched again: next failure was `lake exe mk_all --check`
   (pre-approved fix). Ran `lake exe mk_all` locally; diff was mostly
   alphabetical reordering plus one real addition, `import C4_free.Example`
   — a tracked-but-orphaned empty file from the original template, not
   scratch/untracked content, so committed as-is (`ca4039f`). `lake build`
   green (1316 jobs).
5. Pushed, watched again: **new failure**, not the pre-approved case — the
   actual "Compile blueprint and documentation" (`docgen-action`) step failed
   with exit code 255 and no further detail available via the unauthenticated
   API/log viewer. Diagnosed as far as possible without repo-admin log access:
   - All `\lean{...}` names in `blueprint/src/content.tex` resolve against
     current Lean declarations (not a stale-name issue).
   - `leanblueprint web` (the actual plasTeX build docgen-action performs)
     succeeds locally — rules out `content.tex` syntax as the cause.
   - `leanblueprint pdf` fails locally, but with a MiKTeX/Windows-specific
     LaTeX engine error unrelated to CI's Linux/texlive environment — not
     trusted as reflecting the real CI failure.
   - No `references.bib` exists anywhere in the repo; `docgen-action` defaults
     to expecting one at that path. Plausible but unconfirmed cause.
   - Stopped here per instructions (new/unapproved failure mode) — reported
     step, annotation, and diagnosis to the user; **no fix applied**.

**State at end of session**: `main` at `ca4039f` (pushed). Blueprint has never
successfully deployed to Pages; site still returns 404. Next step needs either
real log access (`gh`/token) or the user checking the Actions tab directly for
the exact error under "Compile blueprint and documentation."

**Note**: no `CLAUDE.md` exists in this repo to define this log's format: this
entry uses a plain dated/bulleted structure by default. If a specific format
is wanted, worth adding a `CLAUDE.md` convention for future sessions to follow.
