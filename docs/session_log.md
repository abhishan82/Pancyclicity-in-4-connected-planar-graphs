# Session Log

Dated summaries of agent work sessions on this repo. Newest entries at the top.

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
