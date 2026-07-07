# Prover Log

Benchmark data on prover attempts against this project's research-level graph
theory lemmas: which lemmas got attempted, by what model/tool, and whether
they closed. Failures are as valuable as successes here — a stuck attempt
records that a goal is harder than it looked, which is useful signal for
whoever (human or model) picks it up next.

**Append-only.** Never edit or delete a past entry, including to "clean up" a
retroactive one — if a later attempt supersedes it, add a new line, don't
rewrite history.

**Format**: one line per attempt —

```
date | lemma | model/tool | outcome | notes
```

## Log

2026-07-05 | `triangular_faces_diagonal_ne` (then an anonymous inline goal in `triangular_faces_edge_disjoint`) | Claude Code (session details unknown) | stuck, sorried | Retroactive entry. Date is when the code first entered git history (commit b05dd6f); the actual attempt happened in an earlier, uncommitted session. Explored several routes via `pg.cmap.rotation_cyclic`/`Equiv.Perm.SameCycle` without closing the goal `d₁''.fst ≠ e₂.snd`, left as `sorry` with exploratory comments. Goal extracted to the named lemma `triangular_faces_diagonal_ne` 2026-07-05 (Task 5 cleanup, commit 4a81642); still unproved as of extraction.
