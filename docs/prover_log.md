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
2026-07-16 | `triangular_faces_diagonal_ne` | Claude Sonnet 5 | **disproved** (machine-checked counterexample, not just stuck) | Built K₃ (complete graph on `Fin 3`) as an explicit `PlaneGraph`: rotation system = swap the 2 darts at each vertex; its only two faces (inner/outer triangle of the unique embedding) are both triangular and share all 3 edges. Instantiating the lemma's exact hypothesis types with witnesses from this model (`d₁''=d20, d₁=d01, d₂=d10, e₂=d02, e₃=d21`, `f₁,f₂` = the two face-cycles) satisfies every hypothesis (`hf₁_mem, hf₂_mem, hd₁''_in, he₂_in, he₃_in, hf₁_period, hf₂_period, hv_f1_31, hv_f2_23, hv_f2_31`) while the conclusion `d₁''.fst ≠ e₂.snd` is false (both sides `= 2`) — verified as one `decide`d conjunction, `#print axioms` shows zero `sorryAx` (only `propext, Classical.choice, Quot.sound`). Root cause: the lemma has no vertex-count/connectivity hypothesis excluding the degenerate case where a triangle's two faces (front and back) glue along an edge with the same "opposite" vertex — happens whenever the graph is too small (here, `n=3`) for the two opposite corners to be forced distinct. Sibling lemmas in the same file (`discharging_bound`, `enumeration_lemma`, etc.) all carry `hn : 5 ≤ Fintype.card V`; this lemma and its caller `triangular_faces_edge_disjoint` currently have no such hypothesis. Missing-lemma diagnosis: likely needs `5 ≤ Fintype.card V` (or equivalent) added to both `triangular_faces_diagonal_ne` and `triangular_faces_edge_disjoint`'s signatures — a statement change, out of scope for this session's no-statement-change constraint. Scratch verification file was not committed (deleted after use, per the no-scratch-files rule).
