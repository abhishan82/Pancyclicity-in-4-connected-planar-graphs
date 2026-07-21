Read CLAUDE.md and docs/prover_log.md's 2026-07-16 and 2026-07-21 entries on
triangular_faces_diagonal_ne first.

Context: triangular_faces_diagonal_ne (NoFourCycles.lean) was found FALSE as
originally stated (K₃ counterexample, no vertex-count hypothesis). That's
fixed: `hn : 5 ≤ Fintype.card V` has been added to it and threaded through
its only caller (triangular_faces_edge_disjoint) from the one place both
are used (edge_bound_no_four_cycles, which already had `hn` in scope but
never passed it down). lake build is green with the corrected statement,
still `sorry`.

Target: prove triangular_faces_diagonal_ne under the corrected statement
(now with `hn` available as a hypothesis, on top of the original 10).
Constraints: no new axioms, no new sorries, statement unchanged from what's
now in NoFourCycles.lean (do not further modify the signature without
stopping to ask). Search Mathlib and our Foundations/CombMap for usable
lemmas before writing anything.

Open question this proof attempt needs to resolve: is `n ≥ 5` actually
*sufficient* to close the argument (not just to rule out the n=3
counterexample)? If you find the hypotheses are still not enough (e.g. a
different small-n degenerate case survives `n ≥ 5`), that itself is a
valid, useful outcome — report it the same way as being stuck.

If stuck after 3 distinct proof strategies, stop and give me: the goal
state at the sticking point, what you tried, and what missing lemma (or
missing hypothesis) would unblock it — then log the attempt in
docs/prover_log.md. If you succeed: line-by-line walkthrough of every
tactic, per the working rules, and log the success.
