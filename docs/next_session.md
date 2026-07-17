Read CLAUDE.md and docs/prover_log.md's 2026-07-16 entry on
triangular_faces_diagonal_ne first.

Context: triangular_faces_diagonal_ne (NoFourCycles.lean) was found to be
FALSE as originally stated — machine-checked counterexample on K₃ (the
triangle graph's inner/outer faces share an edge with the same "opposite"
vertex, since there are only 3 vertices total). Root cause: no vertex-count
hypothesis excludes graphs too small for the two triangles' opposite corners
to be forced distinct.

Pre-authorized statement change (do this first, one commit): add
`hn : 5 ≤ Fintype.card V` to triangular_faces_diagonal_ne's signature (matching
the pattern already used by discharging_bound, enumeration_lemma, and other
sibling lemmas in the same file), and to its caller
triangular_faces_edge_disjoint (threading the hypothesis through the one call
site). Verify lake build stays green with both still `sorry`.

Then attempt the proof of triangular_faces_diagonal_ne under the corrected
statement. Constraints: no new axioms, no new sorries beyond the one already
there, search Mathlib and Foundations/CombMap before writing anything. If
stuck after 3 distinct proof strategies, stop and report: the goal state at
the sticking point, what you tried, and what missing lemma would unblock it
— then log the attempt in docs/prover_log.md. If you succeed: line-by-line
walkthrough of every tactic, per the working rules, and log the success.
