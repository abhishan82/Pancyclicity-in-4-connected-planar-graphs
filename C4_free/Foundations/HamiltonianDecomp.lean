/-
Copyright (c) 2025 Abhinav Shantanam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhinav Shantanam
-/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import C4_free.Foundations.OuterplaneGraph

/-!
# Hamiltonian Decomposition of Plane Graphs

For a plane Hamiltonian graph `G` with Hamiltonian cycle `C`, the decomposition
`(G, C, G₀, G₁)` splits `G` into two 2-connected outerplane graphs `G₀` and `G₁`
that share exactly `C`, with `C` bounding the outer face of each.

## Main definitions

* `PlaneGraph.HamiltonianDecomp`: The decomposition `(G, C, G₀, G₁)`.
* `PlaneGraph.HamiltonianDecomp.internalDualTrees`: The trees `T₀, T₁` — the
  internal duals of `G₀` and `G₁`.
* `OuterplaneGraph.faceWeight`: The weight function `w(f) = |f| - 2` (per side).
* `OuterplaneGraph.sum_faceWeight_eq`: `∑_{f ≠ outer} w(f) = n - 2` for each side.
* `PlaneGraph.edgeDartWeight`: The edge weight `w'(d)` (in `PlaneGraph.lean`).
* `PlaneGraph.sum_edgeDartWeight_eq`: `∑ w'(e) = 2(n - 2)` (in `PlaneGraph.lean`).

## References

* [A. Shantanam, *Towards Pancyclicity in 4-Connected Planar Graphs*]
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace PlaneGraph

/-- The **Hamiltonian decomposition** `(G, C, G₀, G₁)` of a plane Hamiltonian graph:

Given a Hamiltonian cycle `C` in `G`, the cycle `C` divides the plane into two
open discs. The **inner** subgraph `G₀` consists of `C` together with the edges
of `G` in one disc, and the **outer** subgraph `G₁` consists of `C` together
with the edges in the other disc. Both `G₀` and `G₁` are 2-connected outerplane
graphs with `C` bounding their outer face. We choose labels so that
`|E(G₁)| ≥ |E(G₀)|`. -/
structure HamiltonianDecomp (pg : G.PlaneGraph) where
  /-- Root vertex of the Hamiltonian cycle. -/
  root  : V
  /-- The Hamiltonian cycle `C`. -/
  cycle : G.Walk root root
  /-- `C` is a Hamiltonian cycle. -/
  isCycle : cycle.IsHamiltonianCycle
  /-- The first (smaller) outerplane subgraph `G₀`, with `C` as outer boundary. -/
  G₀    : SimpleGraph V
  /-- The second (larger) outerplane subgraph `G₁`, with `C` as outer boundary. -/
  G₁    : SimpleGraph V
  /-- `G₀` is a subgraph of `G`. -/
  sub₀  : G₀ ≤ G
  /-- `G₁` is a subgraph of `G`. -/
  sub₁  : G₁ ≤ G
  /-- Decidability of adjacency in `G₀`. -/
  inst₀ : DecidableRel G₀.Adj
  /-- Decidability of adjacency in `G₁`. -/
  inst₁ : DecidableRel G₁.Adj
  /-- Outerplane structure on `G₀` with `C` bounding its outer face. -/
  op₀   : @OuterplaneGraph V _ _ G₀ inst₀
  /-- Outerplane structure on `G₁` with `C` bounding its outer face. -/
  op₁   : @OuterplaneGraph V _ _ G₁ inst₁
  /-- `G₀` and `G₁` together cover all edges of `G`. -/
  edgeUnion : G₀.edgeSet ∪ G₁.edgeSet = G.edgeSet
  /-- `G₀` and `G₁` share exactly the edges of `C`. -/
  edgeInter : G₀.edgeSet ∩ G₁.edgeSet = {e | e ∈ cycle.edges}
  /-- `G₁` has at least as many edges as `G₀`. -/
  edgeOrd   : Set.ncard G₀.edgeSet ≤ Set.ncard G₁.edgeSet

namespace HamiltonianDecomp

/-- **Face count data** for a Hamiltonian decomposition `(G, C, G₀, G₁)`.
For threshold `j ∈ {5, 6}`, records:
* `f₀_ge`, `f₁_ge`: number of non-outer faces of `Gᵢ` with size ≥ j
* `f_ge`: total such faces over `G`
* `s₀_gt`, `s₁_gt`, `s_gt`: excess-size sums `∑_{F: |F|>j} (|F| - j)` -/
structure FaceCounts (j : ℕ) where
  /-- #{F ∈ F(G₀) \ {outer₀} | |F| ≥ j} -/
  f₀_ge : ℕ
  /-- #{F ∈ F(G₁) \ {outer₁} | |F| ≥ j} -/
  f₁_ge : ℕ
  /-- #{F ∈ F(G) | |F| ≥ j} -/
  f_ge  : ℕ
  /-- ∑_{F ∈ F(G₀)\{outer₀}: |F|>j} (|F| - j) -/
  s₀_gt : ℤ
  /-- ∑_{F ∈ F(G₁)\{outer₁}: |F|>j} (|F| - j) -/
  s₁_gt : ℤ
  /-- ∑_{F ∈ F(G): |F|>j} (|F| - j) -/
  s_gt  : ℤ

variable {pg : G.PlaneGraph} (D : PlaneGraph.HamiltonianDecomp pg)

/-- The **internal dual trees**: `T₀` and `T₁` are the internal duals of
`G₀` and `G₁` respectively. Together, `V(T₀) ∪ V(T₁) = V(G*)` (all
non-outer-face vertices of the dual). -/
noncomputable def internalDualTrees :=
  letI := D.inst₀
  letI := D.inst₁
  (D.op₀.internalDual, D.op₁.internalDual)

end HamiltonianDecomp

end PlaneGraph

end SimpleGraph
