/-
Copyright (c) 2025 Abhinav Shantanam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhinav Shantanam
-/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import C4_free.Foundations.KConnected
import C4_free.Foundations.PlaneGraph

/-!
# Axiomatized External Theorems

This file contains axiomatized statements of deep results from the literature
that are used in the proofs of the main theorems but whose formalization is
beyond the scope of this project.

These are clearly marked as `axiom` and can be replaced with proofs in
future work.

## Axiomatized results

* **Tutte's theorem**: Every 4-connected planar graph is Hamiltonian.
* **Sanders' theorem**: In a 4-connected planar graph, any two edges lie
  on a common Hamiltonian cycle.
* **Whitney's theorem**: A 3-connected planar graph has a unique
  combinatorial embedding (up to orientation).

## References

* [W.T. Tutte, *A theorem on planar graphs*][tutte1956]
* [D.P. Sanders, *On paths in planar graphs*][sanders1997]
* [H. Whitney, *Congruent graphs and the connectivity of graphs*][whitney1932]
-/

-- `IsPlanar` is defined in `PlaneGraph.lean` as `Nonempty (G.PlaneGraph)`.

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace IsKConnected

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **(H)** **Tutte's Theorem** (1956): Every 4-connected planar graph is Hamiltonian.

This is assumed. A full formalization would require Tutte paths and
substantial planarity infrastructure. -/
theorem isHamiltonian_of_isPlanar (h : G.IsKConnected 4) (hp : G.IsPlanar) :
    G.IsHamiltonian := sorry

/-- **(H)** **Sanders' Theorem** (1997): If G is a 4-connected planar graph and
e₁, e₂ are edges of G, then there exists a Hamiltonian cycle in G
containing both e₁ and e₂.

This strengthens Tutte's theorem and is the key tool for Theorems 1.2 and 1.4.
Assumed. -/
theorem hamiltonianCycle_through_edges
    (h : G.IsKConnected 4) (hp : G.IsPlanar)
    (e₁ e₂ : Sym2 V) (he₁ : e₁ ∈ G.edgeSet) (he₂ : e₂ ∈ G.edgeSet) :
    ∃ (v : V) (C : G.Walk v v), C.IsHamiltonianCycle ∧
      e₁ ∈ C.edges ∧ e₂ ∈ C.edges := sorry

/-- **(H)** **Whitney's Theorem** (1932): A 3-connected planar graph has a unique
combinatorial embedding up to orientation — any two plane graph structures on
`G` differ only by a dart-permutation automorphism (i.e., a relabelling of
darts that conjugates one rotation system into the other).

This justifies working with "the" embedding of a 4-connected planar graph.
Assumed. -/
theorem unique_planar_embedding (h : G.IsKConnected 3)
    (pg1 pg2 : G.PlaneGraph) :
    ∃ e : Equiv.Perm G.Dart,
      (∀ d, (e d).fst = d.fst) ∧
      ∀ d, pg2.cmap.perm (e d) = e (pg1.cmap.perm d) := sorry

end IsKConnected

end SimpleGraph
