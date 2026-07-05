/-
Copyright (c) 2025 Abhinav Shantanam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhinav Shantanam
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Set.Card
import C4_free.Foundations.PlaneGraph
import C4_free.Foundations.KConnected

/-!
# Outerplanar and Outerplane Graphs

This file defines outerplanar graphs and their combinatorial structure.

## Main definitions

* `SimpleGraph.IsOuterplanar G`: `G` has a planar embedding with all vertices
  on the outer face boundary.
* `SimpleGraph.OuterplaneGraph G`: A plane graph with a designated outer face
  whose boundary contains every vertex of `G`.
* `OuterplaneGraph.IsChord`: An edge not on the outer face boundary.
* `OuterplaneGraph.chords`: The finset of all chords.
* `OuterplaneGraph.internalDual`: The internal dual (dual minus the outer face vertex).

## Main results

* `OuterplaneGraph.internalDual_isTree`: The internal dual of a 2-connected
  outerplane graph is a tree. (Axiomatized.)

## References

* [B. Mohar, *Face covers and the genus of a graph*][mohar1994]
* [A. Shantanam, *Towards Pancyclicity in 4-Connected Planar Graphs*]
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A graph is **outerplanar** if it admits a plane graph structure in which
every vertex lies on the boundary of some designated outer face. -/
def IsOuterplanar (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ (pg : G.PlaneGraph) (outer : pg.Face),
    ∀ v : V, ∃ d : G.Dart, d.fst = v ∧ d ∈ outer.val.support

/-- An **outerplane graph**: a simple graph `G` with a fixed plane embedding
(`PlaneGraph`) and a designated outer face `outer` such that every vertex of
`G` has at least one incident dart on the boundary of `outer`. -/
structure OuterplaneGraph (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- The underlying plane graph structure. -/
  pg    : G.PlaneGraph
  /-- The designated outer (infinite) face. -/
  outer : pg.Face
  /-- Every vertex of `G` has an incident dart on the outer face boundary. -/
  allOnBoundary : ∀ v : V, ∃ d : G.Dart, d.fst = v ∧ d ∈ outer.val.support
  /-- No edge appears in both directions on the outer boundary: if dart `d`
  is on the outer face, its reverse `d.symm` is not.  This ensures the outer
  boundary is a simple cycle — a necessary condition for a proper embedding. -/
  simple_boundary : ∀ d : G.Dart, d ∈ outer.val.support → d.symm ∉ outer.val.support
  /-- The outer boundary visits each vertex at most once as a **source**:
  no two distinct darts on the outer face have the same first vertex.
  Equivalently, the map `d ↦ d.fst` is injective on `outer.val.support`.
  This holds for any proper outerplanar embedding: the outer face traces a
  Hamiltonian cycle, which is simple. -/
  boundary_injective : ∀ d₁ d₂ : G.Dart,
      d₁ ∈ outer.val.support → d₂ ∈ outer.val.support → d₁.fst = d₂.fst → d₁ = d₂

namespace OuterplaneGraph

variable (opg : OuterplaneGraph G)

/-- The **boundary edges**: the set of undirected edges `{u, v}` such that the
dart `u → v` lies on the outer face boundary. -/
noncomputable def boundaryEdgeFinset : Finset (Sym2 V) :=
  opg.outer.val.support.image fun d => s(d.fst, d.snd)

/-- An edge `e` is a **chord** of `opg` if it is an edge of `G` but is NOT on
the outer face boundary. -/
def IsChord (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ e ∉ opg.boundaryEdgeFinset

/-- The finset of all chords of `opg`. -/
noncomputable def chords : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => e ∉ opg.boundaryEdgeFinset

/-- The number of chords. -/
noncomputable def chordCount : ℕ := opg.chords.card

/-- The **internal dual** of the outerplane graph: the dual graph `G*` with
the vertex corresponding to the outer face deleted. -/
noncomputable def internalDual : SimpleGraph {f : opg.pg.Face // f ≠ opg.outer} :=
  opg.pg.internalDual opg.outer

/-- **Weight function `w`** (blueprint: `PlaneGraph.HamiltonianDecomp.weight_w`):
For each non-outer face `f`, `w(f) = |f| - 2` where `|f|` is the number of
darts (= edges) on the boundary of `f`. -/
noncomputable def faceWeight (f : {f : opg.pg.Face // f ≠ opg.outer}) : ℤ :=
  (f.val.val.support.card : ℤ) - 2

/-- Every boundary edge is an actual edge of `G`:
the darts on the outer face all correspond to edges of `G`. -/
theorem boundaryEdgeFinset_subset_edgeFinset :
    opg.boundaryEdgeFinset ⊆ G.edgeFinset := by
  intro e he
  simp only [boundaryEdgeFinset, Finset.mem_image] at he
  obtain ⟨d, _hd, rfl⟩ := he
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact d.adj

/-- The edge set decomposes as chords plus boundary edges:
`|E(G)| = chordCount + |boundaryEdgeFinset|`. -/
theorem edgeFinset_card_eq :
    G.edgeFinset.card = opg.chordCount + opg.boundaryEdgeFinset.card := by
  have h_sub := opg.boundaryEdgeFinset_subset_edgeFinset
  have h_eq : opg.chords = G.edgeFinset \ opg.boundaryEdgeFinset := by
    ext e; simp [chords, Finset.mem_filter, Finset.mem_sdiff]
  rw [chordCount, h_eq]
  linarith [Finset.card_sdiff_add_card_eq_card h_sub]

/-- The outer face has **at least** `Fintype.card V` darts:
`allOnBoundary` supplies, for each vertex `v`, a dart `d` with `d.fst = v`
inside the outer face support. Since darts at distinct vertices are distinct
(their sources differ), this gives an injection `V ↪ outer.val.support`. -/
theorem outer_face_card_ge :
    Fintype.card V ≤ opg.outer.val.support.card := by
  rw [← Finset.card_univ]
  apply Finset.card_le_card_of_injOn (fun v => (opg.allOnBoundary v).choose)
  · intro v _
    exact (opg.allOnBoundary v).choose_spec.2
  · intro v₁ _ v₂ _ h
    have h1 := (opg.allOnBoundary v₁).choose_spec.1
    have h2 := (opg.allOnBoundary v₂).choose_spec.1
    have key : ((opg.allOnBoundary v₁).choose).fst =
               ((opg.allOnBoundary v₂).choose).fst :=
      congrArg (fun d : G.Dart => d.fst) h
    rw [h1, h2] at key
    exact key

/-- **Outer face size**: For a 2-connected outerplane graph, the outer face has
exactly `n` darts — one per vertex, each visited exactly once as a source.

**Proof**: Antisymmetry of `≤`.
- Lower bound `n ≤ |outer.support|`: `outer_face_card_ge` (injection `v ↦ d_v`).
- Upper bound `|outer.support| ≤ n`: `boundary_injective` says `d ↦ d.fst` is
  injective on `outer.support`, giving an injection into `V` (size `n`). -/
theorem outer_face_size_eq_card :
    opg.outer.val.support.card = Fintype.card V := by
  apply le_antisymm
  · -- d ↦ d.fst is injective on outer.support → |outer.support| ≤ n
    rw [← Finset.card_univ]
    apply Finset.card_le_card_of_injOn (fun d => d.fst)
    · intro d hd; exact Finset.mem_univ _
    · intro d₁ hd₁ d₂ hd₂ h; exact opg.boundary_injective d₁ d₂ hd₁ hd₂ h
  · exact opg.outer_face_card_ge

/-- The boundary edge finset has exactly `|V|` edges for a 2-connected outerplane graph.
The map `d ↦ s(d.fst, d.snd)` is injective on `outer.val.support`:
if two darts map to the same unordered pair, either they are equal
or one is the reverse of the other; the latter is excluded by `simple_boundary`. -/
theorem boundaryEdgeFinset_card_eq :
    opg.boundaryEdgeFinset.card = Fintype.card V := by
  have h_size := opg.outer_face_size_eq_card
  rw [boundaryEdgeFinset, ← h_size]
  apply Finset.card_image_of_injOn
  intro d₁ hd₁ d₂ hd₂ heq
  simp only [Finset.mem_coe] at hd₁ hd₂
  simp only [Sym2.eq_iff] at heq
  rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- d₁.fst = d₂.fst and d₁.snd = d₂.snd → d₁ = d₂
    ext
    · exact h1
    · exact h2
  · -- d₁.fst = d₂.snd and d₁.snd = d₂.fst → d₂ = d₁.symm, contradicting simple_boundary
    exfalso
    have hd₂_eq : d₂ = d₁.symm := by
      ext
      · exact h2.symm
      · exact h1.symm
    rw [hd₂_eq] at hd₂
    exact opg.simple_boundary d₁ hd₁ hd₂

/-- **Sum of weights**: For a 2-connected outerplane graph,
`∑_{f ≠ outer} (|f| - 2) = n - 2`.

**Proof sketch**: By the dart-face incidence equation,
`∑_{all f} |f| = |Dart| = 2|E|`.
Subtracting `2 * F` and applying Euler (`V - E + F = 2`) gives `∑_f (|f|-2) = 2n-4`.
Isolating the outer face (size `n` by `outer_face_size_eq_card`) leaves `n-2`. -/
theorem sum_faceWeight_eq :
    (opg.pg.faceFinset.filter fun σ => σ ≠ opg.outer.val).sum
      (fun σ => (σ.support.card : ℤ) - 2) =
      (Fintype.card V : ℤ) - 2 := by
  -- (1) ∑_f |f| = 2|E|  (dart-face incidence)
  have h_dart_sum : opg.pg.faceFinset.sum (fun σ => (σ.support.card : ℤ)) =
      2 * G.edgeFinset.card := by
    have h1 := opg.pg.cmap.sum_support_card_cycleFactorsFinset
    have h2 := G.dart_card_eq_twice_card_edges
    exact_mod_cast h1.trans h2
  -- (2) ∑_f (|f| - 2) = 2n - 4  (step-by-step via Euler: n - E + F = 2)
  have h_full : opg.pg.faceFinset.sum (fun σ => (σ.support.card : ℤ) - 2) =
      2 * Fintype.card V - 4 := by
    -- ∑(f-2) = ∑f - ∑2
    have hstep1 : opg.pg.faceFinset.sum (fun σ => (σ.support.card : ℤ) - 2) =
        opg.pg.faceFinset.sum (fun σ => (σ.support.card : ℤ)) -
        opg.pg.faceFinset.sum (fun σ => (2 : ℤ)) := by
      simp only [Finset.sum_sub_distrib]
    -- ∑2 = 2 * |fF|
    have hstep2 : opg.pg.faceFinset.sum (fun σ => (2 : ℤ)) =
        2 * opg.pg.faceFinset.card := by
      rw [Finset.sum_const]; ring
    -- |fF| = faceCount (ℕ); cast to ℤ
    have hstep3 : (opg.pg.faceFinset.card : ℤ) = opg.pg.cmap.faceCount :=
      by exact_mod_cast opg.pg.card_faceFinset_eq
    -- Combine then use Euler
    have h_euler := opg.pg.euler_formula
    rw [hstep1, h_dart_sum, hstep2, hstep3]
    omega
  -- (3) |outer| = n
  have h_outer : (opg.outer.val.support.card : ℤ) = Fintype.card V :=
    by exact_mod_cast opg.outer_face_size_eq_card
  -- (4) Split off outer face via sum_filter_add_sum_filter_not
  have hmem : opg.outer.val ∈ opg.pg.faceFinset := opg.outer.2
  have h_sum_split :=
    Finset.sum_filter_add_sum_filter_not opg.pg.faceFinset
      (fun σ => σ ≠ opg.outer.val) (fun σ => (σ.support.card : ℤ) - 2)
  -- The complementary filter (σ = outer) sums to f(outer)
  have h_singleton : (opg.pg.faceFinset.filter fun σ => ¬σ ≠ opg.outer.val).sum
      (fun σ => (σ.support.card : ℤ) - 2) =
      (opg.outer.val.support.card : ℤ) - 2 := by
    have h_eq : opg.pg.faceFinset.filter (fun σ => ¬σ ≠ opg.outer.val) = {opg.outer.val} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, not_ne_iff]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro rfl; exact ⟨hmem, rfl⟩
    rw [h_eq, Finset.sum_singleton]
  -- Re-state h_sum_split with σ to match the goal's lambda variable, then substitute
  have h_split_σ : (opg.pg.faceFinset.filter fun σ => σ ≠ opg.outer.val).sum
      (fun σ => (σ.support.card : ℤ) - 2) +
      (opg.pg.faceFinset.filter fun σ => ¬σ ≠ opg.outer.val).sum
      (fun σ => (σ.support.card : ℤ) - 2) =
      opg.pg.faceFinset.sum (fun σ => (σ.support.card : ℤ) - 2) := h_sum_split
  rw [h_singleton, h_full, h_outer] at h_split_σ
  -- h_split_σ now: A + (V - 2) = 2V - 4; goal: A = V - 2
  omega

/-- **(P)** **Internal dual is a tree** (Mohar): The internal dual of a 2-connected
outerplane graph is a tree.

Assumed — the proof proceeds by induction on the number of chords,
using the fact that removing a chord splits the internal dual along a leaf. -/
theorem internalDual_isTree (hconn : G.IsKConnected 2) : opg.internalDual.IsTree := sorry

end OuterplaneGraph

end SimpleGraph
