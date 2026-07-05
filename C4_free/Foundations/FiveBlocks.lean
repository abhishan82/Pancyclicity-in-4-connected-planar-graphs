/-
Copyright (c) 2025 Abhinav Shantanam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhinav Shantanam
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import C4_free.Foundations.PlaneGraph

/-!
# 5-Block Structures in Plane Graphs

This file defines the 5-fan, 5-block, 5-flower, and 5-tree structures used in
the discharging argument for 4-connected planar graphs without 4-cycles.

## Main definitions

* `PlaneGraph.FiveFan`: A maximal set of consecutive 5-faces around a vertex.
* `PlaneGraph.FiveBlock`: A maximal connected set of 5-faces under dual adjacency.
* `PlaneGraph.FiveFlower`: A 5-block of exactly 6 members whose dual is K_{1,5}.
* `PlaneGraph.FiveTree`: An acyclic 5-block with constrained dual degrees.
* `PlaneGraph.FiveTree.member_count`: A 5-tree with p degree-5 dual vertices
  has 5p+1 members.

## References

* [A. Shantanam, *Towards Pancyclicity in 4-Connected Planar Graphs*]
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace PlaneGraph

variable (pg : G.PlaneGraph)

/-- A **5-fan** incident with vertex `center` in plane graph `pg`:
a maximal set of 5-faces each incident with `center` such that in the cyclic
order of faces around `center`, all faces in the fan appear consecutively. -/
structure FiveFan where
  /-- The center vertex of the fan. -/
  center : V
  /-- The set of faces in the fan. -/
  faces : Finset pg.Face
  /-- The fan is nonempty. -/
  nonempty : faces.Nonempty
  /-- All faces have size 5 (exactly 5 boundary darts). -/
  all_five : ∀ f ∈ faces, f.val.support.card = 5
  /-- All faces are incident with the center vertex. -/
  all_incident : ∀ f ∈ faces, ∃ d : G.Dart, d.fst = center ∧ d ∈ f.val.support

/-- A **5-block** in plane graph `pg`: a maximal connected set of 5-faces,
where connectivity is measured in the dual graph `G*`. A 5-block is **trivial**
if it has exactly one member. -/
structure FiveBlock where
  /-- The set of faces forming the 5-block. -/
  faces : Finset pg.Face
  /-- The block is nonempty. -/
  nonempty : faces.Nonempty
  /-- All faces have size 5. -/
  all_five : ∀ f ∈ faces, f.val.support.card = 5
  /-- The induced dual subgraph on `faces` is connected. -/
  dual_connected : (pg.dual.induce (faces : Set pg.Face)).Connected

/-- A **5-flower** is a 5-block of exactly 6 members `{P₀, P₁, ..., P₅}` where
`P₀` (the center) shares an edge with each of `P₁, ..., P₅`, and the non-center
members are pairwise edge-disjoint. Equivalently, the restricted dual is K_{1,5}. -/
structure FiveFlower extends FiveBlock pg where
  /-- Exactly 6 members. -/
  card_eq : faces.card = 6
  /-- The center face P₀. -/
  center : pg.Face
  /-- The center belongs to the faces. -/
  center_mem : center ∈ faces
  /-- The center is adjacent in the dual to every other member. -/
  center_adj_all : ∀ f ∈ faces, f ≠ center →
    pg.dual.Adj center f
  /-- Non-center members are pairwise non-adjacent in the dual. -/
  non_center_indep : ∀ f₁ ∈ faces, ∀ f₂ ∈ faces,
    f₁ ≠ center → f₂ ≠ center → f₁ ≠ f₂ → ¬ pg.dual.Adj f₁ f₂

/-- The **dual-degree** of a face `f` within a set `s` of faces:
the number of faces in `s` adjacent to `f` in the dual graph. -/
noncomputable def dualDegreeIn (pg : G.PlaneGraph) (s : Finset pg.Face) (f : pg.Face) : ℕ :=
  haveI : DecidablePred (pg.dual.Adj f) := Classical.decPred _
  (s.filter (pg.dual.Adj f)).card

/-- A **5-tree** is an acyclic 5-block such that each vertex in the induced
dual subgraph has degree in `{0, 1, 2, 5}`. Each of the three nontrivial
degree classes `{1}`, `{2}`, `{5}` forms an independent set in the induced
dual, and no degree-1 vertex is adjacent to a degree-2 vertex. Every trivial
5-block and every 5-flower is a 5-tree. -/
structure FiveTree extends FiveBlock pg where
  /-- The dual restricted to the 5-tree is acyclic. -/
  dual_acyclic : (pg.dual.induce (faces : Set pg.Face)).IsAcyclic
  /-- Each vertex has degree 0, 1, 2, or 5 in the induced dual. -/
  degree_constraint : ∀ f ∈ faces,
    dualDegreeIn pg faces f ∈ ({0, 1, 2, 5} : Finset ℕ)
  /-- Degree-1 vertices form an independent set in the induced dual. -/
  no_one_one_adj : ∀ f₁ ∈ faces, ∀ f₂ ∈ faces,
    dualDegreeIn pg faces f₁ = 1 → dualDegreeIn pg faces f₂ = 1 → f₁ ≠ f₂ →
    ¬ pg.dual.Adj f₁ f₂
  /-- Degree-2 vertices form an independent set in the induced dual. -/
  no_two_two_adj : ∀ f₁ ∈ faces, ∀ f₂ ∈ faces,
    dualDegreeIn pg faces f₁ = 2 → dualDegreeIn pg faces f₂ = 2 → f₁ ≠ f₂ →
    ¬ pg.dual.Adj f₁ f₂
  /-- Degree-5 vertices form an independent set in the induced dual. -/
  no_five_five_adj : ∀ f₁ ∈ faces, ∀ f₂ ∈ faces,
    dualDegreeIn pg faces f₁ = 5 → dualDegreeIn pg faces f₂ = 5 → f₁ ≠ f₂ →
    ¬ pg.dual.Adj f₁ f₂
  /-- No degree-1 vertex is adjacent to a degree-2 vertex in the induced dual. -/
  no_one_two_adj : ∀ f₁ ∈ faces, ∀ f₂ ∈ faces,
    dualDegreeIn pg faces f₁ = 1 → dualDegreeIn pg faces f₂ = 2 →
    ¬ pg.dual.Adj f₁ f₂

namespace FiveTree

variable (ft : PlaneGraph.FiveTree pg)

/-- **5-tree member count** (blueprint: `PlaneGraph.FiveTree.member_count`):
A 5-tree whose induced dual subgraph has `p ≥ 0` vertices of degree 5 has
exactly `5p + 1` members.

In particular, every 5-tree has at least 1 member.

**Proof sketch**: Let T = pg.dual restricted to ft.faces.
1. T is a tree (dual_connected + dual_acyclic), so |E(T)| = ft.faces.card - 1.
2. Every edge of T has exactly one deg-5 endpoint:
   - At least one deg-5 endpoint: if both have degree ≤ 2, the independence
     constraints (no_one_one_adj, no_two_two_adj, no_one_two_adj) forbid the edge.
   - At most one deg-5 endpoint: no_five_five_adj.
3. Each deg-5 vertex contributes exactly 5 edges (its degree), and by (2) these
   incidence sets partition E(T). So |E(T)| = 5 * p.
4. From (1) and (3): ft.faces.card = 5p + 1. -/
theorem member_count :
    ∃ p : ℕ,
      Set.ncard {f ∈ (ft.faces : Set pg.Face) | dualDegreeIn pg ft.faces f = 5} = p ∧
      ft.faces.card = 5 * p + 1 := by
  -- Set up abbreviations and instances
  let T := pg.dual.induce (ft.faces : Set pg.Face)
  haveI hVfin   : Fintype (ft.faces : Set pg.Face)      := inferInstance
  haveI hdecT   : DecidableRel T.Adj                    := fun _ _ => Classical.propDecidable _
  haveI hEfin   : Fintype T.edgeSet                     := inferInstance
  haveI hDecEq  : DecidableEq ↥(ft.faces : Set pg.Face) := Classical.decEq _
  haveI hDecSym : DecidableEq (Sym2 ↥(ft.faces : Set pg.Face)) := inferInstance
  -- T is a tree; |E(T)| + 1 = ft.faces.card
  have hTree  : T.IsTree := ⟨ft.dual_connected, ft.dual_acyclic⟩
  have hEcard : T.edgeFinset.card + 1 = ft.faces.card :=
    hTree.card_edgeFinset.trans (Fintype.card_coe ft.faces)
  -- dualDegreeIn is the filter card (the haveI inside the def is a local instance)
  have hDDI : ∀ f : pg.Face,
      dualDegreeIn pg ft.faces f = (ft.faces.filter (pg.dual.Adj f)).card := fun _ => by
    simp [dualDegreeIn]
  -- deg5Sub: subtype-Finset of vertices of T with dual-degree 5
  haveI hDec5 : DecidablePred (fun f : ↥(ft.faces : Set pg.Face) =>
      dualDegreeIn pg ft.faces f.val = 5) := Classical.decPred _
  let deg5Sub : Finset ↥(ft.faces : Set pg.Face) :=
    Finset.univ.filter (fun f => dualDegreeIn pg ft.faces f.val = 5)
  -- Connect Set.ncard (in the statement) to deg5Sub.card
  have hpCard :
      Set.ncard {f ∈ (ft.faces : Set pg.Face) | dualDegreeIn pg ft.faces f = 5}
        = deg5Sub.card := by
    haveI : DecidablePred (fun f : pg.Face => dualDegreeIn pg ft.faces f = 5) :=
      Classical.decPred _
    have hsetEq : {f ∈ (ft.faces : Set pg.Face) | dualDegreeIn pg ft.faces f = 5} =
        ↑(ft.faces.filter (fun f => dualDegreeIn pg ft.faces f = 5)) := by
      ext; simp [Set.mem_sep_iff, Finset.mem_coe, Finset.mem_filter]
    rw [hsetEq, Set.ncard_coe_finset]
    apply Finset.card_bij (fun f hf => ⟨f, (Finset.mem_filter.mp hf).1⟩)
    · intro f hf
      simp only [deg5Sub, Finset.mem_univ, Finset.mem_filter, true_and]
      exact (Finset.mem_filter.mp hf).2
    · intro a _ b _ hab; exact congr_arg Subtype.val hab
    · intro b hb
      simp only [deg5Sub, Finset.mem_univ, Finset.mem_filter, true_and] at hb
      exact ⟨b.val, Finset.mem_filter.mpr ⟨b.property, hb⟩, rfl⟩
  -- Bridge: T.degree v = dualDegreeIn pg ft.faces v.val
  have hBridge : ∀ v : ↥(ft.faces : Set pg.Face),
      T.degree v = dualDegreeIn pg ft.faces v.val := by
    intro v
    rw [hDDI, ← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun w _ => w.val)
    · intro w hw
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj] at hw
      exact Finset.mem_filter.mpr ⟨w.property, hw⟩
    · intro a _ b _ h; exact Subtype.ext h
    · intro g hg
      obtain ⟨hgmem, hgadj⟩ := Finset.mem_filter.mp hg
      exact ⟨⟨g, hgmem⟩,
        by simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]; exact hgadj,
        rfl⟩
  -- Each deg-5 vertex contributes exactly 5 edges to T
  have hInc5 : ∀ v ∈ deg5Sub, (T.incidenceFinset v).card = 5 := by
    intro v hv
    rw [SimpleGraph.card_incidenceFinset_eq_degree, hBridge]
    simp only [deg5Sub, Finset.mem_univ, Finset.mem_filter, true_and] at hv
    exact hv
  -- Every edge of T has at least one deg-5 endpoint
  have hCover : T.edgeFinset ⊆ deg5Sub.biUnion (T.incidenceFinset ·) := by
    intro e he
    simp only [Finset.mem_biUnion]
    -- Decompose e = s(a, b) with T.Adj a b
    induction e using Sym2.ind with | h a b => ?_
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    -- he : T.Adj a b, so pg.dual.Adj a.val b.val and both a,b ∈ ft.faces
    have ha_deg := ft.degree_constraint a.val a.property
    have hb_deg := ft.degree_constraint b.val b.property
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha_deg hb_deg
    -- Neither endpoint has degree 0 (both are adjacent to something)
    have ha_pos : 0 < dualDegreeIn pg ft.faces a.val := by
      rw [← hBridge]
      exact Finset.card_pos.mpr ⟨b, by
        simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]; exact he⟩
    have hb_pos : 0 < dualDegreeIn pg ft.faces b.val := by
      rw [← hBridge]
      exact Finset.card_pos.mpr ⟨a, by
        simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]; exact he.symm⟩
    -- If a has degree 5, witness with a; if b has degree 5, witness with b
    -- Otherwise both ∈ {1,2}, which all independence constraints forbid
    by_cases ha5 : dualDegreeIn pg ft.faces a.val = 5
    · refine ⟨a, by simp [deg5Sub, Finset.mem_filter, ha5], ?_⟩
      simp only [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet,
                 Set.mem_sep_iff, SimpleGraph.mem_edgeSet]
      exact ⟨he, Sym2.mem_mk_left a b⟩
    · by_cases hb5 : dualDegreeIn pg ft.faces b.val = 5
      · refine ⟨b, by simp [deg5Sub, Finset.mem_filter, hb5], ?_⟩
        simp only [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet,
                   Set.mem_sep_iff, SimpleGraph.mem_edgeSet]
        exact ⟨he, Sym2.mem_mk_right a b⟩
      · -- Both endpoints in {1, 2}; all combos forbidden by independence constraints
        have hadj : pg.dual.Adj a.val b.val := SimpleGraph.induce_adj.mp he
        have ha12 : dualDegreeIn pg ft.faces a.val = 1 ∨
                    dualDegreeIn pg ft.faces a.val = 2 := by
          rcases ha_deg with h | h | h | h <;> omega
        have hb12 : dualDegreeIn pg ft.faces b.val = 1 ∨
                    dualDegreeIn pg ft.faces b.val = 2 := by
          rcases hb_deg with h | h | h | h <;> omega
        have hne : a.val ≠ b.val := fun h => he.ne (Subtype.ext h)
        rcases ha12, hb12 with ⟨ha1 | ha2, hb1 | hb2⟩
        · exact absurd hadj
            (ft.no_one_one_adj a.val a.property b.val b.property ha1 hb1 hne)
        · exact absurd hadj
            (ft.no_one_two_adj a.val a.property b.val b.property ha1 hb2)
        · exact absurd hadj.symm
            (ft.no_one_two_adj b.val b.property a.val a.property hb1 ha2)
        · exact absurd hadj
            (ft.no_two_two_adj a.val a.property b.val b.property ha2 hb2 hne)
  -- Incidence sets of distinct deg-5 vertices are disjoint (no_five_five_adj)
  have hDisj : (deg5Sub : Set ↥(ft.faces : Set pg.Face)).PairwiseDisjoint
      (T.incidenceFinset ·) := by
    intro v hv w hw hvw
    simp only [Function.onFun, Finset.disjoint_left]
    intro e hev hew
    -- Decompose e = s(a, b), then unpack incidenceFinset membership
    induction e using Sym2.ind with | h a b => ?_
    -- hev : s(a,b) ∈ T.incidenceFinset v; unpack to T.Adj a b ∧ v ∈ s(a,b)
    simp only [SimpleGraph.mem_incidenceFinset, Set.mem_toFinset, SimpleGraph.incidenceSet,
               Set.mem_sep_iff, SimpleGraph.mem_edgeSet] at hev hew
    -- hev : T.Adj a b ∧ v ∈ s(a,b)   hew : T.Adj a b ∧ w ∈ s(a,b)
    have hve : v = a ∨ v = b := Sym2.mem_iff.mp hev.2
    have hwe : w = a ∨ w = b := Sym2.mem_iff.mp hew.2
    have hne : v ≠ w := hvw
    have he_edge : T.Adj a b := hev.1
    -- Case split: recover T.Adj v w, then apply no_five_five_adj
    have hadj : pg.dual.Adj v.val w.val := by
      rcases hve with rfl | rfl <;> rcases hwe with rfl | rfl
      · exact absurd rfl hne
      · exact SimpleGraph.induce_adj.mp he_edge
      · exact (SimpleGraph.induce_adj.mp he_edge).symm
      · exact absurd rfl hne
    have hv5 : dualDegreeIn pg ft.faces v.val = 5 :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
    have hw5 : dualDegreeIn pg ft.faces w.val = 5 :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
    exact absurd hadj
      (ft.no_five_five_adj v.val v.property w.val w.property hv5 hw5
        (fun h => hne (Subtype.ext h)))
  -- Combine: |E(T)| = 5 * deg5Sub.card
  have hEcount : T.edgeFinset.card = 5 * deg5Sub.card := by
    have hBU : T.edgeFinset = deg5Sub.biUnion (T.incidenceFinset ·) :=
      Finset.Subset.antisymm hCover
        (Finset.biUnion_subset.mpr (fun v _ =>
          @SimpleGraph.incidenceFinset_subset _ T v (T.neighborSetFintype v) _ _))
    rw [hBU, Finset.card_biUnion hDisj, Finset.sum_const_nat (fun v hv => hInc5 v hv)]
    ring
  exact ⟨deg5Sub.card, hpCard, by omega⟩

end FiveTree

end PlaneGraph

end SimpleGraph
