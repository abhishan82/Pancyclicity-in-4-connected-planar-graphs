/-
Copyright (c) 2025 Abhinav Shantanam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhinav Shantanam
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Tactic.Linarith
import C4_free.Foundations.CombMap

/-!
# Surface Graphs, Plane Graphs, and Planarity

This file defines graph embeddings on orientable surfaces via combinatorial maps,
parameterized by genus `g`. The key cases are:

* `g = 0`: plane graphs (sphere / plane)
* `g = 1`: torus graphs
* etc.

## Main definitions

* `SimpleGraph.SurfaceGraph G g`: A combinatorial map on `G` realizing an embedding
  on an orientable surface of genus `g`. The Euler characteristic condition
  `V - E + F = 2 - 2g` is a field.
* `SimpleGraph.PlaneGraph G`: Abbreviation for `G.SurfaceGraph 0`.
* `SimpleGraph.IsPlanar G`: `G` admits a plane graph structure.
* `SimpleGraph.SurfaceGraph.Face`: A face of the embedding — a cyclic orbit of `φ`.
* `SimpleGraph.SurfaceGraph.faceFinset`: The finite set of all faces.

## Main results

* `SimpleGraph.SurfaceGraph.euler_formula`: The Euler formula `V - E + F = 2 - 2g`
  (immediate from the `euler` field).
* `SimpleGraph.PlaneGraph.euler_formula`: For plane graphs, `V - E + F = 2`.

## References

* [B. Mohar and C. Thomassen, *Graphs on Surfaces*][mohar2001]
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A **surface graph** of genus `g`: a simple graph `G` together with a
combinatorial map (rotation system) whose Euler characteristic satisfies
`V - E + F = 2 - 2g`, realizing a cellular embedding of `G` on an orientable
surface of genus `g`. -/
structure SurfaceGraph (G : SimpleGraph V) [DecidableRel G.Adj] (g : ℕ) where
  /-- The underlying combinatorial map (rotation system). -/
  cmap  : G.CombMap
  /-- The Euler characteristic condition for genus `g`:
  `V - E + F = 2 - 2g`. -/
  euler : (Fintype.card V : ℤ) - G.edgeFinset.card + cmap.faceCount = 2 - 2 * g
  /-- **Face boundary simplicity**: In a cellular embedding, each face boundary is a
  simple closed walk — every vertex appears at most once as a dart source on each face.
  Equivalently, the map `d ↦ d.fst` is injective on the support of every face. -/
  face_orbit_simple : ∀ f ∈ cmap.facePerm.cycleFactorsFinset,
      ∀ d₁ ∈ f.support, ∀ d₂ ∈ f.support, d₁.fst = d₂.fst → d₁ = d₂

/-- A **plane graph**: a graph embedded on the sphere/plane (genus 0).
This is the genus-0 case of `SurfaceGraph`. -/
abbrev PlaneGraph (G : SimpleGraph V) [DecidableRel G.Adj] :=
  G.SurfaceGraph 0

/-- A graph is **planar** if it admits some plane graph structure. -/
def IsPlanar (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Nonempty (G.PlaneGraph)

namespace SurfaceGraph

variable {g : ℕ} (pg : G.SurfaceGraph g)

/-- The **Euler formula** for a genus-`g` surface embedding:
`V - E + F = 2 - 2g`. -/
theorem euler_formula :
    (Fintype.card V : ℤ) - G.edgeFinset.card + pg.cmap.faceCount = 2 - 2 * g :=
  pg.euler

/-- A **face** of the embedding is a cyclic orbit of the face permutation `φ`,
represented as a cycle factor of `φ`. The number of faces equals `pg.cmap.faceCount`. -/
def Face (pg : G.SurfaceGraph g) :=
  {σ : Equiv.Perm G.Dart // σ ∈ pg.cmap.facePerm.cycleFactorsFinset}

/-- The **darts** of a face: the support of its cycle permutation. -/
noncomputable def Face.darts (f : pg.Face) : Finset G.Dart :=
  f.val.support

/-- The **size** of a face: the number of darts on its boundary. -/
noncomputable def Face.size (f : pg.Face) : ℕ :=
  f.darts.card

/-- The set of all faces, as a `Finset` of cycle permutations. -/
noncomputable def faceFinset : Finset (Equiv.Perm G.Dart) :=
  pg.cmap.facePerm.cycleFactorsFinset

/-- The face count agrees with `cmap.faceCount`. -/
theorem card_faceFinset_eq :
    pg.faceFinset.card = pg.cmap.faceCount :=
  rfl

end SurfaceGraph

namespace PlaneGraph

variable (pg : G.PlaneGraph)

/-- The **Euler formula** for plane graphs: `V - E + F = 2`. -/
theorem euler_formula :
    (Fintype.card V : ℤ) - G.edgeFinset.card + pg.cmap.faceCount = 2 := by
  simpa using pg.euler

/-- The **dual graph** `G*`: faces of `pg` as vertices, with two faces adjacent
iff they share a boundary dart (i.e., are separated by a common edge of `G`).
Dart `d` and `d.symm` lie on opposite sides of each edge, giving the duality. -/
noncomputable def dual : SimpleGraph pg.Face :=
  { Adj    := fun f1 f2 => f1 ≠ f2 ∧
                ∃ d : G.Dart, d ∈ f1.val.support ∧ d.symm ∈ f2.val.support
    symm   := fun {f1 f2} ⟨hne, d, hd1, hd2⟩ =>
                ⟨hne.symm, d.symm, hd2, by simpa using hd1⟩
    loopless := ⟨fun f h => h.1 rfl⟩ }

/-- Classical `DecidableRel` instance for the dual graph's adjacency relation.
The adjacency `f₁ ~ f₂` is decidable since `G.Dart` is finite (existential over
a finite type with decidable membership). We use `Classical.propDecidable` to
avoid computing the witness explicitly. -/
noncomputable instance instDecidableRelDualAdj (pg : G.PlaneGraph) :
    DecidableRel pg.dual.Adj :=
  fun _ _ => Classical.propDecidable _

/-- An **outer face** of a plane graph: any face may be designated the
infinite (outer) face of the planar embedding. This is a type alias for
`pg.Face`; the choice of which face is "outer" is left to the user. -/
abbrev outerFace := pg.Face

/-- The **internal dual** of `pg` relative to outer face `f`:
the dual graph `G*` with the vertex corresponding to `f` deleted. -/
noncomputable def internalDual (f : pg.Face) :
    SimpleGraph {f' : pg.Face // f' ≠ f} :=
  pg.dual.induce {f' | f' ≠ f}

/-- **Edge weight `w'`** (blueprint: `PlaneGraph.HamiltonianDecomp.weight_wprime`):
For dart `d` in plane graph `pg`, `w'(d) = (|F_d| - 2)/|F_d| + (|F_{d.symm}| - 2)/|F_{d.symm}|`
where `F_d` is the face of `pg` whose orbit contains `d`. -/
noncomputable def edgeDartWeight (pg : G.PlaneGraph) (d : G.Dart) : ℚ :=
  let n₁ := (pg.cmap.facePerm.cycleOf d).support.card
  let n₂ := (pg.cmap.facePerm.cycleOf d.symm).support.card
  ((n₁ : ℚ) - 2) / n₁ + ((n₂ : ℚ) - 2) / n₂

/-- **Sum of `w'`** (axiomatized; blueprint: `PlaneGraph.HamiltonianDecomp.sum_wprime_eq`):
For a plane Hamiltonian graph on `n` vertices,
`∑_{e ∈ E(G)} w'(e) = 2(n - 2)`. Each undirected edge contributes both darts;
we divide by 2 to count edges. -/
theorem sum_edgeDartWeight_eq (pg : G.PlaneGraph) (hham : G.IsHamiltonian) :
    ∑ d : G.Dart, pg.edgeDartWeight d / 2 = 2 * ((Fintype.card V : ℚ) - 2) := by
  set σ := pg.cmap.facePerm with hσ
  -- Step 3 (Euler): ∑ c ∈ σ.cycleFactorsFinset, (|c| - 2 : ℚ) = 2(V - 2)
  have h_step3 : σ.cycleFactorsFinset.sum (fun c => ((c.support.card : ℚ) - 2)) =
      2 * ((Fintype.card V : ℚ) - 2) := by
    -- ∑ c, |c| = |Dart| = 2|E|  (in ℕ, lifted to ℚ)
    have hS : σ.cycleFactorsFinset.sum (fun c => (c.support.card : ℚ)) =
        2 * G.edgeFinset.card := by
      have h := pg.cmap.sum_support_card_cycleFactorsFinset.trans
                  G.dart_card_eq_twice_card_edges
      exact_mod_cast h
    -- F = |cycleFactorsFinset|
    have hF : (σ.cycleFactorsFinset.card : ℚ) = pg.cmap.faceCount := by
      exact_mod_cast pg.card_faceFinset_eq
    -- Euler formula V - E + F = 2 (lift ℤ → ℚ)
    have h_euler : (Fintype.card V : ℚ) - G.edgeFinset.card + pg.cmap.faceCount = 2 := by
      exact_mod_cast pg.euler_formula
    -- ∑(|c| - 2) = ∑|c| - 2F  (split and simplify nsmul)
    have hSplit : σ.cycleFactorsFinset.sum (fun c => ((c.support.card : ℚ) - 2)) =
        σ.cycleFactorsFinset.sum (fun c => (c.support.card : ℚ)) -
        2 * σ.cycleFactorsFinset.card := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    linarith
  -- Step 2 (face reindex): ∑ d, f(d) = ∑ c, (|c| - 2)
  have h_step2 : ∑ d : G.Dart, (((σ.cycleOf d).support.card : ℚ) - 2) /
      (σ.cycleOf d).support.card =
      σ.cycleFactorsFinset.sum (fun c => ((c.support.card : ℚ) - 2)) := by
    -- Partition Finset.univ into cycle supports using sum_biUnion
    have h_biUnion : σ.cycleFactorsFinset.biUnion (·.support) = Finset.univ := by
      ext d
      simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
      rw [← Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset,
          pg.cmap.facePerm_support_eq_univ]
      exact Finset.mem_univ _
    have h_disj : (σ.cycleFactorsFinset : Set (Equiv.Perm G.Dart)).PairwiseDisjoint
        (fun c => c.support) := by
      intro c₁ hc₁ c₂ hc₂ hne
      exact (Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ hc₁ hc₂ hne).disjoint_support
    -- Rewrite LHS: ∑ d : G.Dart = ∑ d ∈ biUnion = ∑ c, ∑ d ∈ c.support
    rw [← h_biUnion, Finset.sum_biUnion h_disj]
    -- For each face c, ∑ d ∈ c.support, f(d) = (|c| - 2)
    apply Finset.sum_congr rfl
    intro c hc
    have h_pos : 0 < c.support.card :=
      Finset.card_pos.mpr (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
    -- For d ∈ c.support, σ.cycleOf d = c (so n(d) = c.support.card)
    have h_cyc : ∀ d ∈ c.support, σ.cycleOf d = c := fun d hd =>
      (Equiv.Perm.cycle_is_cycleOf hd hc).symm
    -- Replace cycleOf d with c; inner sum becomes constant
    trans c.support.sum (fun _ => ((c.support.card : ℚ) - 2) / c.support.card)
    · exact Finset.sum_congr rfl fun d hd => by rw [h_cyc d hd]
    -- c.support.card * ((|c| - 2) / |c|) = |c| - 2
    · rw [Finset.sum_const, nsmul_eq_mul]
      have h_ne : (c.support.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h_pos.ne'
      rw [mul_comm, div_mul_cancel₀ _ h_ne]
  -- Step 1 (symmetry): ∑ d, w'(d)/2 = ∑ d, f(d)
  have h_step1 : ∑ d : G.Dart, pg.edgeDartWeight d / 2 =
      ∑ d : G.Dart, (((σ.cycleOf d).support.card : ℚ) - 2) / (σ.cycleOf d).support.card := by
    -- Symmetry: ∑ d, f(d.symm) = ∑ d, f(d)  via d ↦ d.symm bijection
    have h_sym : ∑ d : G.Dart, (((σ.cycleOf d.symm).support.card : ℚ) - 2) /
        (σ.cycleOf d.symm).support.card =
        ∑ d : G.Dart, (((σ.cycleOf d).support.card : ℚ) - 2) /
        (σ.cycleOf d).support.card :=
      Finset.sum_equiv G.dartRevEquiv (fun _ => by simp)
        (fun d _ => by simp [dartRevEquiv_apply])
    -- ∑ f / b = (∑ f) / b  (pull constant denominator out of sum)
    have sum_div : ∀ (f : G.Dart → ℚ) (b : ℚ),
        ∑ d : G.Dart, f d / b = (∑ d : G.Dart, f d) / b := fun f b => by
      simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
    -- Unfold edgeDartWeight, pull out /2, split, apply symmetry
    simp_rw [edgeDartWeight, ← hσ]
    rw [sum_div, Finset.sum_add_distrib, h_sym]
    ring
  linarith [h_step1, h_step2, h_step3]

end PlaneGraph

end SimpleGraph
