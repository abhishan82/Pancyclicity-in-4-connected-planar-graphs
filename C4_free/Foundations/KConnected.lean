/-
Copyright (c) 2025 Abhinav Shantanam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhinav Shantanam
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Finset.Card

/-!
# k-Connectivity for Simple Graphs

This file defines k-connectivity for simple graphs and establishes basic properties.

## Main definitions

* `SimpleGraph.IsKConnected`: A graph G is k-connected if it has at least k+1 vertices
  and remains connected after removing any fewer than k vertices.
* `SimpleGraph.deleteVerts`: Vertex deletion (re-exported from Mathlib for convenience).

## Main results

* `SimpleGraph.IsKConnected.mono`: k-connectivity implies j-connectivity for j ≤ k.
* `SimpleGraph.IsKConnected.connected`: k-connected graphs (k ≥ 1) are connected.
* `SimpleGraph.IsKConnected.minDegree_ge`: k-connected graphs have minimum degree ≥ k.
* `SimpleGraph.IsKConnected.card_edgeFinset_ge`: 4-connected graphs on n vertices
  have at least 2n edges.

## References

* [R. Diestel, *Graph Theory*][diestel2018]
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A graph `G` is `k`-connected if it has at least `k + 1` vertices and,
for every set `S` of fewer than `k` vertices, the graph `G.deleteVerts S`
is connected (i.e., preconnected and nonempty). -/
def IsKConnected (k : ℕ) : Prop :=
  k + 1 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce (↑(Sᶜ) : Set V)).Connected

/-- 0-connectivity just means the graph has at least 1 vertex. -/
theorem isKConnected_zero_iff :
    G.IsKConnected 0 ↔ Nonempty V := by
  constructor
  · intro ⟨h, _⟩
    exact Fintype.card_pos_iff.mp (by omega)
  · intro hne
    exact ⟨Fintype.card_pos_iff.mpr hne, fun S hS => absurd hS (Nat.not_lt_zero _)⟩

/-- 1-connectivity is equivalent to being connected with at least 2 vertices. -/
theorem isKConnected_one_iff :
    G.IsKConnected 1 ↔ 2 ≤ Fintype.card V ∧ G.Connected := by
  have heq : (↑(∅ : Finset V)ᶜ : Set V) = Set.univ := by simp
  constructor
  · intro ⟨hcard, hconn⟩
    refine ⟨hcard, ?_⟩
    have h := hconn ∅ (by simp)
    rw [heq] at h
    exact (induceUnivIso G).connected_iff.mp h
  · intro ⟨hcard, hconn⟩
    refine ⟨hcard, fun S hS => ?_⟩
    have hSeq : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hSeq; rw [heq]
    exact (induceUnivIso G).connected_iff.mpr hconn

namespace IsKConnected

variable {G} {k : ℕ}

/-- A k-connected graph has at least k + 1 vertices. -/
theorem card_vertices_ge (h : G.IsKConnected k) : k + 1 ≤ Fintype.card V :=
  h.1

/-- k-connectivity is monotone: if G is k-connected and j ≤ k, then G is j-connected. -/
theorem mono (h : G.IsKConnected k) {j : ℕ} (hjk : j ≤ k) : G.IsKConnected j := by
  constructor
  · have h1 := h.1; omega
  · intro S hS
    exact h.2 S (by omega)

/-- A k-connected graph with k ≥ 1 is connected. -/
theorem connected (h : G.IsKConnected k) (hk : 1 ≤ k) : G.Connected := by
  have h1 := h.mono hk
  rw [isKConnected_one_iff] at h1
  exact h1.2

/-- In a k-connected graph, every vertex has degree at least k. -/
theorem minDegree_ge [LocallyFinite G] (h : G.IsKConnected k) (v : V) :
    k ≤ G.degree v := by
  by_contra hlt
  push_neg at hlt
  have hScard : (G.neighborFinset v).card < k := by
    rwa [card_neighborFinset_eq_degree]
  have hconn := h.2 (G.neighborFinset v) hScard
  have hv_notinS : v ∉ G.neighborFinset v := notMem_neighborFinset_self G v
  have hv_mem : (v : V) ∈ (↑((G.neighborFinset v)ᶜ) : Set V) :=
    Finset.mem_coe.mpr (Finset.mem_compl.mpr hv_notinS)
  set v' : ↥(↑((G.neighborFinset v)ᶜ) : Set V) := ⟨v, hv_mem⟩
  have hv_iso : ∀ w : ↥(↑((G.neighborFinset v)ᶜ) : Set V),
      ¬(G.induce (↑((G.neighborFinset v)ᶜ) : Set V)).Adj v' w := by
    intro ⟨w, hw⟩ hadj
    exact (Finset.mem_compl.mp (Finset.mem_coe.mp hw))
      (by simpa using induce_adj.mp hadj)
  -- Any walk starting from v' must end at v' (since v' is isolated)
  have aux : ∀ (s u : ↥(↑((G.neighborFinset v)ᶜ) : Set V))
      (q : (G.induce (↑((G.neighborFinset v)ᶜ) : Set V)).Walk s u),
      s = v' → u = v' := fun _ _ q =>
    Walk.rec (motive := fun {s u} _ => s = v' → u = v')
      (fun {_} hs => hs)
      (fun hadj _ _ hs => absurd (hs ▸ hadj) (hv_iso _))
      q
  have hcard2 : 1 < ((G.neighborFinset v)ᶜ : Finset V).card := by
    rw [Finset.card_compl]; have := h.1; omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard2
  obtain ⟨w, hw_mem, hw_ne⟩ : ∃ w ∈ ((G.neighborFinset v)ᶜ : Finset V), w ≠ v := by
    rcases eq_or_ne a v with rfl | hav
    · exact ⟨b, hb, fun hbv => hab hbv.symm⟩
    · exact ⟨a, ha, hav⟩
  set w' : ↥(↑((G.neighborFinset v)ᶜ) : Set V) := ⟨w, Finset.mem_coe.mpr hw_mem⟩
  have hne : w' ≠ v' := fun heq => hw_ne (congrArg Subtype.val heq)
  obtain ⟨p⟩ := hconn.preconnected v' w'
  exact hne (aux v' w' p rfl)

/-- A k-connected graph on n vertices satisfies `k * n ≤ 2 * |E|`. -/
theorem card_edgeFinset_ge_general (h : G.IsKConnected k) :
    k * Fintype.card V ≤ 2 * G.edgeFinset.card :=
  calc k * Fintype.card V
      = ∑ _v : V, k := by simp [Finset.sum_const, Finset.card_univ, mul_comm]
    _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum fun v _ => h.minDegree_ge v
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

/-- A 4-connected graph on n vertices has at least 2n edges. -/
theorem card_edgeFinset_ge
    (h : G.IsKConnected 4) :
    2 * Fintype.card V ≤ G.edgeFinset.card := by
  have h4 : 4 * Fintype.card V ≤ 2 * G.edgeFinset.card :=
    calc 4 * Fintype.card V
        = ∑ _v : V, 4 := by simp [Finset.sum_const, Finset.card_univ, mul_comm]
      _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum fun v _ => h.minDegree_ge v
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  omega

end IsKConnected

end SimpleGraph
