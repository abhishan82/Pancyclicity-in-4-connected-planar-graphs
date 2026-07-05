/-
Copyright (c) 2025 Abhinav Shantanam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhinav Shantanam
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat
import C4_free.Axioms
import C4_free.Foundations.OuterplaneGraph

/-!
# Cycle Spectrum and Pancyclicity

This file defines the cycle spectrum of a graph (the set of lengths of cycles it contains)
and the notion of pancyclicity, contributing towards the formalization of the
Bondy/Malkevitch conjecture on 4-connected planar graphs.

## Main definitions

* `SimpleGraph.cycleSpectrum`: The set of cycle lengths present in `G`.
* `SimpleGraph.IsPancyclic`: `G` contains cycles of every length from 3 to `|V(G)|`.
* `SimpleGraph.edgeCycleSpectrum`: The set of cycle lengths through a given edge.

## References

* [J.A. Bondy, *Pancyclic graphs I*][bondy1971]
* [J. Malkevitch, *Polytopal graphs*][malkevitch1988]
-/

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- The **cycle spectrum** of a graph `G` is the set of natural numbers `n`
such that `G` contains a cycle of length `n`. -/
def cycleSpectrum : Set ℕ :=
  { n | ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n }

/-- A graph is **pancyclic** if it contains cycles of every length
from 3 up to the number of vertices. -/
def IsPancyclic [Fintype V] : Prop :=
  ∀ k : ℕ, 3 ≤ k → k ≤ Fintype.card V → k ∈ G.cycleSpectrum

/-- The **edge cycle spectrum** of a graph `G` with respect to an edge `e`
is the set of lengths of cycles in `G` that contain the edge `e`.

We represent an edge as a pair of adjacent vertices. A cycle `p` at vertex `v`
"contains" the edge `(a, b)` if the walk `p` traverses the adjacency `a ~ b`
at some point. -/
def edgeCycleSpectrum (a b : V) (hab : G.Adj a b) : Set ℕ :=
  { n | ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n ∧
    s(a, b) ∈ p.edges }

/-- Membership in the cycle spectrum: `n ∈ G.cycleSpectrum` iff there
exists a cycle of length `n`. -/
theorem mem_cycleSpectrum_iff {n : ℕ} :
    n ∈ G.cycleSpectrum ↔
      ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n := by
  rfl

/-- The cycle spectrum only contains values ≥ 3 (since cycles in simple graphs
have length at least 3). -/
theorem cycleSpectrum_subset_ge_three :
    G.cycleSpectrum ⊆ { n | 3 ≤ n } := by
  intro n hn
  obtain ⟨v, p, hcycle, hlen⟩ := hn
  simp only [Set.mem_setOf_eq]
  exact hlen ▸ hcycle.three_le_length

/-- The cycle spectrum is bounded above by `|V(G)|` for finite graphs. -/
theorem cycleSpectrum_subset_le_card [Fintype V] :
    G.cycleSpectrum ⊆ { n | n ≤ Fintype.card V } := by
  intro n hn
  obtain ⟨v, p, hcycle, hlen⟩ := hn
  simp only [Set.mem_setOf_eq]
  have htail := hcycle.isPath_tail
  have hlt := htail.length_lt
  have heq := Walk.length_tail_add_one hcycle.not_nil
  omega

/-- The cycle spectrum of a finite graph is finite. -/
theorem cycleSpectrum_finite [Fintype V] :
    G.cycleSpectrum.Finite :=
  (Set.finite_Icc 3 (Fintype.card V)).subset fun _ hn =>
    Set.mem_Icc.mpr ⟨cycleSpectrum_subset_ge_three G hn, cycleSpectrum_subset_le_card G hn⟩

/-- The edge cycle spectrum is a subset of the cycle spectrum. -/
theorem edgeCycleSpectrum_subset (a b : V) (hab : G.Adj a b) :
    G.edgeCycleSpectrum a b hab ⊆ G.cycleSpectrum := by
  intro n hn
  obtain ⟨v, p, hcycle, hlen, _⟩ := hn
  exact ⟨v, p, hcycle, hlen⟩

/-- The edge cycle spectrum of a finite graph through any edge is finite. -/
theorem edgeCycleSpectrum_finite [Fintype V] (a b : V) (hab : G.Adj a b) :
    (G.edgeCycleSpectrum a b hab).Finite :=
  (cycleSpectrum_finite G).subset (edgeCycleSpectrum_subset G a b hab)

/-- A Hamiltonian graph on `n ≥ 2` vertices has `n ∈ cycleSpectrum`:
the Hamiltonian cycle itself witnesses a cycle of length `n`. -/
theorem IsHamiltonian.card_mem_cycleSpectrum [Fintype V]
    (h : G.IsHamiltonian) (hcard : Fintype.card V ≠ 1) :
    Fintype.card V ∈ G.cycleSpectrum := by
  obtain ⟨v, p, hcyc⟩ := h hcard
  exact ⟨v, p, hcyc.isCycle, hcyc.length_eq⟩

/-- Conversely, a cycle of length `|V|` shows `G` is Hamiltonian:
a simple cycle visits at most `|V|` distinct vertices, so a cycle of
length exactly `|V|` must visit every vertex. -/
theorem isHamiltonian_of_card_mem_cycleSpectrum [Fintype V]
    (h : Fintype.card V ∈ G.cycleSpectrum) : G.IsHamiltonian := by
  obtain ⟨v, p, hcyc, hlen⟩ := h
  intro _
  exact ⟨v, p, Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hcyc, hlen⟩⟩

/-- A graph is Hamiltonian if and only if `|V| ∈ cycleSpectrum`.
(The `≠ 1` condition is needed only for the forward direction.) -/
theorem isHamiltonian_iff_card_mem_cycleSpectrum [Fintype V]
    (hne : Fintype.card V ≠ 1) :
    G.IsHamiltonian ↔ Fintype.card V ∈ G.cycleSpectrum := by
  constructor
  · intro h; exact IsHamiltonian.card_mem_cycleSpectrum G h hne
  · exact isHamiltonian_of_card_mem_cycleSpectrum G

/-- A pancyclic graph on `n ≥ 3` vertices is Hamiltonian (contains a cycle of length `n`). -/
theorem IsPancyclic.isHamiltonian [Fintype V]
    (h : G.IsPancyclic) (hn : 3 ≤ Fintype.card V) : G.IsHamiltonian := by
  intro hne1
  obtain ⟨v, p, hcyc, hlen⟩ := h (Fintype.card V) (by omega) le_rfl
  exact ⟨v, p, Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hcyc, hlen⟩⟩

/-- A pancyclic graph has cycle spectrum equal to `{3, 4, ..., |V|}`. -/
theorem IsPancyclic.cycleSpectrum_eq [Fintype V] (h : G.IsPancyclic) :
    G.cycleSpectrum = { n | 3 ≤ n ∧ n ≤ Fintype.card V } := by
  ext n
  constructor
  · intro hn
    exact ⟨cycleSpectrum_subset_ge_three G hn, cycleSpectrum_subset_le_card G hn⟩
  · intro ⟨h3, hcard⟩
    exact h n h3 hcard

/-- The cycle spectrum has at most `|V| - 2` elements (cycles have lengths 3, …, |V|). -/
theorem cycleSpectrum_ncard_le [Fintype V] :
    G.cycleSpectrum.ncard ≤ Fintype.card V - 2 := by
  have h1 : G.cycleSpectrum ⊆ Set.Icc 3 (Fintype.card V) := fun n hn =>
    Set.mem_Icc.mpr ⟨cycleSpectrum_subset_ge_three G hn, cycleSpectrum_subset_le_card G hn⟩
  calc G.cycleSpectrum.ncard
      ≤ (Set.Icc 3 (Fintype.card V)).ncard :=
        Set.ncard_le_ncard h1 (Set.finite_Icc _ _)
    _ = Fintype.card V + 1 - 3 := Set.ncard_Icc_nat 3 (Fintype.card V)
    _ = Fintype.card V - 2 := by omega

/-- A pancyclic graph has exactly `|V| - 2` distinct cycle lengths. -/
theorem IsPancyclic.cycleSpectrum_ncard [Fintype V] (h : G.IsPancyclic) :
    G.cycleSpectrum.ncard = Fintype.card V - 2 := by
  rw [h.cycleSpectrum_eq]
  have heq : { n : ℕ | 3 ≤ n ∧ n ≤ Fintype.card V } = Set.Icc 3 (Fintype.card V) := by
    ext n; simp [Set.mem_Icc]
  rw [heq, Set.ncard_Icc_nat]
  omega

/-- **Malkevitch's Conjecture** (1988): Every 4-connected planar graph is pancyclic.

This is the main theorem the project aims to establish. Currently stated with `sorry`
pending the full development of planar graph infrastructure and the main argument. -/
theorem malkevitch_conjecture [Fintype V] [DecidableRel G.Adj]
    (h : G.IsKConnected 4) (hp : G.IsPlanar) : G.IsPancyclic := by
  sorry

end SimpleGraph

/-!
## Main Theorems
-/

namespace SimpleGraph.IsKConnected

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A 4-connected planar graph has `|V| ∈ cycleSpectrum`: by Tutte's theorem
it is Hamiltonian, giving a cycle of length `|V|`. -/
theorem four_planar_card_mem_cycleSpectrum
    (h : G.IsKConnected 4) (hp : G.IsPlanar) :
    Fintype.card V ∈ G.cycleSpectrum := by
  have hham := h.isHamiltonian_of_isPlanar hp
  have hne : Fintype.card V ≠ 1 := by have := h.card_vertices_ge; omega
  obtain ⟨v, p, hcyc⟩ := hham hne
  exact ⟨v, p, hcyc.isCycle, hcyc.length_eq⟩

/-- **Theorem 1.2** (Shantanam): If `G` is a 4-connected planar graph on `n` vertices
and `e = (a, b)` is any edge, then `G` contains at least `⌈n/2⌉ + 1` cycles of
pairwise distinct lengths each containing `e`.

**Proof sketch** (axiomatized):
1. By Sanders' theorem, there exists a Hamiltonian cycle `C` through `e`.
2. `C` gives a decomposition `(G, C, G₀, G₁)` with `|E(G₁)| ≥ |E(G₀)|`.
3. Since `|E(G)| ≥ 2n` (4-connected) and `|C| = n`, total chords `c ≥ n`.
   With `c₁ ≥ c₀`, we get `c₁ ≥ n/2`, so `c₁ ≥ ⌈n/2⌉`.
4. `e` lies on the boundary of both `G₀` and `G₁`.
5. By `cycles_of_distinct_lengths`, `G₁` has ≥ `c₁ + 1 ≥ ⌈n/2⌉ + 1`
   distinct cycle lengths through `e`.

**(P)** -/
theorem cycle_lengths_through_edge
    (h : G.IsKConnected 4) (hp : G.IsPlanar)
    (a b : V) (hab : G.Adj a b) :
    (Fintype.card V + 1) / 2 + 1 ≤ (G.edgeCycleSpectrum a b hab).ncard := sorry

/-- In a 4-connected planar graph, the cycle spectrum has at least `⌈n/2⌉ + 1` elements. -/
theorem four_planar_cycleSpectrum_ncard_ge
    (h : G.IsKConnected 4) (hp : G.IsPlanar)
    (a b : V) (hab : G.Adj a b) :
    (Fintype.card V + 1) / 2 + 1 ≤ G.cycleSpectrum.ncard := by
  have h_sub : G.edgeCycleSpectrum a b hab ⊆ G.cycleSpectrum :=
    edgeCycleSpectrum_subset G a b hab
  have h_fin : G.cycleSpectrum.Finite :=
    (Set.finite_Icc 3 (Fintype.card V)).subset fun n hn =>
      Set.mem_Icc.mpr
        ⟨cycleSpectrum_subset_ge_three G hn, cycleSpectrum_subset_le_card G hn⟩
  exact le_trans (h.cycle_lengths_through_edge hp a b hab)
    (Set.ncard_le_ncard h_sub h_fin)

end SimpleGraph.IsKConnected

namespace SimpleGraph.OuterplaneGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable (opg : OuterplaneGraph G)

/-- **Cycles of distinct lengths through a boundary edge**
(key lemma, Shantanam §3): If `G` is a 2-connected outerplane graph with `c`
chords and `e = (a, b)` is an edge on the outer face boundary, then
`G` contains at least `c + 1` cycles of pairwise distinct lengths,
each containing the edge `e`.

The proof goes by induction on `c` using the internal dual tree:
* Base `c = 0`: `G` is a single cycle of length `n`, giving 1 = 0+1 distinct length.
* Step: removing a leaf of the internal dual tree (= contracting a chord) reduces
  to a graph with `c-1` chords while losing exactly one cycle length,
  then restoring the chord adds back a new distinct length.

Assumed pending the full chord-induction infrastructure.

**(P)** -/
theorem cycles_of_distinct_lengths
    (hconn : G.IsKConnected 2)
    (a b : V) (hab : G.Adj a b)
    (hboundary : s(a, b) ∈ opg.boundaryEdgeFinset) :
    opg.chordCount + 1 ≤ (G.edgeCycleSpectrum a b hab).ncard := sorry

end SimpleGraph.OuterplaneGraph

/-!
## Open Conjectures

The following are open conjectures stated as Lean propositions (not axioms —
we make no claim of their truth, only that they are well-formed statements).
-/

namespace Pancyclicity

open SimpleGraph

/-- **Conjecture 7.1** (Edge cycle bound): In a 4-connected planar graph on `n` vertices,
each edge lies on cycles of at least `⌊2n/3⌋ + c` pairwise distinct lengths,
for some universal integer constant `c`. -/
def conjecture_edge_cycle_bound : Prop :=
  ∃ c : ℤ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsKConnected 4 → G.IsPlanar →
    ∀ (a b : V) (hab : G.Adj a b),
      (2 * Fintype.card V / 3 : ℤ) + c ≤
        (G.edgeCycleSpectrum a b hab).ncard

/-- **Conjecture 7.2** (Outerplanar contiguous cycles): In a 2-connected outerplanar
graph on `n` vertices with at least `3n/2` edges, the cycle spectrum contains a
contiguous interval of length at least `⌊n/2⌋ + c` within `{3, …, n}`,
for some universal integer constant `c`. -/
def conjecture_outerplanar_contiguous : Prop :=
  ∃ c : ℤ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsKConnected 2 → G.IsOuterplanar →
    3 * Fintype.card V / 2 ≤ G.edgeFinset.card →
    ∃ a k : ℕ, (Fintype.card V / 2 : ℤ) + c ≤ k ∧
      Set.Icc a (a + k - 1) ⊆ G.cycleSpectrum ∧
      Set.Icc a (a + k - 1) ⊆ Set.Icc 3 (Fintype.card V)

end Pancyclicity
