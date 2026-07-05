# `GraphFamily.lean`: options for the `G_k` data axioms

**Status: report only, per Task 6 of `TASKS_pancyclicity.md`. No changes have been
made to `GraphFamily.lean` in this session.** This document compares two ways to
remove the risk described in that brief — "axiomatized objects with
axiomatized properties risk an inconsistent environment (everything
provable)" — and ends with a recommendation. The author decides; implementation
is future work.

## What's actually axiomatized today

`GraphFamily.lean` states, as `axiom`:

| Declaration | What it claims |
|---|---|
| `Gk (k)` | A `SimpleGraph (GkVertex k)` exists — the graph itself, as *data*. |
| `Gk.instDecidableRel (k)` | Its adjacency is decidable. |
| `Gk.edge (k) (hk : 1 ≤ k)` | `Gk k` has the designated edge `v₀v_{k+2}`. |
| `Gk.isKConnected_four (k) (hk)` | `Gk k` is 4-connected. |
| `Gk.isPlanar (k) (hk)` | `Gk k` is planar. |
| `Gk.cycle_count_exact (k) (hk)` | The edge cycle spectrum through `e` has **exactly** `2k+2` elements. |

`GkVertex k` (the vertex type, `u`/`w`/`v` constructors), `GkVertex.card`
(`= 3k+3`), `gkSrc`, `gkTgt` are already concrete, proved definitions/theorems —
only the graph `Gk` itself and its four properties are axiomatized.

## A finding that changes the risk calculus: there are no downstream consumers

Before comparing options, the important fact to establish is *how much of the
project actually rests on these axioms*. A repo-wide search
(`grep -rn 'Gk\.|GraphFamily\.|GkVertex|gkSrc|gkTgt' C4_free/`) shows **every
reference to `Gk`, `GkVertex`, `gkSrc`, `gkTgt` is inside `GraphFamily.lean`
itself.** No other file in `C4_free/` imports or uses anything from this file.
So "downstream use sites" for either option below means *the seven theorems
already in this file*, not anything in `CycleSpectrum.lean`, `NoFourCycles.lean`,
etc.

Narrowing further, of those seven theorems only two actually consume the
axiomatized *graph data* (`Gk`, `Gk.edge`, `Gk.cycle_count_exact`):

- `Gk.satisfies_theorem_bound` — uses `Gk.cycle_count_exact` and
  `Gk.example_satisfies_lower_bound`.
- `Gk.gap_k_ge_three` — uses `Gk.cycle_count_exact` and `GkVertex.card`.

The other five (`GkVertex.card`, `Gk.example_satisfies_lower_bound`,
`Gk.tightness_k1`, `Gk.tightness_k2`, `Gk.not_tight_k_ge_three`,
`Gk.tightness_iff`) are pure arithmetic about `Fintype.card (GkVertex k) =
3k+3`; they never touch `Gk`, `Gk.edge`, or `Gk.cycle_count_exact` at all,
axiomatized or not.

A second finding worth flagging: **`Gk.isKConnected_four` and `Gk.isPlanar` are
never used anywhere**, including inside this file. They exist solely to state
the blueprint's `lem:gk_properties` ("`G_k` is 4-connected and planar")
faithfully as a standalone fact — no proof in the repo takes them as a
hypothesis. This means neither option below is under any obligation from
existing proofs to touch them, though a faithful account of the blueprint
should still address them somehow (see per-property estimates below).

## Option (a): concrete construction, properties as sorried theorems

Define `Gk k` explicitly as a `SimpleGraph (GkVertex k)` by giving its `Adj`
relation on the `u`/`w`/`v` constructors already in place, then state each of
the four properties as `theorem ... := sorry` (per this project's no-new-axiom
policy) instead of `axiom`.

**Blocking issue before this can start**: the blueprint's `def:gk_construction`
is a one-paragraph gloss — "For each i, connect `u_i` and `w_i` to both `v_i`
and `v_{i+1}`. Add vertices `v_0, v_{k+2}` with specified adjacencies" — and is
*not* precise enough to write `Adj` by cases. In particular it doesn't
pin down: whether `P_U = u_1⋯u_k` and `P_W = w_1⋯w_k` denote actual path edges
among consecutive `u_i`/`w_i` or are just an indexing convention, and what "specified
adjacencies" for `v_0`/`v_{k+2}` actually are beyond the single edge `e`. Getting
this right requires reading §5 of Shantanam's paper directly (not just the
blueprint), which is outside what this session verified. Any difficulty
estimate below assumes that gap is closed first.

Assuming the construction is pinned down, per-property estimate:

| Property | Estimated difficulty | Why |
|---|---|---|
| `instDecidableRel` | **Low** | Automatic once `Adj` is an explicit case-match on `Fin`/`Nat` equalities — `GkVertex` already derives `DecidableEq`. |
| `edge` | **Low** | A `rfl`/`decide` once `e = v₀v_{k+2}` is literally one of the defining `Adj` clauses. |
| `isKConnected_four` | **High** | Proving 4-connectivity of a `k`-indexed family means an induction (or an explicit Menger-style disjoint-paths argument) uniform in `k`; there's no shortcut through existing `Foundations/KConnected.lean` machinery, which only gives necessary conditions (min-degree bounds), not a way to establish connectivity of a specific graph. |
| `isPlanar` | **Medium–High** | Needs an explicit `PlaneGraph` witness — a rotation system (`CombMap`) on `GkVertex k` satisfying the genus-0 axioms, indexed uniformly over `k`. The family is structurally a "ladder/prism," which *is* planar, but threading an explicit, checked rotation system through `Fin k`-indexed vertices using the existing `Foundations/CombMap.lean`/`PlaneGraph.lean` API is real formalization work, not a one-liner. |
| `cycle_count_exact` | **Very high** | This is an *exact* count, not a bound: it needs both a lower bound (exhibit `2k+2` explicit cycles of pairwise distinct lengths through `e`, presumably by induction on `k`) **and** a matching upper bound (no other cycle length occurs). The upper-bound direction is the hard part and is arguably comparable in difficulty to a nontrivial slice of the general machinery in `NoFourCycles.lean`/`CycleSpectrum.lean` — it is not a corollary of anything currently proved, since `cycles_of_distinct_lengths` (Lemma 3.1) only gives a *lower* bound (`≥ c+1`), not an exact count. |

Overall: this is a substantial, standalone formalization project in its own
right — realistically comparable in scope to a meaningful fraction of the
paper's combinatorial core, concentrated almost entirely in `isKConnected_four`
and `cycle_count_exact`. Its payoff is that it makes Theorem 1.3 (tightness)
into a genuine, unconditional existence result with zero residual axiom risk.

## Option (b): bundle into a hypothesis-taking `structure`

Replace the six axioms with a structure:

```lean
structure ExtremalFamily (k : ℕ) (hk : 1 ≤ k) where
  G : SimpleGraph (GkVertex k)
  instDecRel : DecidableRel G.Adj
  edge : G.Adj (gkSrc k) (gkTgt k)
  isKConnected_four : G.IsKConnected 4
  isPlanar : G.IsPlanar
  cycle_count_exact : (G.edgeCycleSpectrum (gkSrc k) (gkTgt k) edge).ncard = 2 * k + 2
```

and rewrite the theorems that use the axiomatized data to take
`(F : ExtremalFamily k hk)` as an explicit hypothesis instead of calling `Gk k`
globally.

**Every downstream use site that would change**, given the finding above: just
the two theorems that actually consume the data —

- `Gk.satisfies_theorem_bound` → takes `(F : ExtremalFamily k hk)`, uses
  `F.cycle_count_exact` in place of `Gk.cycle_count_exact k hk`.
- `Gk.gap_k_ge_three` → same change, using `F.cycle_count_exact`.

The other five theorems (`GkVertex.card` and friends) are untouched — they
never reference `Gk` at all. `Gk.isKConnected_four`/`Gk.isPlanar` become
structure fields (`F.isKConnected_four`, `F.isPlanar`) that remain unused
unless a future proof needs them, same as today.

This is a small, mechanical migration — roughly a dozen lines — *because*
nothing outside this file depends on the current axioms.

**What it costs**: bundling is a soundness fix, not a mathematical result. The
resulting theorems say "if a family with these properties exists, then the
bound is met/tight," not "the bound is met/tight, and such a family exists" —
the existence content of Theorem 1.3 (that `G_k` is *realized*, not merely
hypothetical) is exactly what gets dropped. `ExtremalFamily k hk` could be
empty (vacuously true theorems) without Lean ever telling you so.

## Recommendation

Do **(b) now, (a) later**. Concretely:

- Bundling removes the actual soundness risk the task brief is worried about
  (an unconstrained data axiom plus an unconstrained property-of-that-data axiom
  can make the environment inconsistent, and Lean will not warn you) at very low
  cost — two theorem signatures change, nothing outside this file is touched,
  and the change is mechanical enough to be low-risk.
- It is explicitly **not** a substitute for (a): Theorem 1.3's actual
  mathematical content is that the extremal family *exists*, and (b) alone
  can never establish that — only (a) can. The honest framing after doing (b)
  is "Theorem 1.3 modulo the existence of `G_k`," which should be stated
  plainly in the README ledger (bucket D) rather than presented as fully proved.
- (a) is the real remaining mathematical work, and per the difficulty table
  above, `cycle_count_exact` and `isKConnected_four` are its two expensive
  parts — comparable in scope to a nontrivial piece of the paper, not a quick
  follow-up. It's worth scoping as its own project once the precise
  construction is pinned down from §5 of the paper (the blueprint prose alone
  is insufficient, see "blocking issue" above).
