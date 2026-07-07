# Towards Pancyclicity in 4-Connected Planar Graphs

Lean 4 formalization of results from *Towards Pancyclicity in 4-Connected Planar
Graphs* (Bojan Mohar, Abhinav Shantanam), a paper about the **Malkevitch
conjecture**: every 4-connected planar graph containing a 4-cycle is pancyclic
(contains a cycle of every length from 3 to `n`).

The blueprint (paper-to-Lean dictionary) is under [`blueprint/`](blueprint) and
is the source of truth for every statement below — do not take the plain-language
summaries here as more authoritative than `blueprint/src/content.tex`.

## Status

**This is a formalization of the scaffolding, not a finished proof.** The main
conjecture is stated and currently `sorry`ed. A large amount of supporting
graph theory (connectivity, planar embeddings via combinatorial maps, outerplanar
graphs, cycle spectra) is fully proved, and several of the paper's own theorems
are proved *modulo* the assumed results listed in the ledger below. Read that
ledger before trusting any claim of "proved" — "proved" here means "proved from
the axioms/sorries in the ledger," not "proved from Mathlib alone."

## Plain-language statement of the main results

- **Cycle spectrum**: the cycle spectrum of a graph `G` is the set of distinct
  cycle lengths appearing in `G`. `G` is *pancyclic* if its cycle spectrum is
  exactly `{3, ..., n}`.
- **Malkevitch's Conjecture**: a 4-connected planar graph containing a 4-cycle is
  pancyclic. (Formalized as the target theorem `SimpleGraph.malkevitch_conjecture`,
  currently `sorry`.)
- **Theorem 1.2**: every 4-connected planar graph on `n` vertices has, through
  every edge, at least `⌈n/2⌉ + 1` cycles of pairwise distinct lengths.
- **Theorem 1.3**: Theorem 1.2 is tight — the graph family `G_k` (3k+3 vertices)
  realizes exactly `2k+2` such cycles, matching the bound at `k = 1, 2`.
- **Theorem 1.4**: if in addition `G` has no 4-cycles, the bound strengthens to
  at least `⌈5n/6⌉ + 2` distinct cycle lengths.

## Architecture

```
C4_free/
├── Foundations/
│   ├── KConnected.lean       -- k-connectivity, min-degree, edge-count bounds
│   ├── CombMap.lean           -- combinatorial maps (rotation systems)
│   ├── PlaneGraph.lean        -- plane graphs, faces, Euler's formula, duals
│   ├── OuterplaneGraph.lean   -- outerplanar graphs, chords, internal dual
│   ├── HamiltonianDecomp.lean -- the (G, C, G₀, G₁) decomposition, weight functions
│   └── FiveBlocks.lean        -- 5-fans, 5-blocks, 5-flowers, 5-trees
├── CycleSpectrum.lean          -- cycle spectrum API + the target theorem
├── Axioms.lean                 -- deep external theorems (Tutte, Sanders, Whitney)
├── GraphFamily.lean             -- the extremal family G_k (Theorem 1.3)
└── NoFourCycles.lean            -- main technical development (Ch. 4-5, Theorem 1.4)
```

`Axioms.lean` is the intended home for permanently-assumed external hammers;
paper-internal lemmas that are only assumed *for now* live next to the theorems
that state them, in whichever file matches the blueprint chapter.

## Assumed-results ledger

Every `axiom` and `sorry` in `C4_free/`, bucketed by why it's assumed. Counts as
of this ledger: **6 axioms** (all in `GraphFamily.lean`, bucket D) **and 16
`sorry`s** (14 migrated from former axioms, plus `malkevitch_conjecture` and
the extracted `triangular_faces_diagonal_ne`). Read the doc comment on each
declaration for the full statement and proof sketch — this table is an index,
not a substitute.

Buckets:
- **(H)** Deep external hammer, permanently assumed with citation.
- **(P)** Paper-internal lemma, assumed for now — this project's own
  mathematics, intended to eventually be proved.
- **(D)** Data axiom — the extremal graph family `G_k` and its properties are
  axiomatized as data (see `docs/graphfamily_options.md` for the construction
  plan).
- **(T)** Target — the end-goal conjecture (and any sorries that only exist to
  document a genuinely-unfinished proof step toward it).

| Bucket | Declaration | File | Note |
|---|---|---|---|
| H | `isHamiltonian_of_isPlanar` | `Axioms.lean` | Tutte 1956: 4-connected planar ⟹ Hamiltonian |
| H | `hamiltonianCycle_through_edges` | `Axioms.lean` | Sanders 1997: any two edges lie on a common Hamiltonian cycle |
| H | `unique_planar_embedding` | `Axioms.lean` | Whitney 1932: 3-connected planar graphs have a unique embedding |
| P | `internalDual_isTree` | `Foundations/OuterplaneGraph.lean` | Internal dual of a 2-connected outerplane graph is a tree |
| P | `discharging_bound` | `NoFourCycles.lean` | Lemma 4.1: `s^{>5} ≤ n/3 - 10` |
| P | `enumeration_lemma` | `NoFourCycles.lean` | Lemma 5.1: cycle enumeration from a face adjacent to two leaf-triangles |
| P | `wellTriangulated_cycle_enumeration` | `NoFourCycles.lean` | Corollary 5.2 |
| P | `cycle_spectrum_no_four_cycles` | `NoFourCycles.lean` | Theorem 1.4 main statement |
| P | `leafPathsPartition` | `NoFourCycles.lean` | Every tree admits a leaf-paths partition |
| P | `chord_bound_no_four_cycles` | `NoFourCycles.lean` | `7·chordCount ≤ 5(n-3)` under no-4-cycles |
| P | `leaf_triangle_bound` | `NoFourCycles.lean` | `tᵢ ≥ sᵢ^{>5} + 2cᵢ - n + 4` |
| P | `leaf_triangle_corollary` | `NoFourCycles.lean` | Corollary of the leaf-triangle bound |
| P | `cycle_lengths_through_edge` | `CycleSpectrum.lean` | Theorem 1.2 main statement |
| P | `cycles_of_distinct_lengths` | `CycleSpectrum.lean` | Lemma 3.1: outerplane cycle enumeration |
| D | `Gk` | `GraphFamily.lean` | The extremal family `G_k`, axiomatized as data |
| D | `Gk.instDecidableRel` | `GraphFamily.lean` | Decidability instance for `G_k`'s adjacency |
| D | `Gk.edge` | `GraphFamily.lean` | The designated edge `e = v₀v_{k+2}` |
| D | `Gk.isKConnected_four` | `GraphFamily.lean` | `G_k` is 4-connected |
| D | `Gk.isPlanar` | `GraphFamily.lean` | `G_k` is planar |
| D | `Gk.cycle_count_exact` | `GraphFamily.lean` | `G_k` has exactly `2k+2` distinct cycle lengths through `e` |
| T | `malkevitch_conjecture` | `CycleSpectrum.lean` (`sorry`) | The end-goal conjecture |
| P | `triangular_faces_diagonal_ne` | `NoFourCycles.lean` (`sorry`) | Diagonal-vertex-distinctness fact used inside `triangular_faces_edge_disjoint`; extracted from an in-progress proof attempt that explored several routes without closing the goal |

All (H) and (P) entries above are `theorem foo : T := sorry` — every `axiom` in
the project other than the (D) family has been migrated to this form, with
statements preserved byte-for-byte. **Policy going forward**: new assumed facts
must always be written this way (never as a bare new `axiom`). The (D) family
is `axiom` because it axiomatizes *data* (a graph and its properties), which
cannot be written as `sorry` — see `docs/graphfamily_options.md` for the plan
to replace it with either a concrete construction or a hypothesis-bundling
`structure`.

**Note on `triangular_faces_diagonal_ne`**: the proof it was extracted from
also had a second inline goal, informally called `hbd` (`d₁.fst ≠ d₁.snd`) in
the original task brief for this cleanup. On inspection `hbd` was already
proved trivially as `d₁.adj.ne` (no `sorry`, no exploratory comments) — so
there was nothing to extract there. Only the `hac`-labelled goal
(`d₁''.fst ≠ e₂.snd`, now `triangular_faces_diagonal_ne`) was genuinely
unfinished.

## Blueprint

The blueprint (dependency graph + statements) is built with
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) from
[`blueprint/src/content.tex`](blueprint/src/content.tex) and deployed to GitHub
Pages:

* **[Home page](https://abhishan82.github.io/Pancyclicity-in-4-connected-planar-graphs/)**
* **[Blueprint](https://abhishan82.github.io/Pancyclicity-in-4-connected-planar-graphs/blueprint/)**
  / [dependency graph](https://abhishan82.github.io/Pancyclicity-in-4-connected-planar-graphs/blueprint/dep_graph_document.html)
  / [PDF](https://abhishan82.github.io/Pancyclicity-in-4-connected-planar-graphs/blueprint.pdf)
* **[API docs](https://abhishan82.github.io/Pancyclicity-in-4-connected-planar-graphs/docs/)**

## Development

This repository is based on the
[LeanProject](https://github.com/leanprover-community/LeanProject) template.
See that template's documentation for instructions on installing Lean 4,
configuring the blueprint toolchain, and GitHub Pages setup.

> **Note**: the Lake package name is `C4_free` (see `lakefile.toml`), which
> predates the repository being renamed to
> `Pancyclicity-in-4-connected-planar-graphs`. This mismatch is cosmetic but is
> tracked as a known issue rather than silently renamed.
