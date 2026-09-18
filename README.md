# Erdős 815 — a Lean 4 formalisation of the counterexample

[![Lean](https://img.shields.io/badge/Lean-4.34.0-blue)](lean-toolchain)
[![Mathlib](https://img.shields.io/badge/Mathlib-5ed2965-blue)](lake-manifest.json)
[![sorry-free](https://img.shields.io/badge/sorry-0-brightgreen)](#verification)
[![axioms](https://img.shields.io/badge/axioms-standard%203%20only-brightgreen)](Erdos815/Verify.lean)

A machine-checked Lean 4 proof of **§2 of Narins–Pokrovskiy–Szabó**,
*Graphs without proper subgraphs of minimum degree 3 and short cycles*,
Combinatorica **37** (2017) 495–519 ([arXiv:1408.5289](https://arxiv.org/abs/1408.5289)),
which answers [Erdős Problem 815](https://www.erdosproblems.com/815) in the **negative**.

Prize ledger entry: **JSP-000672** (`TheJustinSunPrize/awards`).

---

## Documents

| Document | What it is |
|---|---|
| [`docs/FAITHFULNESS.zh.md`](docs/FAITHFULNESS.zh.md) | **Read this first.** 17 rows comparing the paper's English wording with the Lean code, line by line, with a verdict on every difference |
| [`docs/README.zh.md`](docs/README.zh.md) | Original Chinese repository notes: construction, file map, lemma tree, build instructions |
| [`docs/CLAIM.md`](docs/CLAIM.md) | The award claim, posted as [awards#1020](https://github.com/TheJustinSunPrize/awards/issues/1020) |
| [`docs/CLAIM.zh.md`](docs/CLAIM.zh.md) | The Chinese original the claim was written from |

## The question and the answer

> Let `k ≥ 3` and `n` be large. If a graph `G` has `n` vertices and `2n − 2` edges and every
> proper induced subgraph has a vertex of degree ≤ 2 (*degree 3-critical*), must `G` contain a
> cycle of length `k`?

**No.** There are infinitely many degree 3-critical graphs containing **no cycle of length 23**
(paper Theorem 1.2).

The construction chain, all of it finite combinatorics:

1. `G(T)` — given a tree `T`, add two vertices `x, y`, the edge `xy`, and all edges from
   `{x, y}` to the leaves of `T`. If `T` is a 1-3 tree then `G(T)` is degree 3-critical.
2. `T(x₁…xₙ)` — take a path `v₁…vₙ` and hang a perfect binary tree of depth `xᵢ − 1` at each
   `vᵢ` (two of them at each end).
3. The period-24 sequence `1,2,1,4,3,2,7,6,5,6,7,2,3,4,1,2,1,8,9,6,5,6,9,8` is *odd-even* and
   *20-avoiding* (paper Theorem 2.5), so `Tₙ` has no leaf-to-leaf path of length 20 and
   `Gₙ = G(Tₙ)` has no cycle of length 23. Lemma 2.1(i) locks `23 = 2·11 + 1` to `20 = 2·11 − 2`.

The paper proves Theorem 2.5 by reading a *fault line* off a figure. Here it is a complete
`24 × 19` enumeration against the literal Definition 2.3, run inside the kernel by `decide` —
strictly stronger than looking at the picture, and the reduction from the infinite statement
(symmetrisation, the `d ≤ 18` bound, periodicity) is proved explicitly rather than assumed.

## The top-level theorem

[`Erdos815/Main.lean:223`](Erdos815/Main.lean) — verbatim:

```lean
theorem erdos_815 :
    ∃ G : ℕ → (Σ n : ℕ, SimpleGraph (Fin n)),
      (∀ i, IsDegree3Critical (G i).2) ∧
      (∀ i j, i < j → (G i).1 < (G j).1) ∧
      (∀ i, ¬ HasCycleOfLength (G i).2 23)
```

The statement is **self-authored** — `formal-conjectures` has no statement for this problem —
so its fidelity is this repository's own risk. [`docs/FAITHFULNESS.zh.md`](docs/FAITHFULNESS.zh.md)
is a 17-row table quoting the paper's English wording against the Lean code line by line, and
it is **the file a reviewer should read first**. Summary of the points that matter:

- *"infinite sequence"* is formalised as **strictly increasing vertex count**, not a bare
  `ℕ → …`. The bare version admits a constant sequence, i.e. a single graph; strict growth
  implies pairwise non-isomorphic and unbounded size, which is what the negative answer needs.
  This is **stronger** than the paper's literal wording, not weaker.
- `IsDegree3Critical` uses **proper induced** subgraphs, matching the paper's own §1 clarification
  that "proper subgraph" is to be read as induced; the equivalence is argued in the fidelity table.
- *"cycle of length 23"* is Mathlib's `Walk.IsCycle` with `Walk.length`, which counts **edges**,
  as the paper does.
- One genuine gap in the paper's argument is closed here: after rotating a cycle to `x`, the edge
  `xy` may be the *last* edge rather than the first; handled via `C.reverse`, no new hypothesis.
- Three typographical slips in the paper were cross-checked (`(xᵢ)` vs `aᵢ` in Def 2.3;
  `T₁^{(1)}` should be `T₁^{(2)}`; Theorem 2.5 writes `aᵢ ≤ 10` where the sequence's maximum is
  in fact **9** — both bounds are proved here).

## Verification

```bash
lake exe cache get
lake build                              # 3149 jobs, 0 errors
lake env lean Erdos815/Verify.lean      # axiom footprint of all 51 theorems
```

Mechanical acceptance — must print nothing:

```bash
grep -rnE '\bsorry\b|\bnative_decide\b|^[[:space:]]*axiom |ofReduceBool|implemented_by' \
  Erdos815 Erdos815.lean
```

[`Erdos815/Verify.lean`](Erdos815/Verify.lean) covers 51 theorems; after de-duplication the
whole repository shows only these footprints:

```
'Erdos815.erdos_815'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos815.theorem_1_2'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos815.theorem_1_3_ii'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos815.theorem_2_5'       depends on axioms: [propext, Quot.sound]
'Erdos815.aSeq_matches_paper' depends on axioms: [propext]
```

No `sorryAx`, no `Lean.ofReduceBool`. Each use of `Classical.choice` was traced and is routine
(`open scoped Classical` in the definition of `IsDegree3Critical`, the 2-colouring of a tree,
`Fintype.ofFinite`, `Exists.choose`). The Theorem 2.5 family — pure finite checking — does not
use it at all. The delivery was verified after a `rm -rf .lake/build` rebuild from scratch.

Environment: Lean `leanprover/lean4:v4.34.0`, Mathlib tag `v4.34.0`, commit
`5ed2965256430c3649e86755f9576b54eca72435`; full pin set in [`lake-manifest.json`](lake-manifest.json).

The raw output of one such clean run is committed under
[`verification/`](verification/README.md): [`build.log`](verification/build.log),
[`axioms.log`](verification/axioms.log) with all 51 audited theorems,
[`scan.log`](verification/scan.log) and [`CHECKSUMS.txt`](verification/CHECKSUMS.txt), so a
reviewer can diff against their own run rather than take the numbers above on trust.

## Credit

The mathematics is due to **Lothar Narins, Alexey Pokrovskiy and Tibor Szabó** — the theorem,
the construction, the proof strategy and that period-24 sequence are all §2 of their paper.
**Prover credit belongs entirely to them.** This repository contains no new mathematics.

What is claimed here is the independent **formalizer credit**: turning the prose proof — including
one argument the paper reads off a figure, one case it does not mention, and several steps
dismissed with "Notice that" that take hundreds of lines in Lean — into kernel-checked proof terms,
plus the line-by-line fidelity table.

### Formalization authors

**Formalization authors:** [noahbenjamin1994](https://github.com/noahbenjamin1994) (Apevon Science). The Lean development was produced with AI assistance. The proof and the fidelity table were generated by an Apevon Science automated agent run on 2026-09-17, then reviewed, built against the pinned toolchain, and published under this account. Full statement in [`AUTHORS.md`](AUTHORS.md).

## Layout

```
Erdos815.lean                   root module
Erdos815/
  Defs.lean               262   all definitions: G(T), T(x₁…xₙ), IsDegree3Critical, k-avoiding …
  Sequence.lean           198   Theorem 2.5 — the period-24 sequence is 20-avoiding
  GTreeCritical.lean      341   T a 1-3 tree ⟹ G(T) degree 3-critical
  GTreeCycles.lean        340   Lemma 2.1(i), forward direction
  TreeBasic.lean          493   coordinates on T(x₁…xₙ)
  TreeStruct.lean         318   T(x₁…xₙ) is a 1-3 tree: connected, acyclic, degrees 1 or 3
  TreeWalks.lean          278   walks and paths in T(x₁…xₙ)
  TreeConstruct.lean      428   explicit leaf-to-leaf path constructions
  TreePaths.lean          288   Lemma 2.2, all four parts
  Transport.lean          150   transporting the conclusion along a graph isomorphism to `Fin N`
  Main.lean               234   Theorem 1.3(ii), Theorem 1.2, `erdos_815`
  Verify.lean              82   axiom audit
docs/                           Chinese README, fidelity table, claim draft
```

## Lemma map

| Paper | Lean | File:line |
|---|---|---|
| Theorem 2.5 | `theorem_2_5` | `Sequence.lean:195` |
| `T` a 1-3 tree ⟹ `G(T)` degree 3-critical | `gt_isDegree3Critical` | `GTreeCritical.lean:280` |
| Lemma 2.1(i) | `lemma_2_1_i_mp` | `GTreeCycles.lean:303` |
| Lemma 2.2(i)–(iv) | `lemma_2_2_i` … `lemma_2_2_iv` | `TreePaths.lean:100,200,219,276` |
| Theorem 1.3(ii) | `theorem_1_3_ii` | `Main.lean:148` |
| Theorem 1.2 | `theorem_1_2` | `Main.lean:174` |
| Theorem 1.2, full form | `erdos_815` | `Main.lean:223` |

## Scope

Only **§2** of the paper is formalised — that is all Theorem 1.2 needs. §3 (Theorem 1.3(i), the
hard direction) and §4 (Theorem 1.4) are **not** done, and **no claim is made that 23 is optimal**;
that is §3. Proposition 2.4 (the fault line) is deliberately not formalised: it is the paper's
restatement of Definition 2.3 for human inspection, and checking the definition directly is
strictly stronger. Lemma 2.1 is proved only in the direction Theorem 1.2 uses; parts (ii)–(iv) of
Lemma 2.2 serve §3 and are off the final theorem's dependency chain but are proved anyway so that
the repository is `sorry`-free.

## References

- Narins, Pokrovskiy, Szabó, *Graphs without proper subgraphs of minimum degree 3 and short
  cycles*, Combinatorica 37 (2017) 495–519, [arXiv:1408.5289](https://arxiv.org/abs/1408.5289).
- [Erdős Problem 815](https://www.erdosproblems.com/815)
- [`docs/FAITHFULNESS.zh.md`](docs/FAITHFULNESS.zh.md) — statement fidelity, the file to review first
- [`docs/CLAIM.md`](docs/CLAIM.md) — draft of the `[Recipient]` issue for `TheJustinSunPrize/awards`

## License

Apache-2.0, see [`LICENSE`](LICENSE).
