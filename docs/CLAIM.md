# Draft `[Recipient]` issue — JSP-000672 (Erdős 815)

**Posted 2026-09-18 as [TheJustinSunPrize/awards#1020](https://github.com/TheJustinSunPrize/awards/issues/1020).**
The Chinese original this was written from is [`CLAIM.zh.md`](CLAIM.zh.md).

---

**Title:** `[Recipient] JSP-000672 — Lean 4 formalization of Erdős 815 (formalizer)`

**Body:**

This is a **formalizer** claim for JSP-000672 (Erdős 815). It is not a claim on the prover side.

### What is being claimed

A complete Lean 4 formalization of **§2** of Narins–Pokrovskiy–Szabó, *Graphs without proper
subgraphs of minimum degree 3 and short cycles*, Combinatorica 37 (2017) 495–519,
arXiv:1408.5289 — there are degree 3-critical graphs of arbitrarily large order containing no
cycle of length 23, which answers Erdős 815 in the negative.

Repository: https://github.com/noahbenjamin1994/erdos-815-lean. Lean `v4.34.0`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, both pinned in the repository.

### Statement

```lean
theorem erdos_815 :
    ∃ G : ℕ → (Σ n : ℕ, SimpleGraph (Fin n)),
      (∀ i, IsDegree3Critical (G i).2) ∧
      (∀ i j, i < j → (G i).1 < (G j).1) ∧
      (∀ i, ¬ HasCycleOfLength (G i).2 23)
```

`formal-conjectures` has no statement for this problem, so the statement above is **ours**, and
its fidelity is our own risk. `docs/FAITHFULNESS.zh.md` in the repository is a 17-row table
quoting the paper's English wording against the Lean code with file and line references. The
points a reviewer is most likely to question:

- *"infinite sequence"* is rendered as strictly increasing vertex count rather than a bare
  `ℕ → …`, because the bare version is satisfied by a constant sequence — a single graph. Strict
  growth gives pairwise non-isomorphic graphs of unbounded size, which is what a negative answer
  to "for all sufficiently large `n`" requires. This is stronger than the paper's literal wording.
- `IsDegree3Critical` quantifies over **proper induced** subgraphs, following the paper's own §1
  note that "proper subgraph" is to be read as induced. The equivalence of the two readings is
  argued in the table (§B2).
- "cycle of length 23" is Mathlib's `Walk.IsCycle` with `Walk.length`, which counts edges, as in
  the paper.

### How to verify

```bash
lake exe cache get
lake build                              # 3149 jobs, 0 errors
lake env lean Erdos815/Verify.lean      # axiom footprint of all 51 theorems

grep -rnE '\bsorry\b|\bnative_decide\b|^[[:space:]]*axiom |ofReduceBool|implemented_by' \
  Erdos815 Erdos815.lean                # no output
```

De-duplicated axiom footprints for the whole repository:

```
'Erdos815.erdos_815'          depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos815.theorem_1_2'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos815.theorem_1_3_ii'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos815.theorem_2_5'        depends on axioms: [propext, Quot.sound]
'Erdos815.aSeq_matches_paper' depends on axioms: [propext]
```

No `sorryAx`, no `native_decide`, no `Lean.ofReduceBool`. Verified after a
`rm -rf .lake/build` rebuild from scratch.

### Relationship to existing work

The theorem, the construction, the proof strategy and the period-24 sequence are all §2 of the
paper by Lothar Narins, Alexey Pokrovskiy and Tibor Szabó. **Prover credit belongs to them; this
claim is for formalizer credit only.** No new mathematics is contributed.

Three things the formalization does beyond transcription, all recorded in the repository:

- Theorem 2.5 is proved in the paper by reading a *fault line* off a figure. Here it is a complete
  `24 × 19` enumeration against the literal Definition 2.3, by `decide` inside the kernel (not
  `native_decide`), with the reduction from the infinite statement proved explicitly.
- One real gap in the paper's argument is closed: after rotating a cycle to `x`, the edge `xy` may
  be the last edge rather than the first. Handled with `C.reverse`; no new hypothesis.
- Three typographical slips were cross-checked, including Theorem 2.5 writing `aᵢ ≤ 10` where the
  sequence's maximum is 9. Both bounds are proved.

### Scope

Only §2 is formalized — that is all Theorem 1.2 needs. §3 (Theorem 1.3(i)) and §4 (Theorem 1.4)
are **not** done, and **no claim is made that 23 is optimal**; that is §3. Proposition 2.4 (the
fault line) is deliberately not formalized: it is a restatement of Definition 2.3 for human
inspection, and checking the definition directly is strictly stronger.

---

## Pre-submission checklist

- [x] Pushed public 2026-09-18T04:05Z.
- [x] Competition state checked 2026-09-18T03:56Z: nothing found on any of the three channels.
- [ ] Consider opening a statement PR against `formal-conjectures` first, so a third party reviews
      the statement before the claim rests on it.
- [x] Posted on its own.
