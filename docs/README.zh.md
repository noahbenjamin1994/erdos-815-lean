> 📁 **路径说明**：本文写于交付时的目录结构。整理成仓库后，Lake 包已上移到仓库根目录，说明文档移到 `docs/`。文中的 `lean/` = 仓库根目录；`FAITHFULNESS.md` → `docs/FAITHFULNESS.zh.md`，`ISSUE.md` → `docs/CLAIM.zh.md`。
> 仓库级说明见根目录 [`README.md`](../README.md)（英文）。

# Erdős #815 — Narins–Pokrovskiy–Szabó §2 的 Lean 4 形式化

本仓把 Narins–Pokrovskiy–Szabó, *Graphs without proper subgraphs of minimum degree 3 and
short cycles*, Combinatorica **37** (2017) 495–519, arXiv:1408.5289 的**第 2 节**证明,
完整重建为 Lean 4 机器可验证明。

最终定理(`Erdos815/Main.lean:223`):

```lean
theorem erdos_815 :
    ∃ G : ℕ → (Σ n : ℕ, SimpleGraph (Fin n)),
      (∀ i, IsDegree3Critical (G i).2) ∧
      (∀ i j, i < j → (G i).1 < (G j).1) ∧
      (∀ i, ¬ HasCycleOfLength (G i).2 23)
```

**状态:引理树全部闭合。全仓零 `sorry`、零额外公理、零 `native_decide`。**

---

## 1. Credit 声明

- **数学 credit(prover credit)完全归原作者** Lothar Narins、Alexey Pokrovskiy、
  Tibor Szabó。定理、构造、证明策略、那条周期 24 的序列,全部是论文 §2 的成果;
  本仓没有贡献任何新的数学内容。
- **本仓主张独立的 formalizer credit**:把论文 §2 的自然语言证明(含一处
  “从图上看出来”的论证和若干论文未展开的步骤)转写为 Lean 4 中内核可检查的证明项,
  并给出与原文措辞的逐条对照。
- 论文 §3(Theorem 1.3(i))与 §4(Theorem 1.4)**不在本仓范围内**,未做。

自拟陈述的忠实性风险由本仓自担。逐条对照见 `FAITHFULNESS.md` —— 那是本交付中
最应当被审阅的文件。

---

## 2. 构造回顾

给定树 `T`,`G(T)` 是在 `T` 上加两个新点 `x`、`y`、边 `xy`,以及 `{x, y}` 到 `T`
所有叶子的全部边所得的图。

`T(x₁…xₙ)`:取 `n` 点路径 `v₁…vₙ`;对 `2 ≤ i ≤ n−1`,在 `vᵢ` 上挂一棵深度 `xᵢ−1`
的完美二叉树;`i = 1` 与 `i = n` 各挂两棵。

*odd-even 序列*:`xᵢ ≡ i (mod 2)`。
*k-avoiding*:`aᵢ ≤ k/2`,且对一切 `i ≠ j` 有 `aᵢ + aⱼ + |i−j| ≠ k`。

证明链条:周期 24 的序列 `1,2,1,4,3,2,7,6,5,6,7,2,3,4,1,2,1,8,9,6,5,6,9,8` 是
20-avoiding 且 odd-even ⟹ `Tₙ = T(a₁…aₙ)` 是无长 20 leaf-leaf 路径的偶 1-3 树 ⟹
`Gₙ = G(Tₙ)` 是 degree 3-critical 且不含长 23 的圈。
`23 = 2·11 + 1` 与 `20 = 2·11 − 2` 由 Lemma 2.1(i) 锁死。

---

## 3. 引理树与文件地图

| 编号 | 内容 | Lean 名 | 文件:行 |
|---|---|---|---|
| T2.5 | 存在 20-avoiding 的 odd-even 序列 | `theorem_2_5` | `Erdos815/Sequence.lean:195` |
| P-crit | `T` 是 1-3 树 ⟹ `G(T)` 是 degree 3-critical | `gt_isDegree3Critical` | `Erdos815/GTreeCritical.lean:280` |
| L2.1(i) | `G(T)` 的长 `ℓ+3` 圈 ⟹ `T` 的长 `ℓ` leaf-leaf 路径 | `lemma_2_1_i_mp` | `Erdos815/GTreeCycles.lean:303` |
| L2.2(i) | odd-even ⟹ `T(x₁…xₙ)` 无奇长 leaf-leaf 路径 | `lemma_2_2_i` | `Erdos815/TreePaths.lean:100` |
| L2.2(ii) | `0 < m < max xᵢ` 时存在长 `2m` 的 leaf-leaf 路径 | `lemma_2_2_ii` | `Erdos815/TreePaths.lean:200` |
| L2.2(iii) | `m = max xᵢ` 的充要刻画 | `lemma_2_2_iii` | `Erdos815/TreePaths.lean:219` |
| L2.2(iv) | `m > max xᵢ` 的充要刻画 | `lemma_2_2_iv` | `Erdos815/TreePaths.lean:276` |
| T1.3(ii) | `Tₙ` 无长 20 的 leaf-leaf 路径 | `theorem_1_3_ii` | `Erdos815/Main.lean:148` |
| T1.2 | `Gₙ` 是 degree 3-critical 且无长 23 的圈 | `theorem_1_2` | `Erdos815/Main.lean:174` |
| **最终** | 论文 Theorem 1.2 的完整形式 | `erdos_815` | `Erdos815/Main.lean:223` |

论文 §2 的 Proposition 2.4(fault line)**刻意未形式化**,理由见 `FAITHFULNESS.md` 第 5 行。

### 文件职责

| 文件 | 行数 | 承担的引理 |
|---|---|---|
| `Erdos815/Defs.lean` | 262 | 全部定义层:`IsOddEvenSeq`、`IsKAvoiding`、`IsLeaf`、`IsDeg3`、`Is13Tree`、`IsLeafLeafPath`、`IsEvenTree`、`GT`(即 `G(T)`)、`IsDegree3Critical`、`TVtx`/`TTree`(即 `T(x₁…xₙ)`)、`HasCycleOfLength`。**不含任何证明义务** |
| `Erdos815/Sequence.lean` | 198 | **T2.5**。周期 24 序列 + 五组 `decide` 有限检查 + 从周期性回到 `ℤ` 上的两侧无穷陈述 |
| `Erdos815/GTreeCritical.lean` | 341 | **P-crit**。`G(T)` 的度数计算、边数 `2n−2`、每个真导出子图有度 `≤ 2` 的顶点 |
| `Erdos815/GTreeCycles.lean` | 340 | **L2.1(i) 的 ⟹ 方向**。`G(T) − xy` 二部(`gtColoring`)、奇圈必含 `xy`、剥离 `C − x − y` |
| `Erdos815/TreeBasic.lean` | 493 | `T(x₁…xₙ)` 的坐标函数 `tIdx`/`tHeight`/`tRank`、`TParams`、`IsOddEvenFin`、`idxDist` |
| `Erdos815/TreeStruct.lean` | 318 | `T(x₁…xₙ)` 是 1-3 树:连通性、无圈性(三族割函数)、每点度 1 或 3 |
| `Erdos815/TreeWalks.lean` | 278 | `T(x₁…xₙ)` 里的典范 walk(上行、跨段) |
| `Erdos815/TreeConstruct.lean` | 428 | 给定长度的 leaf-leaf 路径的**构造**机器,支撑 L2.2 的 “if” 方向 |
| `Erdos815/TreePaths.lean` | 288 | **L2.2 全四条**。分类定理 `leafLeafPath_length` + 交付接口 `lemma_2_2_iv_only_if` |
| `Erdos815/Transport.lean` | 150 | 沿图同构搬运 `IsDegree3Critical` 与 `HasCycleOfLength`,把顶点类型落到 `Fin N` |
| `Erdos815/Main.lean` | 234 | **T1.3(ii)、T1.2、`erdos_815`**。`TVtx` 的有限性、参数核对、最终组装 |
| `Erdos815/Verify.lean` | 82 | 公理验收:对 51 条定理逐条 `#print axioms` |

---

## 4. Toolchain 与依赖版本

| 项 | 值 |
|---|---|
| Lean | `leanprover/lean4:v4.34.0`(`lean-toolchain`) |
| Mathlib | `v4.34.0`,commit `5ed2965256430c3649e86755f9576b54eca72435` |
| batteries | `f2effa3d803fda822b1f97b806c47cf2adfbcbc2` |
| aesop | `355695d523e41d0554926416cba2a2b3544fbbc9` |
| plausible | `118aa17ee84656b8bd727fef7c458ee8c833385c` |
| Qq | `6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259` |
| ProofWidgets4 | `106ff4fafc74ef4ac99d81dbf3ab399118f497a5` |

完整清单见 `lean/lake-manifest.json`。库名 `Erdos815`,根模块 `lean/Erdos815.lean`。

---

## 5. 复现编译

```bash
cd lean
lake exe cache get      # 拉 Mathlib 预编译 olean
lake build              # 从零 3149 个 job,零 error
lake env lean Erdos815/Verify.lean    # 打印全部 51 条定理的公理足迹
```

机械验收(必须无输出):

```bash
grep -rnE '\bsorry\b|\bnative_decide\b|^[[:space:]]*axiom |ofReduceBool|implemented_by' \
  Erdos815 Erdos815.lean
```

本仓在一次 `rm -rf .lake/build` 的**从零重建**下验证过以上三条,`lake build` 报
`Build completed successfully (3149 jobs).`,`grep` 退出 1(无匹配)。

---

## 6. `#print axioms` 的实际输出

`lake env lean Erdos815/Verify.lean` 覆盖 51 条定理,输出里只出现三种公理组合:

```
'Erdos815.erdos_815' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos815.theorem_1_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos815.theorem_1_3_ii' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos815.theorem_2_5' depends on axioms: [propext, Quot.sound]
'Erdos815.aSeq_matches_paper' depends on axioms: [propext]
```

去重后全仓只有三种足迹:`[propext, Classical.choice, Quot.sound]`、
`[propext, Quot.sound]`、`[propext]`。

**验收口径:只允许 `propext`、`Classical.choice`、`Quot.sound`。通过。**
无 `sorryAx`(未证),无 `Lean.ofReduceBool`(编译期求值)。

`Classical.choice` 的来源已逐条查清,均属白名单内的常规用法:
`IsDegree3Critical` 定义里的 `open scoped Classical`、`GTreeCycles.lean` 的
`treeColoring`/`coColor`、`Main.lean` 的 `Fintype.ofFinite` 与 `Exists.choose`。
T2.5 一族(纯有限检查)连 `Classical.choice` 都没用上。

---

## 7. 参考

- 论文:Narins, Pokrovskiy, Szabó. *Graphs without proper subgraphs of minimum degree 3
  and short cycles.* Combinatorica 37 (2017) 495–519. https://arxiv.org/abs/1408.5289
- 问题条目:Erdős #815 / JSP-000672
- 逐条忠实性对照:见同目录 `FAITHFULNESS.md`
- 可直接贴 issue 的交付说明:见同目录 `ISSUE.md`
