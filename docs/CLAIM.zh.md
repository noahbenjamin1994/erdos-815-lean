# Erdős #815 / JSP-000672 — Narins–Pokrovskiy–Szabó §2 的 Lean 4 形式化(完成)

## 结论

Narins–Pokrovskiy–Szabó, *Graphs without proper subgraphs of minimum degree 3 and short
cycles*, Combinatorica 37 (2017) 495–519, arXiv:1408.5289 的**第 2 节**全部证明,
已重建为 Lean 4 机器可验证明:存在一族顶点数任意大的 degree 3-critical 图,
每个都不含长度 23 的圈。引理树 T2.5 / P-crit / L2.1(i) / L2.2 / T1.3(ii) / T1.2
全部闭合,**全仓零 `sorry`、零额外公理、零 `native_decide`**,在 Lean 4.34.0 +
Mathlib `5ed2965` 上从零重建通过。论文 §3(Theorem 1.3(i))与 §4(Theorem 1.4)
不在本次范围内。

最终定理:

```lean
theorem erdos_815 :
    ∃ G : ℕ → (Σ n : ℕ, SimpleGraph (Fin n)),
      (∀ i, IsDegree3Critical (G i).2) ∧
      (∀ i j, i < j → (G i).1 < (G j).1) ∧
      (∀ i, ¬ HasCycleOfLength (G i).2 23)
```

## 引理树完成状态

| 编号 | 内容 | Lean 名 | 位置 | 状态 |
|---|---|---|---|---|
| T2.5 | 周期 24 的序列 `1,2,1,4,3,2,7,6,5,6,7,2,3,4,1,2,1,8,9,6,5,6,9,8` 是 20-avoiding 的 odd-even 序列 | `theorem_2_5` | `Erdos815/Sequence.lean:195` | 闭合 |
| P-crit | `T` 是 1-3 树 ⟹ `G(T)` 是 degree 3-critical | `gt_isDegree3Critical` | `Erdos815/GTreeCritical.lean:280` | 闭合 |
| L2.1(i) | `G(T)` 的长 `ℓ+3` 圈 ⟹ `T` 的长 `ℓ` leaf-leaf 路径(`ℓ` 偶非零) | `lemma_2_1_i_mp` | `Erdos815/GTreeCycles.lean:303` | 闭合 |
| L2.2(i) | odd-even ⟹ `T(x₁…xₙ)` 无奇长 leaf-leaf 路径,即偶树 | `lemma_2_2_i` | `Erdos815/TreePaths.lean:100` | 闭合 |
| L2.2(ii) | `0 < m < max xᵢ` 时存在长 `2m` 的 leaf-leaf 路径 | `lemma_2_2_ii` | `Erdos815/TreePaths.lean:200` | 闭合 |
| L2.2(iii) | `m = max xᵢ` 时的充要刻画 | `lemma_2_2_iii` | `Erdos815/TreePaths.lean:219` | 闭合 |
| L2.2(iv) | `m > max xᵢ` 时的充要刻画 | `lemma_2_2_iv` | `Erdos815/TreePaths.lean:276` | 闭合 |
| T1.3(ii) | `Tₙ` 无长 20 的 leaf-leaf 路径 | `theorem_1_3_ii` | `Erdos815/Main.lean:148` | 闭合 |
| T1.2 | `Gₙ = G(Tₙ)` 是 degree 3-critical 且无长 23 的圈 | `theorem_1_2` | `Erdos815/Main.lean:174` | 闭合 |
| 最终 | 论文 Theorem 1.2 的完整形式 | `erdos_815` | `Erdos815/Main.lean:223` | 闭合 |

L2.2 的 (ii)、(iii) 与 (iv) 的 “if” 方向只服务论文 §3,不在 T1.2 的依赖链上,
但也一并证明了,以使全仓零 `sorry`。
论文 §2.1 的 Proposition 2.4(fault line)刻意未形式化,理由见下方“看图 ⟶ 枚举”。

## 复现步骤

```bash
# Lean 4.34.0(elan 会按 lean-toolchain 自动拉取)
cd lean
lake exe cache get
lake build                              # 3149 jobs, 0 error
lake env lean Erdos815/Verify.lean      # 打印全部 51 条定理的公理足迹
```

机械验收(必须无输出):

```bash
grep -rnE '\bsorry\b|\bnative_decide\b|^[[:space:]]*axiom |ofReduceBool|implemented_by' \
  Erdos815 Erdos815.lean
```

依赖版本:Lean `leanprover/lean4:v4.34.0`;Mathlib `v4.34.0`,commit
`5ed2965256430c3649e86755f9576b54eca72435`。完整清单见 `lean/lake-manifest.json`。
本次交付在一次 `rm -rf .lake/build` 的从零重建下验证过以上全部命令。

## `#print axioms` 输出

`Erdos815/Verify.lean` 覆盖 51 条定理。去重后全仓只有三种公理足迹:

```
'Erdos815.erdos_815' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos815.theorem_1_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos815.theorem_1_3_ii' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos815.theorem_2_5' depends on axioms: [propext, Quot.sound]
'Erdos815.aSeq_matches_paper' depends on axioms: [propext]
```

只出现 `propext` / `Classical.choice` / `Quot.sound`,无 `sorryAx`,无
`Lean.ofReduceBool`。`Classical.choice` 的来源逐条查清且均属常规:
`IsDegree3Critical` 定义里的 `open scoped Classical`、树的 2-染色构造、
`Fintype.ofFinite` 与 `Exists.choose`。T2.5 一族(纯有限检查)连 `Classical.choice`
都没用上。

## 忠实性对照(摘要)

形式化的陈述是我们自拟的,论文并未给出 Lean 代码,因此“证明通过”只保证 Lean 陈述
被证明了。逐条对照(17 处形式出入,含论文原文英文逐字引用 + Lean 代码逐字贴 + 文件行号)
见同目录 `FAITHFULNESS.md`。要点:

- **“infinite sequence” 形式化为顶点数严格递增**,而非裸的 `ℕ → …`——后者允许常序列,
  只给出一个图。严格递增蕴含两两不同构且规模任意大,**强于**论文字面陈述。
  这一点是必需的:原问题是“`n` 充分大时必含长 `k` 的圈”,反例族没有任意大的成员
  就不构成否定回答。
- **`IsDegree3Critical` 取 proper induced subgraph 版本**,与论文 §1 的澄清和 §2 的
  实际用法一致(论文标题写 "proper subgraph",§1 专门说明应读作 induced)。两种读法
  等价,`FAITHFULNESS.md` §B2 给出等价性论证:若 `H ⊆ G` 最小度 `≥ 3`,则 `G[V(H)]`
  含 `H` 全部边,最小度也 `≥ 3`。边数条件 `2 * n - 2` 用 `ℕ` 截断减法,在 `n ≥ 1` 时
  不触发截断,构造出的图 `n ≥ 3`。
- **“cycle of length 23” 用 Mathlib 的 `Walk.IsCycle` + `Walk.length`**,后者数的是
  **边数**,与论文口径一致。
- **T2.5 的原文证明是“从图上看出来”**(Figure 4 + fault line),本仓**不形式化
  Proposition 2.4**,直接按 Definition 2.3 的字面定义在内核里做 `24 × 19` 的**完全
  枚举**(`decide`,非 `native_decide`)。Prop 2.4 是 Def 2.3 为人眼检查而做的等价重述,
  绕过它不损失任何东西,而直接查定义**严格强于**看图。无穷到有限的归约(对称化、
  `d ≤ 18` 的上界、周期性)在 Lean 里逐步显式证明。
- **论文 §2 有一处真实论证缺口已补全**:把圈旋到 `x` 之后,边 `xy` 可能是**末边**而非
  首边,论文未提及;本仓用 `C.reverse` 补上(`cycle_cons_xy`),未引入新假设。
- **论文的三处记号笔误已核对**:Def 2.3 的 `(xᵢ)` vs `aᵢ`;构造段的 `T₁^{(1)}` 应为
  `T₁^{(2)}`;T2.5 写 `aᵢ ≤ 10` 而该序列实际最大值是 **9**(T1.3(ii) 用的正是 9,
  即 `20 > 2·9 = 18`)。本仓两条界都证。
- **范围取舍(已标注,不进入最终定理依赖链)**:L2.1 只做 T1.2 需要的 ⟹ 方向;
  L2.2(ii) 的下界写成 `1 ≤ m` 而非 `0 ≤ m`(`m = 0` 对应起讫同一片叶子的平凡路径,
  被“两叶相异”的定义排除);§3、§4 未做。

本仓**不主张** “23 是最优的”这类论断——那属于论文 §3,不在本次范围。

## Credit

- **数学 credit(prover credit)完全归原作者** Lothar Narins、Alexey Pokrovskiy、
  Tibor Szabó。定理、构造、证明策略与那条周期 24 的序列均为论文 §2 的成果,
  本次交付没有贡献任何新的数学内容。
- **本次交付主张独立的 formalizer credit**:把 §2 的自然语言证明(含一处“从图上看出来”
  的论证、一处论文未提的情形,以及若干论文用 "Notice that" 一句带过、Lean 里需数百行
  的步骤)转写为内核可检查的证明项,并提供与原文措辞的逐条对照。
- 自拟陈述的忠实性风险由本次交付自担,对照见 `FAITHFULNESS.md`。

## 文件

- `lean/` — Lean 4 工程(库名 `Erdos815`,根模块 `lean/Erdos815.lean`,12 个源文件约 3400 行)
- `README.md` — 仓库说明、文件地图、toolchain 与复现命令
- `FAITHFULNESS.md` — 逐条忠实性对照(**本次交付最应被审阅的文件**)
