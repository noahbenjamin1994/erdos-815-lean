# 忠实性对照:自拟 Lean 陈述 vs 论文原文

本文件逐条对照 Narins–Pokrovskiy–Szabó, arXiv:1408.5289 §2(及 §1 中 §2 要用的定义)
的**英文原文措辞**与本仓 Lean 陈述的**逐字代码**。

**为什么需要这份文件**:形式化的陈述是我们自拟的,论文并未给出 Lean 代码。
因此“证明通过”只保证 Lean 陈述被证明了,不保证 Lean 陈述就是论文说的那件事。
后者的风险由本仓自担,只能靠逐条对照来降低。所有行号对应本仓 `lean/` 目录下的文件。

判读约定:**差异栏写“无”表示逐字同义**;凡有任何形式上的出入,都单列理由,
并说明它是否削弱了陈述。全表 17 行,**没有一行是削弱**。

---

## A. 最终定理

### A1. Theorem 1.2 的整体形态

**论文原文(Theorem 1.2):**

> There is an infinite sequence of degree 3-critical graphs `(Gₙ)^∞_{n=1}` which do not
> contain a cycle of length 23.

**Lean 陈述(`Erdos815/Main.lean:223`):**

```lean
theorem erdos_815 :
    ∃ G : ℕ → (Σ n : ℕ, SimpleGraph (Fin n)),
      (∀ i, IsDegree3Critical (G i).2) ∧
      (∀ i j, i < j → (G i).1 < (G j).1) ∧
      (∀ i, ¬ HasCycleOfLength (G i).2 23)
```

**差异与理由:**

1. `(Gₙ)^∞_{n=1}` ⟶ `G : ℕ → (Σ n : ℕ, SimpleGraph (Fin n))`。每个 `Gᵢ` 顶点数不同,
   必须用 `Σ` 把顶点数打包进类型;`Fin n` 顺带给出 `Fintype`,使 `edgeFinset.card`
   有意义。
2. **“infinite sequence” ⟶ 顶点数严格递增**(`∀ i j, i < j → (G i).1 < (G j).1`)。
   这是本表最需要辩护的一处。裸写 `G : ℕ → …` **不够**:常序列 `Gᵢ = G₀` 也是
   `ℕ → …` 的函数,却只给出一个图。顶点数严格递增蕴含两件事,恰是论文 “infinite
   sequence” 的全部内容:(a) 所有 `Gᵢ` 两两不同构(顶点数互不相同);(b) 规模任意大
   (`(G i).1 ≥ (G 0).1 + i`)。这**强于**论文的字面陈述,不弱于。
3. 长度 23 未改,`IsDegree3Critical` 未改。

### A2. “infinite” 的实现:给出的是原族的子列

**实现方式(`Erdos815/Main.lean:100`、`Main.lean:212`):**

```lean
lemma card_TVtx_ge : n ≤ Fintype.card (TVtx x n)

noncomputable def pickIdx : ℕ → ℕ
  | 0 => (famG_unbounded 0).choose
  | (m + 1) => (famG_unbounded (famG (pickIdx m)).1).choose
```

**差异与理由:** 论文的 `Tₙ` 顶点数本来就随 `n` 严格递增。Lean 里直接证这一点需要
精确计数公式(要数完美二叉树的结点数 `2^{xᵢ} − 1` 再对下标求和),是纯额外工作量。
改为先证顶点数**无上界**(`card_TVtx_ge`:主路径的 `n` 个点给出 `Fin n ↪ TVtx x n`),
再贪心选下标取出严格递增的子列。

**这不是削弱**,三条理由:(1) 最终陈述 `∀ i j, i < j → (G i).1 < (G j).1` 一字未改,
给出的函数确实对一切 `i < j` 严格递增;(2) 子列的**每个成员**都是论文那个构造
`G(T(a₁…aₙ))` 的成员,没有换构造、没有换序列、没有放宽前提;(3) 无穷序列的无穷子列
仍是无穷序列,A1 里论证的两件事在子列上同样成立。
**代价**:无法从 `erdos_815` 反读出“第 `i` 个图恰有多少顶点”——而论文本身也没给这个公式。

### A3. 顶点类型的搬运

**实现方式(`Erdos815/Transport.lean:87`、`Transport.lean:131`):**

```lean
theorem IsDegree3Critical.of_iso [Fintype V] [Fintype W] (f : G ≃g H)
    (hG : IsDegree3Critical G) : IsDegree3Critical H

noncomputable def finGraph [Fintype V] (G : SimpleGraph V) : Σ n : ℕ, SimpleGraph (Fin n)
```

**差异与理由:** 构造出的图顶点类型是 `TVtx xA n ⊕ Bool`,而最终陈述要求 `Fin N`。
二者同构,但 Lean 里性质不自动搬运,必须显式证“同构保持 degree 3-critical 和
含长 `ℓ` 的圈”。这是**纯实现层**的工作,论文根本不会提及。陈述不受影响。

---

## B. degree 3-critical

### B1. 定义本身

**论文原文(§1):**

> a graph `G` with `n` vertices and `2n − 2` edges such that every proper induced
> subgraph of `G` has minimum degree at most 2.

**Lean 陈述(`Erdos815/Defs.lean:162`):**

```lean
open scoped Classical in
def IsDegree3Critical {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  G.edgeFinset.card = 2 * Fintype.card V - 2 ∧
  ∀ s : Set V, s.Nonempty → s ≠ Set.univ → ∃ v : s, (G.induce s).degree v ≤ 2
```

**差异与理由:** 三处形式选择,均不改变语义。

1. **`2 * n - 2` 是 `ℕ` 的截断减法**。`n ≥ 1` 时 `2n ≥ 2`,不触发截断,语义无歧义;
   `n = 0` 时论文的 `2n − 2 = −2` 本就无意义,而截断给出 `0`——但我们构造的图
   `n ≥ 3`,永远落在安全区,`erdos_815` 里每个成员都满足。不改用 `ℤ` 是为了避免
   `edgeFinset.card` 处处做 cast。
2. **“minimum degree at most 2” ⟶ “存在一个顶点度 ≤ 2”**。避免引入 `minDegree`
   及其 `Nonempty` 侧条件;在 `s.Nonempty` 前提下二者等价。
3. **`s.Nonempty` 侧条件**:空集上的导出子图没有顶点,谈不上最小度;论文语境里也不把
   空图算作子图。不加这条命题会因空集而假。

### B2. proper subgraph vs proper **induced** subgraph

**论文原文(§1,作者自己的澄清):**

> In addition, one can check that all the results and proofs given in [3] concerning
> graphs with "no proper subgraphs of minimum degree 3" hold also for graphs with
> "no proper induced subgraphs of minimum degree 3". Therefore, it is plausible to
> assume that the word "induced" should be present in the statement of Conjecture 1.1.
> [...] Consequently throughout most of this paper will study Conjecture 1.1 as it is
> stated above.

**Lean 陈述:** `∀ s : Set V, … → ∃ v : s, (G.induce s).degree v ≤ 2`——即
**proper induced subgraph** 版本,与论文标题的 "proper subgraph" 相对。

**差异与理由:** 论文标题用 "proper subgraphs",但 §1 有整段澄清说 §2 用的是
**induced** 版本,我们与论文 §2 的实际用法一致。

**两种读法给出同一个图类**(等价性论证):
设 `H ⊆ G` 是最小度 `≥ 3` 的子图(不必导出),令 `s = V(H)`。`G` 在 `s` 上的导出子图
`G[s]` 包含 `H` 的**全部**边(导出子图收下两端都在 `s` 里的所有边,`H` 的边都是这种),
故对每个 `v ∈ s` 有 `deg_{G[s]}(v) ≥ deg_H(v) ≥ 3`,即 `G[s]` 也是最小度 `≥ 3` 的子图,
且同为真子图(顶点集相同)。反方向平凡:导出子图本身就是子图。
故“存在最小度 ≥ 3 的真子图”⟺“存在最小度 ≥ 3 的真导出子图”,取否定即得两个定义等价。

**选 induced 的额外好处**:导出子图由顶点集 `s : Set V` 唯一决定,Lean 里只需对 `s`
量化;而“所有子图”是更笨重的对象(要同时量化顶点集和边集)。

### B3. P-crit 本身

**论文原文(§2):**

> Notice that if `T` is a 1-3 tree then `G(T)` is degree 3-critical.

**Lean 陈述(`Erdos815/GTreeCritical.lean:280`):**

```lean
theorem gt_isDegree3Critical {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hT : Is13Tree G) : IsDegree3Critical (GT G)
```

**差异与理由:** 无。论文用 "Notice that" 一句带过;Lean 里这是 341 行,
含边数计数(经握手引理与叶子数公式 `Is13Tree.two_mul_card_leafFinset`)与
真导出子图的逐情形讨论——论文完全没写这两块。

---

## C. 圈与长度

### C1. "cycle of length 23"

**论文原文(Theorem 1.2):** `... which do not contain a cycle of length 23.`

**Lean 陈述(`Erdos815/Defs.lean:259`):**

```lean
def HasCycleOfLength (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = ℓ
```

**差异与理由:** Mathlib 没有裸的 `SimpleGraph.Cycle` 类型,圈一律写成“存在起点 `v`
与闭迹 `c : G.Walk v v`,`c.IsCycle` 且 `c.length = ℓ`”。关键点:
**`Walk.length` 数的是边数**,与论文“长度 23 的圈”是同一个计数口径(23 条边、
23 个顶点),不是顶点数减一之类的偏移。`SimpleGraph.Walk.IsCycle` 是 Mathlib 的标准
定义(闭迹、边无重复、去头后支撑集无重复、长度 `≥ 3`),不是我们自拟的。

### C2. Lemma 2.1(i) 的形状改写

**论文原文(Lemma 2.1(i)):**

> The graph `G(T)` contains a cycle of length `2k + 1` ⟺ `T` contains a leaf-leaf
> path of length `2k − 2`.

**Lean 陈述(`Erdos815/GTreeCycles.lean:303`):**

```lean
theorem lemma_2_1_i_mp (hT : G.IsTree) (he : IsEvenTree G) {ℓ : ℕ}
    (hℓ : Even ℓ) (hℓ0 : ℓ ≠ 0) (h : HasCycleOfLength (GT G) (ℓ + 3)) :
    HasLeafLeafPath G ℓ
```

**差异与理由:** 三处,均不削弱本链路使用的结论。

1. **只做 ⟹ 方向**。T1.2 只需要“有 23-圈 ⟹ 有长 20 的 leaf-leaf 路径”的逆否。
   ⟸ 方向(把路径加 `x`、`y` 三条边接成圈)论文有,本链路不用,未做。
   这是**范围**上的取舍,不是对已证内容的削弱。
2. **`2k + 1` / `2k − 2` ⟶ `ℓ + 3` / `ℓ`(`ℓ` 偶)**。纯粹为避开 `ℕ` 的截断减法:
   写 `2k − 2` 会把 `k = 0, 1` 的退化情形混进来(截断成 `0`),而论文写 `2k − 2` 时
   隐含 `k ≥ 1`。令 `ℓ = 2k − 2`,二者在 `k ≥ 2` 时逐字同义。
3. **`ℓ ≠ 0` 是必需的,不是偷懒**。`ℓ = 0` 对应 3-圈 `x–y–leaf–x`,它给出的
   “长 0 的 leaf-leaf 路径”两端是同一个点,不满足 `IsLeafLeafPath` 的 `u ≠ v`。
   论文写 `2k − 2` 时同样默认 `k ≥ 2`。本链路只用 `ℓ = 20`,不受影响。

**交付接口(`Erdos815/GTreeCycles.lean:335`)把这三点吸收掉,形状与论文一致:**

```lean
theorem no_cycle_23_of_no_leaf_path_20 (hT : Is13Tree G) (he : IsEvenTree G)
    (h20 : ¬ HasLeafLeafPath G 20) : ¬ HasCycleOfLength (GT G) 23
```

### C3. 论文一句话背后的两处缺口(本仓补上)

**论文原文:**

> So `C` must contain the edge `xy` and hence `C − x − y` must be a leaf-leaf path of
> length `2k − 2` as required.

**差异与理由:** `C − x − y` 的剥离在 Lean 里是四步手术,不是一句话:把圈旋到 `x`
(`Walk.rotate`)、剥 `x→y`、剥 `y→a`、反过来剥 `x→b`,再把余下的 `r : b ⇝ a` 降回 `T`。

更要紧的是:**论文完全没提“旋到 `x` 之后 `xy` 可能是末边而非首边”**。补法是改用
`C.reverse`(同为圈、同长,首边即 `xy`),依据是“圈里含 `x` 的边只有首、末两条”。
见 `cycle_cons_xy`(`Erdos815/GTreeCycles.lean:249`)。这是 §2 叙述中**唯一**一处
本仓认定有真实论证缺口的地方,已在 Lean 里独立补全,未引入任何新假设。

---

## D. 树的概念

### D1. even tree

**论文原文(§1):**

> A tree is called *even* if all of its leaves are in the same class of the tree's unique
> bipartition.

**Lean 陈述(`Erdos815/Defs.lean:85`):**

```lean
def IsEvenTree (G : SimpleGraph V) : Prop :=
  ∀ (u v : V) (p : G.Walk u v), IsLeafLeafPath G p → p.length % 2 = 0
```

**差异与理由:** 采用等价刻画“任意两叶之间的路径长为偶”。等价性:二部图里两点同色
⟺ 它们之间的路径长为偶(Mathlib `Coloring.even_length_iff_congr`),而树中两点间路径
唯一,故两个定义给出同一个树类。好处是不必先构造出那个二部划分。
需要划分的地方(L2.1 的 `G(T) − xy` 二部)在 `GTreeCycles.lean` 里现造
(`gtColoring`),靠 `leaf_color_eq` 把路径形式翻回“所有叶子同色”——这正是当初
选路径形式时预留的接口。

### D2. 1-3 tree

**论文原文(§1):**

> a tree is called a *1-3-tree* if every vertex has degree 1 or 3.

**Lean 陈述(`Erdos815/Defs.lean:54`、`Defs.lean:64`):**

```lean
def IsLeaf (G : SimpleGraph V) (v : V) : Prop := ∃! w, G.Adj v w

structure Is13Tree (G : SimpleGraph V) : Prop where
  isTree : G.IsTree
  deg : ∀ v : V, IsLeaf G v ∨ IsDeg3 G v
```

**差异与理由:** “度为 1” 写成 `∃! w, G.Adj v w`(恰有一个邻居),“度为 3” 写成
邻居集恰含三个互异元素(`IsDeg3`)。理由:不需要 `Fintype V` / `DecidableRel G.Adj`
实例——我们要构造的图在这些实例上要额外操心。有限图上这与 `G.degree v = 1` / `= 3`
等价,等价性在 `GTreeCritical.lean:82` / `:87` 显式证明并在计数时使用。

### D3. leaf-leaf path

**论文原文(§1):** `the lengths of paths going between two leaves`

**Lean 陈述(`Erdos815/Defs.lean:72`):**

```lean
def IsLeafLeafPath {u v : V} (G : SimpleGraph V) (p : G.Walk u v) : Prop :=
  p.IsPath ∧ IsLeaf G u ∧ IsLeaf G v ∧ u ≠ v
```

**差异与理由:** 显式要求 `u ≠ v`(两片**相异**的叶子)。论文写 "between two leaves"
读作两片叶子,且 Lemma 2.1 的用法要求相异(见 C2 第 3 点)。
唯一受影响的是 Lemma 2.2(ii) 的下界,见 E3。

---

## E. Lemma 2.2

### E1. 与原文的证明路线差异:(i) 不走分类

**论文原文(Lemma 2.2 证明):**

> Note also that all these paths have even length (`xᵢ + j − i + xⱼ` is even because
> `(x₁, . . . , xₙ)` is an odd-even sequence), and so (i) holds.

**Lean 陈述(`Erdos815/TreePaths.lean:100`、`TreePaths.lean:113`):**

```lean
theorem lemma_2_2_i (hp : TParams x n) (hoe : IsOddEvenFin x n) …
theorem TTree_isEvenTree (hp : TParams x n) (hoe : IsOddEvenFin x n) :
    IsEvenTree (TTree x n)
```

**差异与理由:** 论文由三分类逐类验算奇偶得到 (i);我们改用显式分级函数
`tRank := tIdx + tHeight`,它在**每条边上恰好变化 1**,故 `tRank % 2` 是真 2-染色;
叶子的 rank 恒为 `i + xᵢ`,odd-even 条件使它恒为奇数 ⟹ 所有叶子同色 ⟹ 任意
leaf-leaf 路径长为偶。结论完全相同,证明更短,且让 (i) 与整套路径分类**解耦**。

### E2. 分类定理压成两档

**论文原文(Lemma 2.2 证明的三分类):** 交为空 / 交为单点 / 交为线段 `vᵢ…vⱼ`。

**Lean 陈述(`Erdos815/TreePaths.lean:156`):**

```lean
theorem leafLeafPath_length (hp : TParams x n)
    {u v : TVtx x n} (p : (TTree x n).Walk u v) (hpp : IsLeafLeafPath (TTree x n) p) :
    (tIdx u.val = tIdx v.val ∧ p.length ≤ 2 * x ((tIdx u.val : ℕ))) ∨
    (tIdx u.val ≠ tIdx v.val ∧
      p.length = x ((tIdx u.val : ℕ)) + x ((tIdx v.val : ℕ)) +
        idxDist (tIdx u.val) (tIdx v.val))
```

**差异与理由:** 论文的前两类(交为空、交为单点)合并为“同块”一档,且**只给上界**
`≤ 2xᵢ`;论文第三类(交为线段)是“异块”一档,给**精确值** `xᵢ + xⱼ + |i−j|`。
同块档只需上界,因为 (iv) 的 only-if 只用它来排除该档(`2m > 2·max xᵢ ≥ 2xᵢ`);
只要上界就不必构造最短路——无圈图里 `path.length ≤ walk.length` 即可,省掉整套
完美二叉树的 LCA 引理。**异块档保留等号**,因为 (iv) 的产物需要精确的
`xᵢ + xⱼ + |i−j|`。信息量对本链路无损失。

### E3. Lemma 2.2(ii) 的下界

**论文原文(Lemma 2.2(ii)):**

> For every integer `m`, `0 ≤ m < maxⁿ_{i=1} xᵢ`, the tree `T(x₁ . . . xₙ)` contains a
> leaf-leaf path of length `2m`.

**Lean 陈述(`Erdos815/TreePaths.lean:200`):** 下界写成 `1 ≤ m`,不是 `0 ≤ m`。

**差异与理由:** `m = 0` 对应长度 0 的 leaf-leaf 路径,即起讫为**同一片**叶子的平凡
路径;`IsLeafLeafPath` 要求两端相异(D3),故排除。这是定义口径的直接后果,
不是漏证。**本链路(T1.3(ii) → T1.2)只用 (i) 与 (iv) 的 only-if,不用 (ii)**,
故这处出入不进入最终定理的依赖链。(ii) 仍按原文其余部分陈述并已证明。

### E4. (iv) only-if 不需要 odd-even 假设

**论文原文:** 四条 (i)–(iv) 统一置于 "Let `x₁, . . . , xₙ` be an odd-even sequence" 之下。

**Lean 陈述(`Erdos815/TreePaths.lean:178`):**

```lean
theorem lemma_2_2_iv_only_if (hp : TParams x n) {m : ℕ} (hm : xMax x n < m)
    (h : HasLeafLeafPath (TTree x n) (2 * m)) :
    ∃ i j : Fin n, i ≠ j ∧ x (i : ℕ) + x (j : ℕ) + idxDist i j = 2 * m
```

**差异与理由:** 我们**去掉了** odd-even 假设——only-if 方向的论证只用到分类定理
`leafLeafPath_length`,与奇偶无关。假设更少即结论更强,不是削弱。完整的
`lemma_2_2_iv`(`TreePaths.lean:276`)按原文带着 odd-even 假设陈述,也已证明。

### E5. `T(x₁…xₙ)` 构造的隐含前提被显式化

**论文原文:**

> First consider a path on `n` vertices with vertex sequence `v₁, . . . , vₙ`. [...]
> Given a sequence of positive integers `x₁, . . . , xₙ` [...]

**Lean 陈述(`Erdos815/TreeBasic.lean:45`):**

```lean
structure TParams (x : ℕ → ℕ) (n : ℕ) : Prop where
  two_le : 2 ≤ n
  pos : ∀ i, i < n → 1 ≤ x i
```

**差异与理由:** 两条都是论文的**隐含**前提,且都是必需的:`n ≥ 2` 由 "a path on `n`
vertices" 与 Figure 3 隐含(`n = 1` 时 `v₁` 同时是首尾,构造退化);`xᵢ ≥ 1` 就是
"a sequence of positive integers"。缺任一条,某个 `vᵢ` 的度会掉到 2,`T(x₁…xₙ)` 就
不是 1-3 树。论文正确地依赖它们但未列出;Lean 必须写出来。最终定理里 `n = i + 2`
自动满足 `2 ≤ n`,序列取值恒 `≥ 1`(`xA_pos`),两条前提都被履行。

### E6. 下标平移

**论文原文:** `xᵢ ≡ i (mod 2)`,下标从 **1** 起;`Tₙ = T(x₁ … xₙ)`。

**Lean 陈述(`Erdos815/TreeBasic.lean:56`、`Erdos815/Main.lean:112`):**

```lean
def IsOddEvenFin (x : ℕ → ℕ) (n : ℕ) : Prop := ∀ i, i < n → x i % 2 = (i + 1) % 2

def xA (i : ℕ) : ℕ := aSeq ((i : ℤ) + 1)
```

**差异与理由:** `TTree x n` 取 `x` 在 `0, …, n−1` 上的值,故我们的 `x i` 是论文的
`x_{i+1}`,odd-even 条件相应写成 `x i ≡ i + 1 (mod 2)`。最终组装时取
`xA i := aSeq (i + 1)`,即论文的 `a_{i+1}`,与 `aSeq I ≡ I (mod 2)` 严丝合缝。
这是纯记号平移,已在两处 docstring 里写死,并由 `aSeq_matches_paper`(见 F2)
机械锁定。

---

## F. Theorem 2.5 与序列

### F1. k-avoiding 的定义

**论文原文(Definition 2.3):**

> Let `k` be a positive even integer. A two-sided sequence `(xᵢ)_{i∈ℤ}` of positive
> integers is called *k-avoiding* if `aᵢ ≤ k/2` for all `i ∈ ℤ` and if for every
> `i, j ∈ ℤ`, `i ≠ j`, we have `aᵢ + aⱼ + |i − j| ≠ k`.

**Lean 陈述(`Erdos815/Defs.lean:31`、`Defs.lean:41`):**

```lean
def IsOddEvenSeq (a : ℤ → ℕ) : Prop := ∀ i : ℤ, ((a i : ℤ) - i) % 2 = 0

def IsKAvoiding (k : ℕ) (a : ℤ → ℕ) : Prop :=
  (∀ i : ℤ, 2 * a i ≤ k) ∧
  (∀ i j : ℤ, i ≠ j → a i + a j + (i - j).natAbs ≠ k)
```

**差异与理由:** 两处,均为消除除法歧义。

1. **`aᵢ ≤ k/2` 写成 `2 * aᵢ ≤ k`**。`k` 是偶数,二者等价;写成乘法避免 `ℕ` 除法的
   截断歧义。
2. **`|i − j|` 用 `Int.natAbs`** 落回 `ℕ`,与 `aᵢ + aⱼ` 同类型。
3. 序列类型 `ℤ → ℕ` 对应论文的 "two-sided sequence of positive integers";
   “positive” 不写进类型而是作为单独的有限检查(`aSeq_pos`,`Sequence.lean:142`)——
   这是必需的,因为 `d ≥ 19` 那一档的排除正是靠 `aᵢ ≥ 1`。

**论文的一处记号笔误(已核对):** Definition 2.3 把序列记作 `(xᵢ)` 而条件里写 `aᵢ`,
指的是同一个序列。我们统一用 `a`。

### F2. 序列本身与下标对齐

**论文原文(Theorem 2.5 证明):**

> Let `(aᵢ)_{i∈ℤ}` be the periodic sequence of period 24 consisting of repetitions of
> `. . . , 1, 2, 1, 4, 3, 2, 7, 6, 5, 6, 7, 2, 3, 4, 1, 2, 1, 8, 9, 6, 5, 6, 9, 8, . . . .`

**Lean 陈述(`Erdos815/Sequence.lean:33`、`Sequence.lean:45`):**

```lean
def seqList : List ℕ :=
  [8, 1, 2, 1, 4, 3, 2, 7, 6, 5, 6, 7, 2, 3, 4, 1, 2, 1, 8, 9, 6, 5, 6, 9]

theorem aSeq_matches_paper :
    (List.range 24).map (fun t => aSeq (t + 1)) =
      [1, 2, 1, 4, 3, 2, 7, 6, 5, 6, 7, 2, 3, 4, 1, 2, 1, 8, 9, 6, 5, 6, 9, 8] := by
  decide
```

**差异与理由:** `seqList` 把末项 `8` 旋到开头,是为了让 `aSeq i = seqAt (i % 24)`
这个最简的周期延拓公式恰好给出 `aSeq 1 = 1, …, aSeq 24 = 8`,即与论文从 1 起的下标
完全一致。**这个对齐本身是被机器检查的**:`aSeq_matches_paper` 逐项断言
`aSeq 1 … aSeq 24` 等于论文正文里印的那 24 个数,由 `decide` 判定。
换句话说,“我们抄对了序列且对齐了下标”不是口头保证,而是一条已证定理。

### F3. T2.5 的证明:从看图到完全枚举

**论文原文(Theorem 2.5 证明结尾):**

> Figure 4 is a snapshot of two periods of the graph. The points on the graph are black
> circles, and the fault lines are drawn in red. [...]
> **From the picture we see that** no point of the sequence lies on a fault line of
> another point, implying that `(aᵢ)_{i∈ℤ}` is indeed 20-avoiding.

**Lean 陈述(`Erdos815/Sequence.lean:72`、`Sequence.lean:81`、`Sequence.lean:183`):**

```lean
def noConflictOK : Bool :=
  (range 24).all fun r =>
    (range 19).all fun d =>
      decide (d = 0) || decide (seqAt r + seqAt ((r + d) % 24) + d ≠ 20)

theorem noConflictOK_eq : noConflictOK = true := by decide

theorem aSeq_isKAvoiding : IsKAvoiding 20 aSeq
```

**差异与理由:这是本仓相对论文**严格更强**的一处,值得单列。**

论文的 T2.5 证明是**看图**的:Proposition 2.4 与 fault line 那一整套是为人眼检查服务的
几何化重述,最后一步是 "From the picture we see that"。这一步不可直接形式化,
而且它是全篇中证据强度最弱的一环(读者无法从印刷图上真正验证 24 个点 × 两条对角线
的全部关系)。

我们**不形式化 Proposition 2.4**,直接按 Definition 2.3 的字面定义做**完全枚举**:
`decide` 在 Lean 内核里逐项求值 `24 × 19` 个组合,确认无一冲突。这是内核层面的
判定性检查,不依赖任何图像、直觉或 `native_decide`(后者会引入 `Lean.ofReduceBool`
公理,本仓禁用)。

**为什么绕过 Prop 2.4 不损失任何东西**:Prop 2.4 是 Def 2.3 的等价重述
(“`(i, aᵢ)` 在 `(j, aⱼ)` 的 fault line 上”按 fault line 的定义展开就是
`aᵢ + aⱼ + |i−j| = 20` 且 `i > j`),是一条**为了让人眼能查**而引入的中间语言。
直接查定义本身比查它的重述更强。

**有限化归约**(数学上平凡,但 Lean 里必须写出来,`Sequence.lean:162`):
无穷条件 `∀ i ≠ j ∈ ℤ, aᵢ + aⱼ + |i−j| ≠ 20` 归约到 `24 × 19` 的有限检查,靠三步:
(a) **对称化**:`i ≠ j` 时不妨 `i < j`,令 `d = j − i ≥ 1`;
(b) **`d` 的上界**:`aᵢ, aⱼ ≥ 1` ⟹ 和 `≥ d + 2`,故 `d ≥ 19` 时和 `≥ 21 > 20`,
条件自动成立,只需查 `d ≤ 18`;
(c) **`i` 可约到 `[0, 24)`**:周期性。
三步都在 Lean 里显式证明,不是注释里的断言。

### F4. 论文 `aᵢ ≤ 10` 与实际最大值 9

**论文原文(Theorem 2.5 证明):** `It is clearly an odd-even sequence, and aᵢ ≤ 10 = 20/2
for all i ∈ ℤ.`
**论文原文(Theorem 1.3(ii) 证明):** `since 20 > 2 · max xᵢ = 18`

**Lean 陈述(`Erdos815/Sequence.lean:159`、`Erdos815/Main.lean:133`):**

```lean
lemma aSeq_le_nine (i : ℤ) : aSeq i ≤ 9
lemma xA_xMax_lt (n : ℕ) : xMax xA n < 10
```

**差异与理由:** 论文两处用了两个不同的界,不矛盾但需要说明。Definition 2.3 要求
`aᵢ ≤ k/2 = 10`,论文在 T2.5 里核对的就是这条松界;而 T1.3(ii) 的论证需要
`20 > 2 · max aᵢ`,用的是该序列的**实际**最大值 **9**(`2 × 9 = 18 < 20`)。
论文写 `≤ 10` 是为对齐 Def 2.3,并非声称取到 10。
本仓两条界都证:`aSeq_le_half`(`2aᵢ ≤ 20`,即 Def 2.3 那条)与 `aSeq_le_nine`
(实际界,供 T1.3(ii) 用)。后者是本链路必需的——`lemma_2_2_iv_only_if` 要
`xMax < m` 且 `m = 10`,松界 `≤ 10` 给不出严格不等号。

### F5. 论文的第三处记号笔误

**论文原文(构造段):** `trees T₁^{(1)} and T₁^{(1)} of depths x₁ − 1`

**差异与理由:** 按后文的 `v₁u₁^{(1)}, v₁u₁^{(2)}` 与 Figure 3,第二棵应为 `T₁^{(2)}`。
这是排版笔误,不影响内容。本仓的编码里两侧由 `Bool` 参数 `s` 区分
(`TV.treeV i s l`,`Defs.lean:192`),`s = true` 只在 `i = 0` 与 `i = n−1` 出现
(由 `TValid` 强制,`Defs.lean:209`),与 Figure 3 的语义一致。

---

## G. Theorem 1.3(ii) 与原问题的关系

### G1. T1.3(ii)

**论文原文(Theorem 1.3(ii)):**

> There is an infinite family of even 1-3 trees `(Tₙ)^∞_{n=1}`, such that `Tₙ` contains
> no leaf-leaf path of length 20.

**Lean 陈述(`Erdos815/Main.lean:148`):**

```lean
theorem theorem_1_3_ii {n : ℕ} (hn : 2 ≤ n) :
    ¬ HasLeafLeafPath (TTree xA n) 20
```

**差异与理由:** 论文把“无穷族”打包进陈述;我们**对每个 `n ≥ 2` 分别陈述**,
族的无穷性在最终定理 `erdos_815` 里给出(A1、A2)。这样拆更强:它对**每一个**
`n ≥ 2` 都断言,而不只是断言存在某个无穷子族。“even 1-3 trees” 的两个性质由
`TTree_is13Tree` 与 `TTree_isEvenTree` 分别给出(`TreePaths.lean:113`、
`TreeStruct.lean` 内),在 `theorem_1_2` 里作为前提被使用。

### G2. 原问题、`k ≥ 3` 与只给 `k = 23` 反例

**原问题(Erdős #815 / 论文 Conjecture 1.1 的语境):** 对 `k ≥ 3` 且 `n` 充分大,
degree 3-critical 图是否**必**含长度 `k` 的圈?

**论文与本仓给出的答案:否。**

**为什么单个 `k` 的反例族就构成对原问题的否定回答:** 原问题是一个**全称**命题
(对一切 `k ≥ 3`、一切充分大的 `n`,都必含长 `k` 的圈)。否定它只需要给出**一个** `k`
和**任意大**的反例。论文取 `k = 23`,给出顶点数无上界的一族 degree 3-critical 图,
每个都不含长 23 的圈。“任意大”这一面正是 `erdos_815` 第二个合取项
(顶点数严格递增)所保证的——若只有有限个反例,就不能排除“`n` 充分大之后结论成立”,
否定就不成立。这解释了为什么 A1 里坚持不能把“无穷”弱化成“存在一个”。

**为什么是 23:** 23 由构造链条锁死,不是随意取的。Lemma 2.1(i):`G(T)` 有长 `2k+1`
的圈 ⟺ `T` 有长 `2k−2` 的 leaf-leaf 路径;Theorem 2.5 给出的是 **20**-avoiding 序列
⟹ `Tₙ` 无长 **20** 的 leaf-leaf 路径;令 `2k − 2 = 20` ⟹ `k = 11` ⟹ 圈长
`2k + 1 = 23`。所以“20-avoiding”与“无 23-圈”是同一件事的两面。

**本仓未覆盖的相关结论:** 论文 §3 的 Theorem 1.3(i) 说明本方法给不出更强的结果
(即 23 是这条路线能达到的界),§4 的 Theorem 1.4 是另一个方向。二者**均不在本任务
范围内,未做**,因此本仓**不主张**“23 是最优的”这类论断——只主张论文 §2 的内容
已被完整形式化。

---

## H. 汇总:偏离清单

全仓与论文的形式出入共 17 处,分三类,**无一削弱最终定理**:

| 类别 | 条目 | 性质 |
|---|---|---|
| **更强**(Lean 版严于论文) | F3(看图 ⟶ 完全枚举)、A1(无穷 ⟶ 顶点数严格递增)、E4(去掉 odd-even 假设)、G1(逐 `n` 陈述)、C3(补上论文未提的首末边情形) | 结论更强或假设更少 |
| **等价重述**(消除 Lean 的类型/歧义) | B1(截断减法、最小度写法、`s.Nonempty`)、B2(induced,附等价性论证)、C1(`Walk.length` 数边)、C2(`2k+1` ⟶ `ℓ+3`)、D1(偶树用路径刻画)、D2(度用 `∃!` 刻画)、E1(分级函数代替分类)、E2(三档压两档)、E6(下标平移)、F1(`2aᵢ ≤ k` 与 `natAbs`) | 语义不变 |
| **范围取舍**(论文有、本链路不用) | C2 第 1 点(L2.1 只做 ⟹ 方向,⟸ 未做)、E3((ii) 下界 `1 ≤ m` 而非 `0 ≤ m`)、G2(§3/§4 未做) | 已明确标注,不进入最终定理依赖链 |
| **论文自身的笔误**(已核对) | F1(`(xᵢ)` vs `aᵢ`)、F4(`≤ 10` vs 实际 `9`)、F5(`T₁^{(1)}` vs `T₁^{(2)}`) | 不影响内容,按语义处理 |

另有两处**纯实现层**选择,论文不会提及、不改变陈述:A2(子列)与 A3(同构搬运)。

**结论:自拟的 `erdos_815` 陈述是论文 Theorem 1.2 的忠实(且在若干处更强的)形式化。
风险自担,对照如上。**
