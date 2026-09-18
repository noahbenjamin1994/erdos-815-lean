/-
# 定义层

Narins–Pokrovskiy–Szabó, *Graphs without proper subgraphs of minimum degree 3 and
short cycles*, Combinatorica 37 (2017) 495–519, arXiv:1408.5289, §2 的形式化。

本文件只放定义,**不含任何证明义务**。逐条定义对应的论文原文见
`.work/erdos-815/notes/paper-section2.md`,设计理由见 `notes/blueprint.md`。

图论基础一律复用 Mathlib(`SimpleGraph.Walk` / `IsPath` / `IsCycle` / `IsTree` /
`SimpleGraph.induce`),不另造一套。
-/
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace Erdos815

/-! ## 1. 序列(论文 §2.1)

论文的序列是**两侧无穷**的 `(aᵢ)_{i∈ℤ}`,取值为正整数,故用 `ℤ → ℕ`。
-/

/-- **odd-even sequence**(论文 §2 / §2.1):`aᵢ ≡ i (mod 2)`。

写成 `((a i : ℤ) - i) % 2 = 0` 是为了 `omega` 能直接处理(它认识以字面量为模的整数取余)。 -/
def IsOddEvenSeq (a : ℤ → ℕ) : Prop := ∀ i : ℤ, ((a i : ℤ) - i) % 2 = 0

/-- **k-avoiding**(论文 Definition 2.3):

> Let `k` be a positive even integer. A two-sided sequence `(aᵢ)_{i∈ℤ}` of positive integers
> is called `k`-avoiding if `aᵢ ≤ k/2` for all `i ∈ ℤ` and if for every `i, j ∈ ℤ`, `i ≠ j`,
> we have `aᵢ + aⱼ + |i − j| ≠ k`.

`aᵢ ≤ k/2` 写成无除法的 `2 * aᵢ ≤ k`(`k` 是偶数,二者等价,且避免 `ℕ` 除法截断)。
`|i − j|` 用 `Int.natAbs` 落回 `ℕ`,与 `aᵢ + aⱼ` 同类型。 -/
def IsKAvoiding (k : ℕ) (a : ℤ → ℕ) : Prop :=
  (∀ i : ℤ, 2 * a i ≤ k) ∧
  (∀ i j : ℤ, i ≠ j → a i + a j + (i - j).natAbs ≠ k)

/-! ## 2. 树的局部概念 -/

variable {V : Type*} {G : SimpleGraph V}

/-- **leaf**:度为 1 的顶点。

写成 `∃! w, G.Adj v w`(恰有一个邻居)而不是 `G.degree v = 1`,
是为了**不需要** `Fintype V` / `DecidableRel G.Adj` 实例 —— 在我们要构造的
无穷族上这些实例都要额外操心。两者在有限图上等价。 -/
def IsLeaf (G : SimpleGraph V) (v : V) : Prop := ∃! w, G.Adj v w

/-- **1-3 tree**(论文 §1):树,且每个顶点度为 1 或 3。

「度为 3」同样避开 `Fintype`,写成「邻居集恰含三个互异元素」。 -/
def IsDeg3 (G : SimpleGraph V) (v : V) : Prop :=
  ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    ∀ w, G.Adj v w ↔ (w = a ∨ w = b ∨ w = c)

/-- **1-3-tree**:*a tree is called a 1-3-tree if every vertex has degree 1 or 3*。 -/
structure Is13Tree (G : SimpleGraph V) : Prop where
  isTree : G.IsTree
  deg : ∀ v : V, IsLeaf G v ∨ IsDeg3 G v

/-- **leaf-leaf path**:两个**相异**叶子之间的路径。

论文 §1:*the lengths of paths going between two leaves*。
`Walk.length` 数的是**边数**,与论文的「路径长度」一致。 -/
def IsLeafLeafPath {u v : V} (G : SimpleGraph V) (p : G.Walk u v) : Prop :=
  p.IsPath ∧ IsLeaf G u ∧ IsLeaf G v ∧ u ≠ v

/-- `G` 含一条长为 `ℓ` 的 leaf-leaf 路径。 -/
def HasLeafLeafPath (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), IsLeafLeafPath G p ∧ p.length = ℓ

/-- **even tree**(论文 §1):*all of its leaves are in the same class of the tree's
unique bipartition*。

等价刻画(我们采用的形式):任意两个叶子之间的路径长度都是偶数。二部图里两点同色
⟺ 它们之间的路径长为偶数,而树中两点间路径唯一,所以这与论文定义等价 —— 好处是
不必先构造出那个二部划分。 -/
def IsEvenTree (G : SimpleGraph V) : Prop :=
  ∀ (u v : V) (p : G.Walk u v), IsLeafLeafPath G p → p.length % 2 = 0

/-! ## 3. `G(T)` 构造(论文 §2)

> Given a tree `T`, define `G(T)` to be the graph formed from `T` by adding two new
> vertices `x` and `y`, the edge `xy` as well as every edge between `{x, y}` and the
> leaves of `T`.

顶点类型取 `V ⊕ Bool`:`.inl v` 是 `T` 的原顶点,`.inr false` 是 `x`,`.inr true` 是 `y`。
-/

/-- `G(T)` 的邻接关系。 -/
def gtAdj (G : SimpleGraph V) : V ⊕ Bool → V ⊕ Bool → Prop
  | .inl a, .inl b => G.Adj a b
  | .inl a, .inr _ => IsLeaf G a
  | .inr _, .inl b => IsLeaf G b
  | .inr p, .inr q => p ≠ q

lemma gtAdj_symm (G : SimpleGraph V) : ∀ u v, gtAdj G u v → gtAdj G v u := by
  rintro (a | p) (b | q) h <;> simp only [gtAdj] at h ⊢
  · exact h.symm
  · exact h
  · exact h
  · exact h.symm

lemma gtAdj_irrefl (G : SimpleGraph V) : ∀ u, ¬ gtAdj G u u := by
  rintro (a | p) h <;> simp only [gtAdj] at h
  · exact G.irrefl h
  · exact h rfl

/-- **`G(T)`**:树 `T` 加两个新点 `x = .inr false`、`y = .inr true`、边 `xy`,
以及 `{x, y}` 到 `T` 所有叶子的全部边。 -/
def GT (G : SimpleGraph V) : SimpleGraph (V ⊕ Bool) where
  Adj := gtAdj G
  symm := ⟨gtAdj_symm G⟩
  loopless := ⟨gtAdj_irrefl G⟩

@[simp] lemma GT_adj_inl_inl (G : SimpleGraph V) (a b : V) :
    (GT G).Adj (.inl a) (.inl b) ↔ G.Adj a b := Iff.rfl

@[simp] lemma GT_adj_inl_inr (G : SimpleGraph V) (a : V) (p : Bool) :
    (GT G).Adj (.inl a) (.inr p) ↔ IsLeaf G a := Iff.rfl

@[simp] lemma GT_adj_inr_inl (G : SimpleGraph V) (b : V) (p : Bool) :
    (GT G).Adj (.inr p) (.inl b) ↔ IsLeaf G b := Iff.rfl

@[simp] lemma GT_adj_inr_inr (G : SimpleGraph V) (p q : Bool) :
    (GT G).Adj (.inr p) (.inr q) ↔ p ≠ q := Iff.rfl

/-! ## 4. degree 3-critical(论文 §1)

> a graph `G` with `n` vertices and `2n − 2` edges such that every proper induced
> subgraph of `G` has minimum degree at most 2.

**关于「真子图」 vs 「真导出子图」**:论文标题说的是 proper subgraph,但 §1 明确
论证了 Conjecture 1.1 里应当理解为 **induced**(并说 [3] 的结果对两种读法都成立),
正文「throughout most of this paper」用的就是 induced 版本。我们采用 **proper induced
subgraph**,与论文 §2 实际使用的定义一致。

这两种读法在「最小度 ≤ 2」这个条件上其实是等价的:若 `H ⊆ G` 是最小度 `≥ 3` 的子图,
则 `G` 在 `V(H)` 上的导出子图包含 `H` 的所有边,最小度也 `≥ 3`。所以
「无最小度 ≥ 3 的真子图」与「无最小度 ≥ 3 的真导出子图」给出同一个图类
(顶点集相同、边更多的导出子图只会让度更大)。

**`2 * n - 2` 是 `ℕ` 截断减法**:在 `n ≥ 1` 时 `2 * n ≥ 2`,不发生截断,无歧义。
我们要构造的图 `n ≥ 3`,永远落在安全区。

**实例选择**:用 `open scoped Classical` 提供 `DecidableRel G.Adj` 与 `Fintype ↥s`,
不要求调用方提供 —— 这是 `Prop` 层的定义,可计算性无关紧要,而显式实例会在
`Sum`/`Sigma` 顶点类型上制造大量样板。 -/

open scoped Classical in
/-- **degree 3-critical**:`n` 个顶点、`2n − 2` 条边,且每个真导出子图的最小度 `≤ 2`。

「最小度 ≤ 2」写成「存在一个顶点度 ≤ 2」;真导出子图对应 `s ≠ Set.univ`,
并要求 `s.Nonempty`(空图没有顶点可谈最小度,论文的语境里也不把它算作子图)。 -/
def IsDegree3Critical {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  G.edgeFinset.card = 2 * Fintype.card V - 2 ∧
  ∀ s : Set V, s.Nonempty → s ≠ Set.univ → ∃ v : s, (G.induce s).degree v ≤ 2

/-! ## 5. 完美二叉树与 `T(x₁ … xₙ)`(论文 §2)

### 完美二叉树

> We say that a rooted binary tree `T` is *perfect* if all non-leaf vertices have two
> children and all root-leaf paths have the same length `d`.

深度 `d` 的完美二叉树,顶点 = 长度 `≤ d` 的 `Bool` 串(根是空串,`l` 的两个孩子是
`false :: l` 与 `true :: l`)。`|V| = 2^{d+1} − 1`,与论文的另一刻画一致。

### `T(x₁ … xₙ)`

> First consider a path on `n` vertices with vertex sequence `v₁, . . . , vₙ`. For each `i`
> satisfying `2 ≤ i ≤ n − 1`, add a perfect rooted binary tree `Tᵢ` of depth `xᵢ − 1` with
> root vertex `uᵢ`. For `i = 1` and `n` add two perfect rooted binary trees each [...]
> Finally, for each `i, 2 ≤ i ≤ n − 1`, we add the edges `vᵢuᵢ`, as well as the edges
> `v₁u₁^{(1)}, v₁u₁^{(2)}, vₙuₙ^{(1)},` and `vₙuₙ^{(2)}`.

顶点用一个 raw 类型 + 合法性谓词刻画:
* `PathV i`  —— 路径点 `vᵢ`(`i < n`);
* `TreeV i s l` —— 挂在 `vᵢ` 上、第 `s` 侧(`s = false` 是论文的 `Tᵢ` / `Tᵢ^{(1)}`,
  `s = true` 只在 `i = 0` 与 `i = n-1` 出现,是论文的 `Tᵢ^{(2)}`)的那棵完美二叉树里
  的结点,`l : List Bool` 是从该子树根往下的路径(根 = `[]`,即论文的 `uᵢ`)。
-/

/-- `T(x₁ … xₙ)` 的 raw 顶点。 -/
inductive TV (n : ℕ) where
  /-- 路径上的第 `i` 个点 `v_{i+1}`(0-based)。 -/
  | pathV : Fin n → TV n
  /-- 挂在 `vᵢ` 上、第 `s` 侧的完美二叉树里、根到该点路径为 `l` 的结点。 -/
  | treeV : Fin n → Bool → List Bool → TV n
  deriving DecidableEq

variable {n : ℕ}

/-- 第 `i` 个位置是否用**两**棵子树(论文:`i = 1` 和 `i = n` 各挂两棵)。 -/
def twoSided (n : ℕ) (i : Fin n) : Prop := (i : ℕ) = 0 ∨ (i : ℕ) = n - 1

instance (n : ℕ) (i : Fin n) : Decidable (twoSided n i) := by
  unfold twoSided; infer_instance

/-- raw 顶点的合法性:侧 `s = true` 只在两侧位置出现;子树深度是 `xᵢ − 1`,
故根到结点的路径长 `|l| ≤ xᵢ − 1`。 -/
def TValid (x : ℕ → ℕ) (n : ℕ) : TV n → Prop
  | .pathV _ => True
  | .treeV i s l => (s = false ∨ twoSided n i) ∧ l.length + 1 ≤ x (i : ℕ)

instance (x : ℕ → ℕ) (n : ℕ) (v : TV n) : Decidable (TValid x n v) := by
  cases v <;> unfold TValid <;> infer_instance

/-- `T(x₁ … xₙ)` 的顶点类型。 -/
def TVtx (x : ℕ → ℕ) (n : ℕ) : Type := {v : TV n // TValid x n v}

instance (x : ℕ → ℕ) (n : ℕ) : DecidableEq (TVtx x n) := by
  unfold TVtx; infer_instance

/-- raw 邻接:路径边 `vᵢvᵢ₊₁`、子树内部的父子边、以及 `vᵢ` 与子树根 `uᵢ` 的连边。 -/
def tAdjRaw (n : ℕ) : TV n → TV n → Prop
  | .pathV i, .pathV j => (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)
  -- `vᵢ` 连到挂在它身上的每棵子树的根(`l = []`,即论文的 `uᵢ`)
  | .pathV i, .treeV j _ l => i = j ∧ l = []
  | .treeV j _ l, .pathV i => i = j ∧ l = []
  -- 同一棵子树内的父子边
  | .treeV i s l, .treeV j t m =>
      i = j ∧ s = t ∧ (∃ b, l = b :: m) ∨ i = j ∧ s = t ∧ (∃ b, m = b :: l)

lemma tAdjRaw_symm (n : ℕ) : ∀ u v : TV n, tAdjRaw n u v → tAdjRaw n v u := by
  rintro (i | ⟨i, s, l⟩) (j | ⟨j, t, m⟩) h <;> simp only [tAdjRaw] at h ⊢ <;> try tauto

lemma tAdjRaw_irrefl (n : ℕ) : ∀ u : TV n, ¬ tAdjRaw n u u := by
  rintro (i | ⟨i, s, l⟩) h <;> simp only [tAdjRaw] at h
  · omega
  · rcases h with ⟨-, -, b, hb⟩ | ⟨-, -, b, hb⟩ <;>
      exact absurd hb.symm (List.cons_ne_self b l)

/-- **`T(x₁ … xₙ)`**:论文 §2 的那棵 1-3 树。

下标约定:`x` 用 `ℕ → ℕ`,`T` 取它在 `0, 1, …, n-1` 上的值,对应论文的 `x₁ … xₙ`。 -/
def TTree (x : ℕ → ℕ) (n : ℕ) : SimpleGraph (TVtx x n) where
  Adj u v := tAdjRaw n u.val v.val
  symm := ⟨fun u v h => tAdjRaw_symm n u.val v.val h⟩
  loopless := ⟨fun u h => tAdjRaw_irrefl n u.val h⟩

@[simp] lemma TTree_adj (x : ℕ → ℕ) (n : ℕ) (u v : TVtx x n) :
    (TTree x n).Adj u v ↔ tAdjRaw n u.val v.val := Iff.rfl

/-! ## 6. 目标陈述里要用到的「含长为 `ℓ` 的圈」

Mathlib 没有裸的 `SimpleGraph.Cycle` 类型,圈一律写成
「存在起点 `v` 与闭迹 `c : G.Walk v v`,`c.IsCycle` 且 `c.length = ℓ`」。
`Walk.length` 数的是**边数**,与论文「长度 23 的圈」一致。 -/

/-- `G` 含一个长为 `ℓ` 的圈。 -/
def HasCycleOfLength (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = ℓ

end Erdos815
