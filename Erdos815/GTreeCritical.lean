/-
# P-crit —— `T` 是 1-3 树 ⟹ `G(T)` 是 degree 3-critical

论文 §2:*Notice that if `T` is a 1-3 tree then `G(T)` is degree 3-critical.*
论文把这一步当作显然,**没有给出证明**;形式化时必须自己补全。下面先写出完整的
proof sketch(我们补的论证),再逐条形式化。

---

## Proof sketch(我们补的;论文只有一句 "Notice that")

记 `T` 有 `t` 个顶点、`ℓ` 个叶子、`d` 个 3 度点。`G(T)` 有 `N = t + 2` 个顶点。

### (A) 1-3 树的顶点计数恒等式:`2ℓ = t + 2`

1. `T` 是树 ⟹ `|E(T)| = t − 1`(Mathlib `IsTree.card_edgeFinset`)。
2. 每个顶点度为 1 或 3,两类互斥 ⟹ `ℓ + d = t`。
3. 握手引理 `∑ deg = 2|E(T)|` ⟹ `ℓ · 1 + d · 3 = 2(t − 1)`。
4. 消去 `d`:`2d = t − 2`,`ℓ = t − d` ⟹ `2ℓ = t + 2`。

### (B) 边数 `= 2N − 2`

直接对 `G(T)` 再用一次握手引理,而不去拆 `edgeFinset`:

* 每个 `.inl a`(`T` 的原顶点)在 `G(T)` 里的度**恰为 3**:
  - `a` 是叶子 ⟹ 邻居是「`T` 里唯一的那个邻居」+ `x` + `y` = 3 个;
  - `a` 是 3 度点 ⟹ `a` 不是叶子,故 `x, y` 都不与它相连,邻居就是 `T` 里那 3 个。
  这条「所有原顶点在 `G(T)` 里都是 3 度」是整个构造的要点。
* 每个 `.inr p`(即 `x` 与 `y`)的度是 `ℓ + 1`(全部叶子 + 对方)。

于是 `∑_{w ∈ V(G(T))} deg(w) = 3t + 2(ℓ + 1)`,代入 (A) 的 `2ℓ = t + 2` 得 `= 4t + 4`,
故 `|E(G(T))| = 2t + 2 = 2(t + 2) − 2 = 2N − 2`。 ∎

### (C) 每个真导出子图最小度 `≤ 2`

反证。设 `S ⊊ V(G(T))`、`S ≠ ∅`,且 `G(T)[S]` 的每个顶点度 `≥ 3`。

**关键观察**:`G(T)` 里 `.inl a` 的度恰为 3(见 (B)),而导出子图的度不超过全图的度。
所以若 `.inl a ∈ S` 且它在 `G(T)[S]` 里的度 `≥ 3`,则它在 `G(T)` 里的**全部**邻居都在 `S` 里。

* **情形 1:`S` 含某个 `.inl a₀`。**
  由上述观察,`A := {a | .inl a ∈ S}` 对 `T` 的邻接封闭。`T` 连通 ⟹ 沿任意 walk 传播 ⟹
  `A = V(T)`,即所有原顶点都在 `S` 里。再由 (A) 知叶子集非空,取一个叶子 `a₁`;
  `a₁` 在 `G(T)` 里与 `x, y` 都相邻,故 `x, y ∈ S`。于是 `S = V(G(T))`,与 `S` 真子集矛盾。

* **情形 2:`S` 不含任何 `.inl a`。**
  则 `S ⊆ {x, y}`,任取 `v ∈ S`,它在 `G(T)[S]` 里的度 `≤ |S| ≤ 2` —— 这一支不需要反证,
  直接给出了要找的顶点。 ∎

---

原文摘录见 `.work/erdos-815/notes/paper-section2.md`,设计理由见 `notes/blueprint.md`。
-/
import Erdos815.Defs

namespace Erdos815

open Finset SimpleGraph

variable {V : Type*}

/-! ## 0. 实例无关性

`IsDegree3Critical` 是用 `open scoped Classical in` 写的,`Fintype (GT G).edgeSet`、
`Fintype ((GT G).neighborSet w)` 这些实例在**定义**里被固化成了具体的闭项;而我们在
证明里由 `classical` / `inferInstance` 现场合成的实例只是**定义相等**、并不语法相同。
`omega` 之类按语法配原子的 tactic 会把二者当成两个无关的量,于是证不动。

解决办法:凡是要跟 `IsDegree3Critical` 的目标对接的引理,一律把 `Fintype` 实例
写成**显式参数**,从而对任意实例都成立(见下面的 `mem_of_adj_of_degree_le`)。
`Fintype` 是 `Subsingleton`,这不损失任何东西。

次选办法:避开 `omega` 这类按语法配原子的 tactic,改用 `le_trans (le_of_eq …) …`
这种不看语法的组合子 —— 本文件两处都用到了。 -/

/-! ## 1. `IsLeaf` / `IsDeg3` 与 `degree` 的对接

`Defs.lean` 里 `IsLeaf` / `IsDeg3` 是用 `∃!` / 「恰三个互异邻居」写的(为了不拖 `Fintype`
实例)。计数时必须换回 `degree`。 -/

/-- 叶子 ⟺ 度为 1。 -/
lemma isLeaf_iff_degree_eq_one {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)] :
    IsLeaf G v ↔ G.degree v = 1 :=
  SimpleGraph.degree_eq_one_iff_existsUnique_adj.symm

/-- 3 度点 ⟹ 度为 3。 -/
lemma IsDeg3.degree_eq_three {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)]
    (h : IsDeg3 G v) : G.degree v = 3 := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hadj⟩ := h
  show #(G.neighborFinset v) = 3
  rw [Finset.card_eq_three]
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  ext w
  simp only [SimpleGraph.mem_neighborFinset, hadj w, Finset.mem_insert, Finset.mem_singleton]

/-- 3 度点不是叶子。

刻意**不**经过 `degree`(那会拖一个 `Fintype (G.neighborSet v)` 实例参数,
而这条引理在下面的临界性论证里要用在实例来源不同的上下文中):
直接用 `IsLeaf` 的唯一性把两个互异邻居等同起来。 -/
lemma IsDeg3.not_isLeaf {G : SimpleGraph V} {v : V} (h : IsDeg3 G v) : ¬ IsLeaf G v := by
  obtain ⟨a, b, _, hab, -, -, hadj⟩ := h
  intro hl
  obtain ⟨u, -, huniq⟩ := hl
  exact hab ((huniq a ((hadj a).mpr (Or.inl rfl))).trans
    (huniq b ((hadj b).mpr (Or.inr (Or.inl rfl)))).symm)

/-- 1-3 树里,不是叶子的点度为 3。 -/
lemma Is13Tree.degree_eq_three_of_ne_one {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (hT : Is13Tree G) {v : V} (h : G.degree v ≠ 1) : G.degree v = 3 := by
  rcases hT.deg v with hl | hd
  · exact absurd (isLeaf_iff_degree_eq_one.mp hl) h
  · exact hd.degree_eq_three

/-! ## 2. (A) 1-3 树的顶点计数恒等式 `2ℓ = t + 2` -/

/-- `T` 的叶子集合(用 `degree = 1` 刻画,便于 `filter`)。 -/
def leafFinset (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 1)

lemma mem_leafFinset {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] {v : V} :
    v ∈ leafFinset G ↔ G.degree v = 1 := by
  simp [leafFinset]

/-- **1-3 树的顶点计数恒等式**:`2 · (叶子数) = (顶点数) + 2`。

论文完全没写这一条(它把 P-crit 整条当作显然),但它是边数计算的全部内容。
证明 = 树的边数公式 + 握手引理 + 「度只能是 1 或 3」的二分,最后交给 `omega`。 -/
theorem Is13Tree.two_mul_card_leafFinset {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (hT : Is13Tree G) :
    2 * (leafFinset G).card = Fintype.card V + 2 := by
  classical
  -- 把 `univ` 按「度是否为 1」劈成两半
  have hsplit : (leafFinset G).card
      + (Finset.univ.filter (fun v : V => ¬ (G.degree v = 1))).card = Fintype.card V := by
    rw [leafFinset]
    exact Finset.card_filter_add_card_filter_not _
  -- 度之和按同样的二分展开
  have hsum : (leafFinset G).card
      + 3 * (Finset.univ.filter (fun v : V => ¬ (G.degree v = 1))).card = ∑ v, G.degree v := by
    rw [← Finset.sum_filter_add_sum_filter_not (univ : Finset V)
      (fun v => G.degree v = 1) (fun v => G.degree v)]
    congr 1
    · rw [leafFinset, Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)]
      simp
    · rw [Finset.sum_congr rfl
        (fun v hv => hT.degree_eq_three_of_ne_one (Finset.mem_filter.mp hv).2)]
      simp [mul_comm]
  -- 握手引理 + 树的边数公式
  have hhand : ∑ v, G.degree v = 2 * #G.edgeFinset := G.sum_degrees_eq_twice_card_edges
  have htree : #G.edgeFinset + 1 = Fintype.card V := hT.isTree.card_edgeFinset
  omega

/-- 1-3 树至少有一个叶子(其实至少两个;这里只需要非空)。 -/
lemma Is13Tree.leafFinset_nonempty {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (hT : Is13Tree G) : (leafFinset G).Nonempty := by
  rw [← Finset.card_pos]
  have h := hT.two_mul_card_leafFinset
  have hV : 0 < Fintype.card V :=
    Fintype.card_pos_iff.mpr hT.isTree.connected.nonempty
  omega

/-! ## 3. (B) `G(T)` 的度分布 -/

/-- **`T` 的每个原顶点在 `G(T)` 里的度恰为 3。**

这是整个构造的要点:叶子在 `T` 里度 1、在 `G(T)` 里补上 `x, y` 正好到 3;
3 度点在 `T` 里已经是 3、且不与 `x, y` 相连。 -/
lemma GT_degree_inl {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [DecidableRel (GT G).Adj] (hT : Is13Tree G) (a : V) :
    (GT G).degree (Sum.inl a) = 3 := by
  classical
  show #((GT G).neighborFinset (Sum.inl a)) = 3
  rw [Finset.card_eq_three]
  rcases hT.deg a with hleaf | hdeg3
  · -- `a` 是叶子:邻居 = {唯一的 T-邻居, x, y}
    obtain ⟨w, hw, huniq⟩ := id hleaf
    refine ⟨Sum.inl w, Sum.inr false, Sum.inr true, by simp, by simp, by simp, ?_⟩
    ext u
    rcases u with b | q
    · simp only [SimpleGraph.mem_neighborFinset, GT_adj_inl_inl, Finset.mem_insert,
        Finset.mem_singleton, Sum.inl.injEq, reduceCtorEq, or_false]
      exact ⟨fun h => huniq b h, fun h => h ▸ hw⟩
    · simp only [SimpleGraph.mem_neighborFinset, GT_adj_inl_inr, Finset.mem_insert,
        Finset.mem_singleton, reduceCtorEq, Sum.inr.injEq, false_or]
      exact ⟨fun _ => by cases q <;> simp, fun _ => hleaf⟩
  · -- `a` 是 3 度点:邻居就是 T 里那三个;`a` 不是叶子,故不与 x, y 相连
    have hnl : ¬ IsLeaf G a := hdeg3.not_isLeaf
    obtain ⟨a₁, a₂, a₃, h12, h13, h23, hadj⟩ := id hdeg3
    refine ⟨Sum.inl a₁, Sum.inl a₂, Sum.inl a₃, by simpa using h12, by simpa using h13,
      by simpa using h23, ?_⟩
    ext u
    rcases u with b | q
    · simp only [SimpleGraph.mem_neighborFinset, GT_adj_inl_inl, Finset.mem_insert,
        Finset.mem_singleton, Sum.inl.injEq, reduceCtorEq, or_false]
      exact hadj b
    · simp only [SimpleGraph.mem_neighborFinset, GT_adj_inl_inr, Finset.mem_insert,
        Finset.mem_singleton, reduceCtorEq, or_self, iff_false]
      exact hnl

/-- **`x` 与 `y` 在 `G(T)` 里的度是「叶子数 + 1」**(全部叶子,外加对方)。 -/
lemma GT_degree_inr {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [DecidableRel (GT G).Adj] (p : Bool) :
    (GT G).degree (Sum.inr p) = (leafFinset G).card + 1 := by
  classical
  show #((GT G).neighborFinset (Sum.inr p)) = _
  have hset : (GT G).neighborFinset (Sum.inr p)
      = insert (Sum.inr (!p)) ((leafFinset G).map ⟨Sum.inl, Sum.inl_injective⟩) := by
    ext u
    rcases u with b | q
    · simp [SimpleGraph.mem_neighborFinset, isLeaf_iff_degree_eq_one, mem_leafFinset]
    · simp only [SimpleGraph.mem_neighborFinset, GT_adj_inr_inr, Finset.mem_insert,
        Finset.mem_map, Function.Embedding.coeFn_mk, Sum.inr.injEq, reduceCtorEq, and_false,
        exists_false, or_false]
      cases p <;> cases q <;> simp
  rw [hset, Finset.card_insert_of_notMem (by simp), Finset.card_map]

/-! ## 4. (B) 边数 `= 2N − 2` -/

/-- **`G(T)` 的边数恰为 `2N − 2`**,其中 `N = |V(T)| + 2` 是 `G(T)` 的顶点数。 -/
theorem GT_card_edgeFinset {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [DecidableRel (GT G).Adj] (hT : Is13Tree G) :
    #(GT G).edgeFinset = 2 * Fintype.card (V ⊕ Bool) - 2 := by
  classical
  have hhand : ∑ w, (GT G).degree w = 2 * #(GT G).edgeFinset :=
    (GT G).sum_degrees_eq_twice_card_edges
  have hsplit : ∑ w, (GT G).degree w
      = (∑ a : V, (GT G).degree (Sum.inl a)) + ∑ q : Bool, (GT G).degree (Sum.inr q) :=
    Fintype.sum_sum_type _
  have hL : (∑ a : V, (GT G).degree (Sum.inl a)) = 3 * Fintype.card V := by
    rw [Finset.sum_congr rfl (fun a _ => GT_degree_inl hT a)]
    simp [Finset.card_univ, mul_comm]
  have hR : (∑ q : Bool, (GT G).degree (Sum.inr q)) = 2 * ((leafFinset G).card + 1) := by
    rw [Finset.sum_congr rfl (fun q _ => GT_degree_inr q)]
    simp [Finset.card_univ, two_mul]
  have hleaf := hT.two_mul_card_leafFinset
  have hcard : Fintype.card (V ⊕ Bool) = Fintype.card V + 2 := by simp
  omega

/-! ## 5. (C) 临界性

先来一条一般引理:导出子图里某点的度达到它在全图里的度 ⟹ 它在全图里的邻居全都落在导出集里。 -/

/-- 若 `v ∈ s` 在 `H.induce s` 里的度不低于它在 `H` 里的度,则 `v` 在 `H` 里的邻居全在 `s` 里。

证明:`H.induce s` 的邻居集在 `Subtype.val` 下单射地嵌入 `H` 的邻居集;
基数不减 ⟹ 像就是整个邻居集。 -/
lemma mem_of_adj_of_degree_le {W : Type*} (H : SimpleGraph W) (s : Set W) (v : s)
    (inst₁ : Fintype ((H.induce s).neighborSet v)) (inst₂ : Fintype (H.neighborSet v.val))
    (h : @SimpleGraph.degree _ H v.val inst₂
          ≤ @SimpleGraph.degree _ (H.induce s) v inst₁) {w : W} (hw : H.Adj v.val w) :
    w ∈ s := by
  classical
  set A : Finset W :=
    (@SimpleGraph.neighborFinset _ (H.induce s) v inst₁).image (fun u : s => (u : W)) with hA
  have hsub : A ⊆ @SimpleGraph.neighborFinset _ H v.val inst₂ := by
    intro y hy
    rw [hA, Finset.mem_image] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    rw [SimpleGraph.mem_neighborFinset] at hu ⊢
    exact hu
  have hcardA : #A = @SimpleGraph.degree _ (H.induce s) v inst₁ := by
    rw [hA, Finset.card_image_of_injective _ Subtype.val_injective]
    rfl
  have heq : A = @SimpleGraph.neighborFinset _ H v.val inst₂ :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardA]; exact h)
  have hmem : w ∈ A := by
    rw [heq, SimpleGraph.mem_neighborFinset]; exact hw
  rw [hA, Finset.mem_image] at hmem
  obtain ⟨u, _, rfl⟩ := hmem
  exact u.2

/-! ## 6. 主定理 -/

open scoped Classical in
/-- **P-crit**(论文 §2 的 *"Notice that if `T` is a 1-3 tree then `G(T)` is degree 3-critical"*)。

论文未给证明;上面文件头的 proof sketch 是我们补的论证,下面是它的形式化。 -/
theorem gt_isDegree3Critical {V : Type*} [Fintype V] {G : SimpleGraph V} (hT : Is13Tree G) :
    IsDegree3Critical (GT G) := by
  classical
  refine ⟨GT_card_edgeFinset hT, ?_⟩
  -- (C) 临界性
  intro s hne hne_univ
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ v : s, 2 < ((GT G).induce s).degree v`
  by_cases hA : ∃ a : V, Sum.inl a ∈ s
  · -- 情形 1:`S` 含某个原顶点 ⟹ 传播到全体 ⟹ `S = V(G(T))`,矛盾
    obtain ⟨a₀, ha₀⟩ := hA
    have hall : ∀ a : V, Sum.inl a ∈ s →
        ∀ w : V ⊕ Bool, (GT G).Adj (Sum.inl a) w → w ∈ s := by
      intro a ha w hw
      -- `deg_{G(T)}(inl a) = 3 ≤ deg_{G(T)[S]}(inl a)`,故 `inl a` 的邻居全在 `S` 里。
      -- 实例显式传入:`hcon` 里的实例来自 `IsDegree3Critical` 的定义(classical 闭项),
      -- 与这里 `inferInstance` 合成的不语法相同,只能靠显式参数对接。
      exact mem_of_adj_of_degree_le (GT G) s ⟨Sum.inl a, ha⟩ _ _
        (le_trans (le_of_eq (GT_degree_inl hT a)) (hcon ⟨Sum.inl a, ha⟩)) hw
    have hclosed : ∀ a b : V, G.Adj a b → Sum.inl a ∈ s → Sum.inl b ∈ s := fun a b hab ha =>
      hall a ha (Sum.inl b) (by simpa using hab)
    have hwalk : ∀ (u b : V), G.Walk u b → Sum.inl u ∈ s → Sum.inl b ∈ s := by
      intro u b p
      induction p with
      | nil => exact id
      | cons h _ ih => exact fun hu => ih (hclosed _ _ h hu)
    have hAll : ∀ b : V, Sum.inl b ∈ s := by
      intro b
      obtain ⟨p⟩ := hT.isTree.connected.preconnected a₀ b
      exact hwalk a₀ b p ha₀
    obtain ⟨a₁, ha₁⟩ := hT.leafFinset_nonempty
    have hleaf : IsLeaf G a₁ := isLeaf_iff_degree_eq_one.mpr (mem_leafFinset.mp ha₁)
    have hx : Sum.inr false ∈ s := hall a₁ (hAll a₁) _ (by simpa using hleaf)
    have hy : Sum.inr true ∈ s := hall a₁ (hAll a₁) _ (by simpa using hleaf)
    refine hne_univ (Set.eq_univ_iff_forall.mpr ?_)
    rintro (b | q)
    · exact hAll b
    · cases q
      · exact hx
      · exact hy
  · -- 情形 2:`S ⊆ {x, y}`,任取一点度 `≤ 2`
    push_neg at hA
    obtain ⟨v₀, hv₀⟩ := hne
    have hsub : s ⊆ ({Sum.inr false, Sum.inr true} : Set (V ⊕ Bool)) := by
      rintro (b | q) hb
      · exact absurd hb (hA b)
      · cases q <;> simp
    have hcard : Fintype.card s ≤ 2 := by
      have h1 : s.toFinset ⊆ ({Sum.inr false, Sum.inr true} : Set (V ⊕ Bool)).toFinset :=
        Set.toFinset_subset_toFinset.mpr hsub
      have h2 := Finset.card_le_card h1
      rw [Set.toFinset_card] at h2
      refine le_trans h2 ?_
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      exact le_trans (Finset.card_insert_le _ _) (by simp)
    have hdeg : ((GT G).induce s).degree ⟨v₀, hv₀⟩ ≤ 2 :=
      le_trans (Finset.card_le_univ _) hcard
    have h3 := hcon ⟨v₀, hv₀⟩
    omega

end Erdos815
