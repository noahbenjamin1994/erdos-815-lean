/-
# Lemma 2.1(i) —— `G(T)` 的奇圈长 ↔ `T` 的 leaf-leaf 路径长

论文 §2 Lemma 2.1(i) 原文:

> (i) The graph `G(T)` contains a cycle of length `2k + 1` ⟺ `T` contains a leaf-leaf
>     path of length `2k − 2`.
>
> **Proof.** For (i), let `C` be a `(2k + 1)`-cycle in `G(T)`. Notice that since `T` is an
> even tree, `G(T) − xy` is bipartite. So `C` must contain the edge `xy` and hence
> `C − x − y` must be a leaf-leaf path of length `2k − 2` as required.

T1.2 只需要 ⟹ 方向,所以本文件只做 ⟹。把 `2k + 1` / `2k − 2` 改写成 `ℓ + 3` / `ℓ`
(`ℓ` 偶且 `ℓ > 0`),**纯粹是为了避开 `ℕ` 的截断减法** —— 二者在 `k ≥ 2` 时同义,
而 `ℓ = 2k − 2` 的写法在 Lean 里会把 `k = 0, 1` 的退化情形混进来。
`ℓ > 0` 是必需的:`ℓ = 0` 对应 3-圈 `x–y–leaf–x`,它给出的「长 0 的 leaf-leaf 路径」
两端是同一个点,不满足 `IsLeafLeafPath` 里的 `u ≠ v`。本链路只用 `ℓ = 20`,不受影响。

## 证明骨架(与论文逐句对应)

**(A) `G(T) − xy` 二部** —— 论文 "since `T` is an even tree, `G(T) − xy` is bipartite"。
`T` 是树 ⟹ 有 2-染色 `cT`;`T` 是偶树 ⟹ **所有叶子同色**(两叶子间的路径长为偶,
由 `Coloring.even_length_iff_congr` 得同色)。把 `x, y` 都染成叶子色的反色,
即得 `G(T) − xy` 的 2-染色:`G(T) − xy` 的边只有「树内边」和「叶子–{x,y}」两类,
两类都被这个染色分开。见 `gtColoring`。

**(B) 奇圈必用 `xy`** —— 论文 "So `C` must contain the edge `xy`"。
若 `C` 不含 `xy`,`C` 整条落在 `G(T) − xy` 里,而二部图里的闭迹长度必偶。见 `edge_xy_mem_edges_of_odd`。

**(C) `C − x − y` 是 leaf-leaf 路径** —— 论文 "hence `C − x − y` must be a leaf-leaf path"。
把 `C` 旋到 `x` 起点后剥三条边:`x → y`(即 `xy`)、`y → a`、`b → x`。
剩下的 `r : b ⇝ a` 长度为 `ℓ`,支撑集不含 `x, y`,于是可以**降回 `T`**(`exists_walk_of_support_inl`);
`a, b` 是叶子,因为 `y`(resp. `x`)在 `G(T)` 里除对方外只与叶子相邻。见 `leafPath_of_cycle_cons`。

**(C′) `xy` 未必是首边** —— 论文一句话带过,Lean 里要补:旋到 `x` 之后 `xy` 可能是**末**边。
此时改用 `C.reverse`(同为圈、同长),其首边就是 `xy`。
「`xy` 只能是首边或末边」的理由:圈的支撑集去头后无重复,`x` 只出现在两端,
所以除首末两条外没有边含 `x`。见 `cycle_cons_xy`。

## 与 `Defs.lean` 的关系

本文件**没有修改 `Defs.lean`**,因此蓝图无需改动。特别地,论文说的「`T` 是偶树」
在 `Defs.lean` 里已取「所有 leaf-leaf 路径长为偶」这一等价形式,不必先造出二部划分;
(A) 里需要的划分是本文件**现造**的(`gtColoring`),这正是当初把 `IsEvenTree`
写成路径形式所预留的接口。
-/
import Erdos815.Defs
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

namespace Erdos815

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## 1. 把支撑集全在 `.inl` 上的 `G(T)`-walk 降回 `T`

这是 (C) 里「`C − x − y` 是 `T` 中的路径」那一步的唯一技术内容。结论写成
`w.support = p.support.map Sum.inl` 而不是「长度相等 + 顶点一一对应」,
是因为这个更强的形式**一次性**给出长度(`List.length_map`)与 `IsPath`
(`List.Nodup.of_map`),省掉两轮转写。 -/

/-- 支撑集全落在 `.inl` 上的 `G(T)`-walk 可以降回 `T`,且支撑集逐点对应。 -/
lemma exists_walk_of_support_inl :
    ∀ {u v : V ⊕ Bool} (w : (GT G).Walk u v) {a b : V},
      u = Sum.inl a → v = Sum.inl b →
      (∀ z ∈ w.support, ∃ c : V, z = Sum.inl c) →
      ∃ p : G.Walk a b, w.support = p.support.map Sum.inl := by
  intro u v w
  induction w with
  | nil =>
      intro a b ha hb _
      subst ha
      obtain rfl : a = b := by simpa using hb
      exact ⟨Walk.nil, by simp⟩
  | @cons u' v' w' h p ih =>
      intro a b ha hb hs
      subst ha
      -- `v'` 是 `p` 的起点,故落在 `cons h p` 的支撑集里,于是它形如 `.inl c`
      obtain ⟨c, rfl⟩ : ∃ c : V, v' = Sum.inl c := by
        refine hs v' ?_
        simp [Walk.support_cons]
      obtain ⟨q, hq⟩ := ih (a := c) (b := b) rfl hb (by
        intro z hz
        exact hs z (by simp [Walk.support_cons, hz]))
      refine ⟨Walk.cons (by simpa using h) q, ?_⟩
      simp [Walk.support_cons, hq]

/-! ## 2. (A) `G(T) − xy` 的二部划分 -/

/-- `T` 的一个 `Bool` 值 2-染色(树必有,见 `SimpleGraph.IsTree.coloringTwo`)。 -/
noncomputable def treeColoring (hT : G.IsTree) : G.Coloring Bool :=
  G.recolorOfEquiv finTwoEquiv hT.coloringTwo

/-- **偶树的所有叶子同色。**

论文 §1 的 even tree 定义就是「所有叶子在二部划分的同一类」;`Defs.lean` 取的是等价形式
「所有 leaf-leaf 路径长为偶」。这条引理把后者翻回前者:两叶子间在树里有路径,
其长为偶 ⟹ 由 `Coloring.even_length_iff_congr` 两端同色。 -/
lemma leaf_color_eq (hT : G.IsTree) (he : IsEvenTree G) (cT : G.Coloring Bool)
    {u v : V} (hu : IsLeaf G u) (hv : IsLeaf G v) : cT u = cT v := by
  classical
  by_cases huv : u = v
  · rw [huv]
  · -- 树连通,取一条 `u ⇝ v` 的道路(`bypass` 把 walk 化成 path)
    obtain ⟨w⟩ := hT.connected u v
    have hp : (w.bypass).IsPath := w.bypass_isPath
    have hlen : w.bypass.length % 2 = 0 := he u v w.bypass ⟨hp, hu, hv, huv⟩
    have heven : Even w.bypass.length := Nat.even_iff.mpr hlen
    exact Bool.eq_iff_iff.mpr ((cT.even_length_iff_congr w.bypass).mp heven)

open scoped Classical in
/-- 叶子在 `cT` 下的**公共颜色的反色** —— 这就是要分给 `x`、`y` 的颜色。

没有叶子时取值无所谓(`G(T) − xy` 里 `x, y` 此时是孤立点),故用 `dite` 兜底。
这样写的好处是**不需要 `Fintype V`**,也不需要先证「1-3 树必有叶子」。 -/
noncomputable def coColor (G : SimpleGraph V) (cT : G.Coloring Bool) : Bool :=
  if h : ∃ a : V, IsLeaf G a then !(cT h.choose) else true

lemma coColor_ne (hT : G.IsTree) (he : IsEvenTree G) (cT : G.Coloring Bool)
    {a : V} (ha : IsLeaf G a) : cT a ≠ coColor G cT := by
  have hex : ∃ a : V, IsLeaf G a := ⟨a, ha⟩
  rw [coColor, dite_cond_eq_true (by simpa using hex),
    leaf_color_eq hT he cT ha hex.choose_spec]
  simp

/-- **`G(T) − xy` 的 2-染色**(论文:*since `T` is an even tree, `G(T) − xy` is bipartite*)。

原顶点 `.inl a` 用树染色 `cT a`,新顶点 `x = .inr false`、`y = .inr true` 统一用叶子的反色。
三类边各自被分开:树内边由 `cT` 合法性;叶子–`{x,y}` 边由 `coColor_ne`;
而 `xy` 边已经被删掉。 -/
noncomputable def gtColoring (hT : G.IsTree) (he : IsEvenTree G) :
    ((GT G).deleteEdges {s(Sum.inr false, Sum.inr true)}).Coloring Bool :=
  Coloring.mk
    (fun z => match z with
      | .inl a => treeColoring hT a
      | .inr _ => coColor G (treeColoring hT))
    (by
      intro z w hzw
      rw [SimpleGraph.deleteEdges_adj] at hzw
      obtain ⟨hadj, hne⟩ := hzw
      match z, w with
      | .inl a, .inl b => exact (treeColoring hT).valid (by simpa using hadj)
      | .inl a, .inr p => exact coColor_ne hT he _ (by simpa using hadj)
      | .inr p, .inl b => exact (coColor_ne hT he _ (by simpa using hadj)).symm
      | .inr p, .inr q =>
          -- `x` 与 `y` 之间那条边已被删去,这一支不可能出现
          exfalso; revert hne hadj; cases p <;> cases q <;> simp)

/-! ## 3. (B) 奇圈必含边 `xy` -/

/-- **奇长闭迹必用到边 `xy`。**

论文:*So `C` must contain the edge `xy`*。反证:若不含,整条闭迹落在二部的
`G(T) − xy` 里,而二部图里闭迹两端同色 ⟹ 长度为偶。 -/
lemma edge_xy_mem_edges_of_odd (hT : G.IsTree) (he : IsEvenTree G) {u : V ⊕ Bool}
    (c : (GT G).Walk u u) (hodd : ¬ Even c.length) :
    s(Sum.inr false, Sum.inr true) ∈ c.edges := by
  by_contra hmem
  refine hodd ?_
  -- `c` 避开了 `xy`,于是可以搬到 `G(T) − xy` 里
  have hlen := Walk.length_transfer
    (p := c) (H := (GT G).deleteEdges {s(Sum.inr false, Sum.inr true)})
    (by
      simp only [SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
      exact fun e he' => ⟨c.edges_subset_edgeSet he', by rintro rfl; exact hmem he'⟩)
  rw [← hlen]
  exact ((gtColoring hT he).even_length_iff_congr _).mpr Iff.rfl

/-! ## 4. (C) 剥掉 `x`、`y` 得到 leaf-leaf 路径 -/

/-- **核心一步**:首边恰为 `xy` 的圈 `x → y ⇝ x`,去掉 `x`、`y` 后是 `T` 里的 leaf-leaf 路径。

论文:*hence `C − x − y` must be a leaf-leaf path of length `2k − 2` as required*。 -/
lemma leafPath_of_cycle_cons {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (hxy : (GT G).Adj (Sum.inr false) (Sum.inr true))
    (q : (GT G).Walk (Sum.inr true) (Sum.inr false))
    (hcyc : (Walk.cons hxy q).IsCycle) (hlen : q.length = ℓ + 2) :
    HasLeafLeafPath G ℓ := by
  obtain ⟨hqp, -⟩ := (Walk.cons_isCycle_iff q hxy).mp hcyc
  -- 剥第二条边 `y → a`
  obtain ⟨a, h₂, q₂, rfl⟩ :=
    Walk.exists_eq_cons_of_ne (by simp : (Sum.inr true : V ⊕ Bool) ≠ Sum.inr false) q
  obtain ⟨hq₂p, hy⟩ := (Walk.cons_isPath_iff h₂ q₂).mp hqp
  have hq₂len : q₂.length = ℓ + 1 := by simpa using hlen
  -- `a ≠ x`:否则 `q₂ : Walk x x` 是道路,只能是 `nil`,与长度 `ℓ + 1 > 0` 矛盾
  have hax : a ≠ (Sum.inr false : V ⊕ Bool) := by
    rintro rfl
    have := Walk.length_eq_zero_iff.mpr (Walk.isPath_iff_nil.mp hq₂p)
    omega
  -- 剥最后一条边:把 `q₂` 反过来,剥 `x → b`
  obtain ⟨b, h₃, r, hr⟩ :=
    Walk.exists_eq_cons_of_ne (Ne.symm hax) q₂.reverse
  have hq₂rp : q₂.reverse.IsPath := hq₂p.reverse
  rw [hr] at hq₂rp
  obtain ⟨hrp, hx⟩ := (Walk.cons_isPath_iff h₃ r).mp hq₂rp
  have hrlen : r.length = ℓ := by
    have : q₂.reverse.length = r.length + 1 := by rw [hr]; simp
    simp only [Walk.length_reverse, hq₂len] at this
    omega
  -- `r` 的支撑集落在 `q₂` 的支撑集里(`q₂.reverse` 的支撑集是它的逆序)
  have hrsub : ∀ z ∈ r.support, z ∈ q₂.support := by
    intro z hz
    have : z ∈ q₂.reverse.support := by rw [hr]; simp [Walk.support_cons, hz]
    simpa using this
  -- `a` 是叶子:`y` 在 `G(T)` 里除 `x` 外只和叶子相邻,而 `a ≠ x`
  obtain ⟨a', rfl, hleafa⟩ : ∃ a' : V, a = Sum.inl a' ∧ IsLeaf G a' := by
    match a with
    | .inl a' => exact ⟨a', rfl, by simpa using h₂⟩
    | .inr p => cases p <;> simp_all
  -- `b` 是叶子:`x` 在 `G(T)` 里除 `y` 外只和叶子相邻,而 `b ≠ y`(`y ∉ q₂.support`)
  obtain ⟨b', rfl, hleafb⟩ : ∃ b' : V, b = Sum.inl b' ∧ IsLeaf G b' := by
    match b with
    | .inl b' => exact ⟨b', rfl, by simpa using h₃⟩
    | .inr p =>
        exfalso
        cases p with
        | false => exact (SimpleGraph.irrefl (G := GT G)) h₃
        | true => exact hy (hrsub _ (by simp [Walk.start_mem_support]))
  -- `r` 的支撑集全是 `.inl`:它既不含 `x`(`cons h₃ r` 是道路)也不含 `y`
  have hsupp : ∀ z ∈ r.support, ∃ c : V, z = Sum.inl c := by
    intro z hz
    match z with
    | .inl c => exact ⟨c, rfl⟩
    | .inr p =>
        exfalso
        cases p with
        | false => exact hx hz
        | true => exact hy (hrsub _ hz)
  -- 降回 `T`
  obtain ⟨s, hs⟩ := exists_walk_of_support_inl r rfl rfl hsupp
  have hslen : s.length = ℓ := by
    have h1 : r.support.length = s.support.length := by rw [hs]; simp
    rw [Walk.length_support, Walk.length_support, hrlen] at h1
    omega
  have hsp : s.IsPath := by
    rw [Walk.isPath_def]
    exact List.Nodup.of_map Sum.inl (hs ▸ hrp.support_nodup)
  have hne : b' ≠ a' := by
    rintro rfl
    have := Walk.length_eq_zero_iff.mpr (Walk.isPath_iff_nil.mp hsp)
    omega
  exact ⟨b', a', s, ⟨hsp, hleafb, hleafa, hne⟩, hslen⟩

/-- **(C′)**:以 `x` 为起点、含边 `xy` 的圈,可以(必要时取 `reverse`)写成首边为 `xy` 的形式。

论文把这一步和 (C) 合并成了一句话,但 Lean 里必须补:旋到 `x` 之后 `xy` 可能是**末**边。
理由是圈里含 `x` 的边只有首、末两条 —— 去掉首边后剩下的道路 `p` 只在末端碰到 `x`。 -/
lemma cycle_cons_xy {c : (GT G).Walk (Sum.inr false) (Sum.inr false)}
    (hcyc : c.IsCycle) (hmem : s(Sum.inr false, Sum.inr true) ∈ c.edges) :
    ∃ (hxy : (GT G).Adj (Sum.inr false) (Sum.inr true))
      (q : (GT G).Walk (Sum.inr true) (Sum.inr false)),
      (Walk.cons hxy q).IsCycle ∧ q.length + 1 = c.length := by
  classical
  -- 圈非空,剥出首边 `x → w₁`
  obtain ⟨w₁, h₁, p, rfl⟩ := Walk.not_nil_iff.mp hcyc.not_nil
  obtain ⟨hpp, hpe⟩ := (Walk.cons_isCycle_iff p h₁).mp hcyc
  by_cases hw₁ : w₁ = Sum.inr true
  · -- `xy` 就是首边,直接用 `c` 本身
    subst hw₁
    exact ⟨h₁, p, hcyc, by simp⟩
  · -- `xy` 不是首边 ⟹ 它在 `p` 里 ⟹ 它只能是 `p` 的末边 ⟹ 用 `c.reverse`
    have hmem' : s(Sum.inr false, Sum.inr true) ∈ p.edges := by
      rw [Walk.edges_cons, List.mem_cons] at hmem
      rcases hmem with h | h
      · exact absurd (by simpa using h.symm) hw₁
      · exact h
    -- 把 `p` 反过来剥首边 `x → wL`
    have hne : (Sum.inr false : V ⊕ Bool) ≠ w₁ := h₁.ne
    obtain ⟨wL, hL, m, hm⟩ := Walk.exists_eq_cons_of_ne hne p.reverse
    have hmp : (Walk.cons hL m).IsPath := hm ▸ hpp.reverse
    obtain ⟨hmpath, hxm⟩ := (Walk.cons_isPath_iff hL m).mp hmp
    -- `p = m.reverse.concat hL.symm`,故 `p` 的边 = `m.reverse` 的边 ++ 末边 `s(wL, x)`
    have hpeq : p = m.reverse.concat hL.symm := by
      rw [← p.reverse_reverse, hm]; simp [Walk.concat]
    -- `xy` 不可能落在 `m.reverse` 里,否则 `x ∈ m.support`
    have hwL : wL = Sum.inr true := by
      rw [hpeq, Walk.edges_concat, List.concat_eq_append, List.mem_append,
        List.mem_singleton] at hmem'
      rcases hmem' with h | h
      · exact absurd (by simpa using m.reverse.fst_mem_support_of_mem_edges h) hxm
      · rw [Sym2.eq_iff] at h
        rcases h with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact absurd h2 (by simp)
        · exact h2.symm
    subst hwL
    -- `c.reverse = cons hL (m.concat h₁.symm)`,首边正是 `xy`
    refine ⟨hL, m.concat h₁.symm, ?_, ?_⟩
    · have : (Walk.cons h₁ p).reverse = Walk.cons hL (m.concat h₁.symm) := by
        rw [Walk.reverse_cons, hm]; simp [Walk.concat]
      exact this ▸ hcyc.reverse
    · rw [hpeq]; simp [Walk.concat]

/-! ## 5. Lemma 2.1(i) 的 ⟹ 方向,以及本步交付的接口 -/

/-- **Lemma 2.1(i),⟹ 方向。**

> The graph `G(T)` contains a cycle of length `2k + 1` ⟹ `T` contains a leaf-leaf path
> of length `2k − 2`.

这里写作「长 `ℓ + 3` 的圈 ⟹ 长 `ℓ` 的 leaf-leaf 路径」(`ℓ` 偶且非零),
与论文的 `2k + 1` / `2k − 2` 在 `k ≥ 2` 时同义,详见文件头。 -/
theorem lemma_2_1_i_mp (hT : G.IsTree) (he : IsEvenTree G) {ℓ : ℕ}
    (hℓ : Even ℓ) (hℓ0 : ℓ ≠ 0) (h : HasCycleOfLength (GT G) (ℓ + 3)) :
    HasLeafLeafPath G ℓ := by
  classical
  obtain ⟨v, c, hcyc, hclen⟩ := h
  -- (B):`ℓ + 3` 是奇数,故 `c` 必含边 `xy`
  have hodd : ¬ Even c.length := by
    rw [hclen]
    obtain ⟨t, rfl⟩ := hℓ
    simp only [Nat.even_iff]
    omega
  have hmem := edge_xy_mem_edges_of_odd hT he c hodd
  -- 把圈旋到 `x` 起点
  have hx : (Sum.inr false : V ⊕ Bool) ∈ c.support := c.fst_mem_support_of_mem_edges hmem
  have hrotcyc : (c.rotate _ hx).IsCycle := hcyc.rotate hx
  have hrotmem : s(Sum.inr false, Sum.inr true) ∈ (c.rotate _ hx).edges :=
    (Walk.rotate_edges c _ hx).perm.mem_iff.mpr hmem
  -- (C′) + (C)
  obtain ⟨hxy, q, hqcyc, hqlen⟩ := cycle_cons_xy hrotcyc hrotmem
  refine leafPath_of_cycle_cons hℓ0 hxy q hqcyc ?_
  simp only [Walk.length_rotate, hclen] at hqlen
  omega

/-- **本步交付的接口** —— 第 5 步组装 T1.2 时唯一会用到的东西。

论文 Proof of Theorem 1.2:

> Since `Tₙ` is an even 1-3-tree, we can use part (i) of Lemma 2.1 and the fact that `Tₙ`
> does not contain a leaf-leaf path of length 20 to conclude that `Gₙ` contains no cycle
> of length 23.

`23 = 20 + 3`(论文写作 `2·11 + 1`,对应 `2k − 2 = 20`)。 -/
theorem no_cycle_23_of_no_leaf_path_20 (hT : Is13Tree G) (he : IsEvenTree G)
    (h20 : ¬ HasLeafLeafPath G 20) : ¬ HasCycleOfLength (GT G) 23 := by
  intro hc
  exact h20 (lemma_2_1_i_mp hT.isTree he (by decide) (by decide) (by simpa using hc))

end Erdos815
