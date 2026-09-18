/-
# Lemma 2.2 —— odd-even 序列下 `T(x₁…xₙ)` 的 leaf-leaf 路径长度刻画

Narins–Pokrovskiy–Szabó, arXiv:1408.5289, §2。原文四条与证明见
`.work/erdos-815/notes/paper-section2.md`。

**论文的证明思路**(逐字):leaf-leaf 路径按它与主路径 `v₁…vₙ` 的交分类,
交总是一条(可能为空的)路径:

| 交 | 路径形态 | 长度 |
|---|---|---|
| 空 | 落在某棵深度 `xᵢ−1` 的完美二叉树内部 | `2m`,`0 ≤ m < max xᵢ` |
| 单点 | 该点必是 `v₁` 或 `vₙ`,路径穿过深度 `x₁`(或 `xₙ`)的完美树的根 | `2x₁` 或 `2xₙ` |
| 线段 `vᵢ…vⱼ` | 从第 `i` 块的叶子上到 `vᵢ`,走主路径到 `vⱼ`,再下到第 `j` 块的叶子 | `xᵢ + (j−i) + xⱼ` |

## 我们的形式化路线(与论文等价,但更短)

**(i) 偶性不走分类。** 我们在 `TreeBasic.lean` 里给出显式的分级函数
`tRank = tIdx + tHeight`,它在**每条边上恰好变化 1**,于是
`tColor := tRank % 2` 是一个真 2-染色;而叶子的 rank 恒为 `i + xᵢ`,
odd-even(`xᵢ ≡ i+1 mod 2`)使它恒为奇数 ⟹ **所有叶子同色** ⟹
任意 leaf-leaf 路径长为偶(Mathlib `Coloring.even_length_iff_congr`)。
这比论文「三分类后逐类验算奇偶」短得多,结论完全相同。

**(iv) 的 "only if" 走分类,但只需两档。** 我们证的分类定理是
`leafLeafPath_length`:

* 两端叶子同属一块(`tIdx u = tIdx v`):长度 `≤ 2xᵢ` —— **只要上界**。
  上界不需要构造出最短路,只要造**任意一条** walk:无圈图里
  `path.length ≤ walk.length`(`path_length_le_walk`)。
  这一档合并了论文的「交为空」与「交为单点」两类。
* 两端叶子不同块:长度**恰为** `xᵢ + xⱼ + |i−j|`。这里需要等号,
  因此必须构造出那条**典范路径**并证它 `IsPath`,再用树的路径唯一性
  (`IsAcyclic.subsingleton_path`)把给定路径与它等同。

(iv) 的 only-if 随即得到:`2m > 2·max xᵢ ≥ 2xᵢ` 排除第一档。

## 本链路不需要的部分

(ii)、(iii) 与 (iv) 的 "if" 方向要求**构造出**各长度的路径,是论文 §3 的需求;
本任务(T1.3(ii) → T1.2)只用 (i) 与 (iv) 的 only-if。两者仍按原文陈述在此,
证明留待需要时补。

## 一处与原文的形式差异(已核对,记录在案)

原文 (ii) 写 `0 ≤ m < max xᵢ`,`m = 0` 对应「长度 0 的 leaf-leaf 路径」,
即起讫为**同一片**叶子的平凡路径。`Defs.lean` 的 `IsLeafLeafPath` 要求两端点
**相异**(论文 §1 "paths going between two leaves",且 Lemma 2.1 的用法要求相异),
故我们把 (ii) 的下界写成 `1 ≤ m`。这不影响任何被使用的结论:
本链路只用 (i) 与 (iv)。
-/
import Erdos815.TreeBasic
import Erdos815.TreeStruct
import Erdos815.TreeWalks
import Erdos815.TreeConstruct

namespace Erdos815

open SimpleGraph

variable {n : ℕ} {x : ℕ → ℕ}

/-! ## 0. 记号 -/

/-- `max_{i=1}^{n} xᵢ`(0-based:`x` 在 `0 … n−1` 上的最大值)。 -/
def xMax (x : ℕ → ℕ) (n : ℕ) : ℕ := (Finset.range n).sup x

lemma le_xMax {i : ℕ} (hi : i < n) : x i ≤ xMax x n :=
  Finset.le_sup (f := x) (Finset.mem_range.mpr hi)

/-! ## 1. 无圈图里「路径不长于任意 walk」 -/

/-- 无圈图中,两点间的路径长度 `≤` 任意一条同端点 walk 的长度。

理由:`w.bypass` 是同端点的路径,由路径唯一性它就等于 `p`,而
`w.bypass.length ≤ w.length`。**这条是上界档的全部技术内容** ——
不必构造最短路,随便给一条 walk 就够。 -/
lemma path_length_le_walk {W : Type*} {H : SimpleGraph W} (hac : H.IsAcyclic)
    {u v : W} {p : H.Walk u v} (hp : p.IsPath) (w : H.Walk u v) :
    p.length ≤ w.length := by
  classical
  have h := (hac.subsingleton_path u v).elim (⟨p, hp⟩ : H.Path u v) ⟨w.bypass, w.bypass_isPath⟩
  have hpe : p = w.bypass := congrArg Subtype.val h
  rw [hpe]
  exact w.length_bypass_le_length

/-- 无圈图中,两条同端点的路径长度相等。 -/
lemma path_length_eq {W : Type*} {H : SimpleGraph W} (hac : H.IsAcyclic)
    {u v : W} {p q : H.Walk u v} (hp : p.IsPath) (hq : q.IsPath) :
    p.length = q.length := by
  have h := (hac.subsingleton_path u v).elim (⟨p, hp⟩ : H.Path u v) ⟨q, hq⟩
  exact congrArg (fun r : H.Path u v => r.val.length) h

/-! ## 2. Lemma 2.2 (i) —— 无奇长 leaf-leaf 路径 -/

/-- **Lemma 2.2(i).** *The tree `T(x₁ . . . xₙ)` contains no leaf-leaf path of odd length.*

证明:`tColoring` 是 `T(x₁…xₙ)` 的 2-染色,odd-even 条件使**所有叶子同色**
(`leaf_tColor`),于是任意 leaf-leaf 路径两端同色 ⟹ 长度为偶。 -/
theorem lemma_2_2_i (hp : TParams x n) (hoe : IsOddEvenFin x n)
    {u v : TVtx x n} (p : (TTree x n).Walk u v)
    (hpp : IsLeafLeafPath (TTree x n) p) : p.length % 2 = 0 := by
  obtain ⟨-, hu, hv, -⟩ := hpp
  have hcu : tColor u = true := leaf_tColor hoe ((isLeaf_iff hp u).mp hu)
  have hcv : tColor v = true := leaf_tColor hoe ((isLeaf_iff hp v).mp hv)
  have heven : Even p.length := by
    rw [SimpleGraph.Coloring.even_length_iff_congr (tColoring x n) p]
    show (tColor u = true) ↔ (tColor v = true)
    rw [hcu, hcv]
  exact Nat.even_iff.mp heven

/-- **Lemma 2.2(i) 的推论.** *In particular, `T(x₁, . . . , xₙ)` is an even tree.* -/
theorem TTree_isEvenTree (hp : TParams x n) (hoe : IsOddEvenFin x n) :
    IsEvenTree (TTree x n) := fun _ _ p hpp => lemma_2_2_i hp hoe p hpp

/-! ## 3. 分类定理

论文「按与主路径的交分类」的 Lean 形态。两档:

* **同块**(交为空 或 交为单点 `v₁`/`vₙ`):长度 `≤ 2xᵢ`;
* **异块**(交为线段 `vᵢ…vⱼ`):长度**恰为** `xᵢ + xⱼ + |i−j|`。

同块只给上界是刻意的:(iv) 的 only-if 只需要用 `2m > 2·max xᵢ` 把这一档排除掉,
给出精确值(`2xᵢ` 或 `2(xᵢ−1−c)`)反而要多证一堆用不上的东西。 -/

/-- 上界档:两端叶子同属一块时,leaf-leaf 路径长 `≤ 2xᵢ`。

见证 walk:从 `u` 沿父边上到 `vᵢ`(长 `xᵢ`),再沿父边下到 `v`(长 `xᵢ`)。
`u`、`v` 同块但可能不同侧,这条 walk 两种情形都合法。 -/
lemma leafLeafPath_le_of_idx_eq (hp : TParams x n)
    {u v : TVtx x n} (p : (TTree x n).Walk u v) (hpp : IsLeafLeafPath (TTree x n) p)
    (hidx : tIdx u.val = tIdx v.val) :
    p.length ≤ 2 * x ((tIdx u.val : ℕ)) := by
  obtain ⟨hpath, hu, hv, -⟩ := hpp
  obtain ⟨w, hw⟩ := exists_leafWalk_of_idx_eq ((isLeaf_iff hp u).mp hu)
    ((isLeaf_iff hp v).mp hv) hidx
  calc p.length ≤ w.length := path_length_le_walk TTree_isAcyclic hpath w
    _ = 2 * x ((tIdx u.val : ℕ)) := hw

/-- 精确档:两端叶子不同块时,leaf-leaf 路径长恰为 `xᵢ + xⱼ + |i−j|`。

见证路径:`u ⇝ vᵢ`(长 `xᵢ`)`⇝ vⱼ`(长 `|i−j|`)`⇝ v`(长 `xⱼ`)。
需要证它 `IsPath`(支撑集无重复:三段的 `(tIdx, tHeight)` 坐标两两不同),
再用树的路径唯一性得到等号。 -/
lemma leafLeafPath_eq_of_idx_ne (hp : TParams x n)
    {u v : TVtx x n} (p : (TTree x n).Walk u v) (hpp : IsLeafLeafPath (TTree x n) p)
    (hidx : tIdx u.val ≠ tIdx v.val) :
    p.length =
      x ((tIdx u.val : ℕ)) + x ((tIdx v.val : ℕ)) + idxDist (tIdx u.val) (tIdx v.val) := by
  obtain ⟨hpath, hu, hv, -⟩ := hpp
  obtain ⟨q, hq, hqlen⟩ := exists_leafPath_of_idx_ne ((isLeaf_iff hp u).mp hu)
    ((isLeaf_iff hp v).mp hv) hidx
  rw [path_length_eq TTree_isAcyclic hpath hq, hqlen]

/-- **分类定理**(论文三分类的 Lean 形态,合并成两档)。 -/
theorem leafLeafPath_length (hp : TParams x n)
    {u v : TVtx x n} (p : (TTree x n).Walk u v) (hpp : IsLeafLeafPath (TTree x n) p) :
    (tIdx u.val = tIdx v.val ∧ p.length ≤ 2 * x ((tIdx u.val : ℕ))) ∨
    (tIdx u.val ≠ tIdx v.val ∧
      p.length = x ((tIdx u.val : ℕ)) + x ((tIdx v.val : ℕ)) +
        idxDist (tIdx u.val) (tIdx v.val)) := by
  by_cases h : tIdx u.val = tIdx v.val
  · exact Or.inl ⟨h, leafLeafPath_le_of_idx_eq hp p hpp h⟩
  · exact Or.inr ⟨h, leafLeafPath_eq_of_idx_ne hp p hpp h⟩

/-! ## 4. Lemma 2.2 (iv) 的 "only if" —— 本步交付给 step 5 的接口 -/

/-- **Lemma 2.2(iv) 的 "only if" 方向。**

*For every `m > maxⁿ_{i=1} xᵢ`, the tree `T(x₁ . . . xₙ)` contains a leaf-leaf path of
length `2m` **only if** there are two distinct integers `i` and `j` such that
`xᵢ + xⱼ + |i − j| = 2m`.*

注意这一条**不需要** odd-even 假设(论文把 (i)–(iv) 放在同一个 "Let `x₁,…,xₙ` be an
odd-even sequence" 之下,但 only-if 方向的论证只用到分类定理)。

产物形态与 `Defs.lean` 的 `IsKAvoiding` 逐字同形:`x i + x j + idxDist i j`。 -/
theorem lemma_2_2_iv_only_if (hp : TParams x n) {m : ℕ} (hm : xMax x n < m)
    (h : HasLeafLeafPath (TTree x n) (2 * m)) :
    ∃ i j : Fin n, i ≠ j ∧ x (i : ℕ) + x (j : ℕ) + idxDist i j = 2 * m := by
  obtain ⟨u, v, p, hpp, hlen⟩ := h
  rcases leafLeafPath_length hp p hpp with ⟨-, hle⟩ | ⟨hne, heq⟩
  · -- 同块档:长度 `≤ 2xᵢ ≤ 2·max < 2m`,与 `p.length = 2m` 矛盾
    exfalso
    have h1 : x ((tIdx u.val : ℕ)) ≤ xMax x n := le_xMax (tIdx u.val).2
    rw [hlen] at hle
    omega
  · exact ⟨tIdx u.val, tIdx v.val, hne, by rw [← heq, hlen]⟩

/-! ## 5. 论文四条的完整陈述

(ii)、(iii) 与 (iv) 的 "if" 方向本链路不使用(它们是论文 §3 的需求),
按原文陈述在此,证明待补。 -/

/-- **Lemma 2.2(ii).** *For every integer `m`, `0 ≤ m < maxⁿ_{i=1} xᵢ`, the tree
`T(x₁ . . . xₙ)` contains a leaf-leaf path of length `2m`.*

`1 ≤ m`:见文件头「与原文的形式差异」—— `m = 0` 对应起讫同一片叶子的平凡路径,
被 `IsLeafLeafPath` 的「两端相异」排除。 -/
theorem lemma_2_2_ii (hp : TParams x n) (hoe : IsOddEvenFin x n)
    {m : ℕ} (hm1 : 1 ≤ m) (hm : m < xMax x n) :
    HasLeafLeafPath (TTree x n) (2 * m) := by
  -- 取达到上确界的那一块 `i`(`n ≥ 2 > 0` 使 `range n` 非空),于是 `m < xᵢ`,
  -- 即 `m ≤ xᵢ − 1`,`TreeConstruct.hasLeafLeafPath_branch` 在第 `i` 块的
  -- **第一侧**(`s = false`,任何块都允许)里给出长 `2m` 的分叉路径。
  have hne : (Finset.range n).Nonempty :=
    Finset.nonempty_range_iff.mpr (by have := hp.two_le; omega)
  obtain ⟨i₀, hi₀mem, hi₀⟩ := Finset.exists_mem_eq_sup (Finset.range n) hne x
  have hi₀lt : i₀ < n := Finset.mem_range.mp hi₀mem
  have hmx : m < x i₀ := by rw [← hi₀]; exact hm
  exact hasLeafLeafPath_branch hp ⟨i₀, hi₀lt⟩ false (Or.inl rfl) hm1
    (by show m ≤ x i₀ - 1; omega)

/-- **Lemma 2.2(iii).** *For `m = maxⁿ_{i=1} xᵢ`, the tree `T(x₁ . . . xₙ)` contains a
leaf-leaf path of length `2m` if and only if either `max{x₁, xₙ} = maxⁿ_{i=1} xᵢ` or
there are two distinct integers `i` and `j` such that `xᵢ + xⱼ + |i − j| = 2m`.*

`max{x₁, xₙ}` 在 0-based 下是 `max (x 0) (x (n−1))`。 -/
theorem lemma_2_2_iii (hp : TParams x n) (hoe : IsOddEvenFin x n)
    {m : ℕ} (hm : m = xMax x n) :
    HasLeafLeafPath (TTree x n) (2 * m) ↔
      (max (x 0) (x (n - 1)) = xMax x n ∨
        ∃ i j : Fin n, i ≠ j ∧ x (i : ℕ) + x (j : ℕ) + idxDist i j = 2 * m) := by
  have hn2 : 2 ≤ n := hp.two_le
  have h0n : (0 : ℕ) < n := by omega
  have hlastn : n - 1 < n := by omega
  constructor
  · -- ⟹:用分类定理。异块档直接落进右析取项;同块档必须证明这一块就是两侧块。
    rintro ⟨u, v, p, hpp, hlen⟩
    rcases leafLeafPath_length hp p hpp with ⟨hidx, hle⟩ | ⟨hne, heq⟩
    · refine Or.inl ?_
      obtain ⟨hpath, hu, hv, -⟩ := hpp
      have hlu : IsTLeafRaw x n u.val := (isLeaf_iff hp u).mp hu
      have hlv : IsTLeafRaw x n v.val := (isLeaf_iff hp v).mp hv
      have hxi : x ((tIdx u.val : ℕ)) ≤ xMax x n := le_xMax (tIdx u.val).2
      have hxpos : 1 ≤ x ((tIdx u.val : ℕ)) := hp.pos _ (tIdx u.val).2
      -- 先排除「两片叶子在同一侧」:那样 `p.length ≤ 2(xᵢ−1) < 2xᵢ ≤ 2·max = 2m`
      have hts : twoSided n (tIdx u.val) := by
        rcases twoSided_or_sameSideWalk hlu hlv hidx with hts | ⟨w, hw⟩
        · exact hts
        · exfalso
          have hb := path_length_le_walk TTree_isAcyclic hpath w
          rw [hlen, hw] at hb
          omega
      -- 同块档只有上界,但 `p.length = 2m = 2·max ≥ 2xᵢ` 反过来把它顶成等号
      have hxeq : x ((tIdx u.val : ℕ)) = xMax x n := by rw [hlen] at hle; omega
      -- `twoSided` ⟹ `i = 0` 或 `i = n−1`,于是 `max (x 0) (x (n−1)) ≥ xᵢ = max`
      refine le_antisymm (max_le (le_xMax h0n) (le_xMax hlastn)) ?_
      rcases hts with hc | hc
      · calc xMax x n = x ((tIdx u.val : ℕ)) := hxeq.symm
          _ = x 0 := by rw [hc]
          _ ≤ max (x 0) (x (n - 1)) := le_max_left _ _
      · calc xMax x n = x ((tIdx u.val : ℕ)) := hxeq.symm
          _ = x (n - 1) := by rw [hc]
          _ ≤ max (x 0) (x (n - 1)) := le_max_right _ _
    · exact Or.inr ⟨tIdx u.val, tIdx v.val, hne, by rw [← heq, hlen]⟩
  · rintro (hmax | ⟨i, j, hij, hsum⟩)
    · -- ⟸ 左析取项:`x 0` 或 `x (n−1)` 取到上确界,该块是两侧块,穿心路径长 `2xᵢ = 2m`
      have key : ∀ i : Fin n, twoSided n i → x (i : ℕ) = m →
          HasLeafLeafPath (TTree x n) (2 * m) := by
        intro i hts hxi
        have h := hasLeafLeafPath_twoSided hp i hts
        rwa [hxi] at h
      rcases max_choice (x 0) (x (n - 1)) with hc | hc
      · exact key ⟨0, h0n⟩ (Or.inl rfl) (by rw [hm, ← hmax, hc])
      · exact key ⟨n - 1, hlastn⟩ (Or.inr rfl) (by rw [hm, ← hmax, hc])
    · -- ⟸ 右析取项:与 (iv) 的 ⟸ 完全相同的异块构造
      have h := hasLeafLeafPath_of_idx_ne hp hij
      rwa [hsum] at h

/-- **Lemma 2.2(iv).** *For every `m > maxⁿ_{i=1} xᵢ`, the tree `T(x₁ . . . xₙ)` contains
a leaf-leaf path of length `2m` if and only if there are two distinct integers `i` and `j`
such that `xᵢ + xⱼ + |i − j| = 2m`.*

⟹ 方向即 `lemma_2_2_iv_only_if`(已闭合);⟸ 方向要构造路径,本链路不使用。 -/
theorem lemma_2_2_iv (hp : TParams x n) (hoe : IsOddEvenFin x n)
    {m : ℕ} (hm : xMax x n < m) :
    HasLeafLeafPath (TTree x n) (2 * m) ↔
      ∃ i j : Fin n, i ≠ j ∧ x (i : ℕ) + x (j : ℕ) + idxDist i j = 2 * m := by
  constructor
  · exact lemma_2_2_iv_only_if hp hm
  · -- ⟸:`i ≠ j` 时取两块各自「最左」的那片叶子,`exists_leafPath_of_idx_ne`
    -- 给出的路径长恰为 `xᵢ + xⱼ + |i−j| = 2m`(`TreeConstruct.hasLeafLeafPath_of_idx_ne`)
    rintro ⟨i, j, hij, hsum⟩
    have h := hasLeafLeafPath_of_idx_ne hp hij
    rwa [hsum] at h

end Erdos815
