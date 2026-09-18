/-
# `T(x₁ … xₙ)` 里**给定长度**的 leaf-leaf 路径(step 5 补齐 Lemma 2.2 的构造方向)

`TreeWalks.lean` 造的是「给定两片叶子,连接它们的典范 walk / path」;本文件反过来:
**给定一个长度,造出取到该长度的一对叶子与它们之间的路径**。这是论文 Lemma 2.2
(ii)(iii)(iv-if) 的全部技术内容,对应原文最后一句
*"one must only note that a perfect tree of depth `d` contains a leaf-leaf path of every
even length"*。

## 三种长度来源(与论文三分类一一对应)

| 论文的情形 | 本文件的构造 | 长度 |
|---|---|---|
| 交为空:两片叶子在同一棵子树内分叉 | `hasLeafLeafPath_branch` | `2m`,`1 ≤ m ≤ xᵢ − 1` |
| 交为单点 `vᵢ`(仅 `i = 1` 或 `i = n`) | `hasLeafLeafPath_twoSided` | `2xᵢ` |
| 交为线段 `vᵢ…vⱼ` | `hasLeafLeafPath_of_idx_ne`(复用 `exists_leafPath_of_idx_ne`) | `xᵢ + xⱼ + \|i−j\|` |

## 构造用的两条归纳(都照抄 `exists_upPath_aux` 的骨架)

* `exists_partialUp`:从 `treeV i s (p ++ c)` 沿父边走到 `treeV i s c`,长 `|p|`,是路径;
  支撑集不变量写成 **`∃ q, |q| ≤ |p| ∧ z.val = treeV i s (q ++ c)`**。
* `exists_upPath_sideAux`:`exists_upPath` 的加强版,支撑集里额外记住**侧** `s`
  (`w = vᵢ` 或 `w.val = treeV i s _`)。B4 的不交性只能靠侧来分。

### 为什么不变量写成 `q ++ c` 而不是「`l'` 是 `p ++ c` 的后缀」

工单原本的建议是记后缀关系,再靠「`replicate m false` 的后缀全是 `false`」
对「`A ++ [true]` 的非空后缀含 `true`」来区分两半。后者需要一条
「非空后缀含末元素」的引理,Mathlib 不直给,要自己从 `IsSuffix` 拆。

改用 `q ++ c` 之后,两半的公共尾巴分别取 `false :: c` 与 `true :: c`,
于是「两半支撑集相交」⟹ `q₁ ++ false :: c = q₂ ++ true :: c`,
两边长度相同 ⟹ `|q₁| = |q₂|` ⟹ `List.append_inj` ⟹ `false = true`。
**一条列表引理搞定,完全不碰后缀结构。**
-/
import Erdos815.TreeBasic
import Erdos815.TreeStruct
import Erdos815.TreeWalks

namespace Erdos815

open SimpleGraph

variable {n : ℕ} {x : ℕ → ℕ}

/-! ## 0. 小工具 -/

/-- 一条路径的支撑集去掉首点后不再含首点(`TreeWalks.lean` 里同名的是 `private`)。 -/
private lemma head_notMem_tail' {W : Type*} {H : SimpleGraph W} {a b : W}
    {p : H.Walk a b} (hp : p.IsPath) : a ∉ p.support.tail := by
  have hnd : (a :: p.support.tail).Nodup := by
    rw [Walk.cons_tail_support]
    exact (Walk.isPath_def p).mp hp
  exact (List.nodup_cons.mp hnd).1

/-- 同块同侧的两个子树结点相等 ⟹ 列表相等。

单独抽出来是因为 `injection` 在 `i`、`s` 两个分量**语法相同**时会把它们直接消掉,
产出的等式条数随上下文变化(实测 `injection h with _ _ e` 会报 "No goals to be solved"),
用 `injEq` + `simp` 是稳定写法。 -/
lemma treeV_list_inj {i : Fin n} {s : Bool} {l m : List Bool}
    (h : (TV.treeV i s l : TV n) = TV.treeV i s m) : l = m := by
  simpa using h

/-- 子树根总是合法的(只要该侧允许、且 `xᵢ ≥ 1`)。 -/
lemma TValid_root {i : Fin n} {s : Bool} {l : List Bool}
    (h : TValid x n (.treeV i s l)) : TValid x n (.treeV i s ([] : List Bool)) := by
  refine ⟨h.1, ?_⟩
  have := h.2
  simp only [List.length_nil]
  omega

/-! ## 1. (B1) 部分上行路径:`treeV i s (p ++ c)` ⇝ `treeV i s c` -/

/-- **部分上行路径**。长度恰为 `|p|`,是一条路径,且支撑集里每个点的 raw 形态都是
`treeV i s (q ++ c)`(同块、同侧、同尾巴),`|q| ≤ |p|`。

这条不变量正好够 `hasLeafLeafPath_branch` 里两半的不交性(见文件头)。 -/
lemma exists_partialUp {i : Fin n} {s : Bool} (c : List Bool) :
    ∀ (p : List Bool) (h : TValid x n (.treeV i s (p ++ c)))
      (hc : TValid x n (.treeV i s c)),
      ∃ w : (TTree x n).Walk (tT x i s (p ++ c) h) (tT x i s c hc),
        w.length = p.length ∧ w.IsPath ∧
        ∀ z ∈ w.support, ∃ q : List Bool, q.length ≤ p.length ∧
          z.val = TV.treeV i s (q ++ c) := by
  intro p
  induction p with
  | nil =>
      intro h hc
      refine ⟨Walk.nil, by simp, by simp, ?_⟩
      intro z hz
      simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
      subst hz
      exact ⟨[], by simp, rfl⟩
  | cons b m ih =>
      intro h hc
      have hpar : TValid x n (.treeV i s (m ++ c)) := TValid_tail h
      obtain ⟨w, hlen, hpath, hsupp⟩ := ih hpar hc
      have hadj : (TTree x n).Adj (tT x i s (b :: m ++ c) h) (tT x i s (m ++ c) hpar) :=
        Or.inl ⟨rfl, rfl, b, rfl⟩
      refine ⟨Walk.cons hadj w, by simp [hlen], ?_, ?_⟩
      · -- 新头结点的深度是 `|m| + |c| + 1`,比整段的上界 `|m| + |c|` 大,故不在段内
        rw [Walk.cons_isPath_iff]
        refine ⟨hpath, fun hmem => ?_⟩
        obtain ⟨q, hq, hqe⟩ := hsupp _ hmem
        have he : TV.treeV i s (b :: m ++ c) = TV.treeV i s (q ++ c) := hqe
        have hl := congrArg (fun l : List Bool => l.length) (treeV_list_inj he)
        simp only [List.length_append, List.length_cons] at hl
        omega
      · intro z hz
        simp only [Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact ⟨b :: m, by simp, rfl⟩
        · obtain ⟨q, hq, hqe⟩ := hsupp z hz
          exact ⟨q, by simp only [List.length_cons]; omega, hqe⟩

/-! ## 2. (B2) 上到子树根的 walk(只要 walk,不要路径) -/

/-- 从子树结点沿父边走到该子树的根 `uᵢ^{(s)}`,长度 `|l|`。

`[S4-11]` 的 ⟹ 方向只用它做**上界**(`path_length_le_walk`),故不必证 `IsPath`。 -/
lemma exists_rootWalk {i : Fin n} {s : Bool} :
    ∀ (l : List Bool) (h : TValid x n (.treeV i s l))
      (h0 : TValid x n (.treeV i s ([] : List Bool))),
      ∃ w : (TTree x n).Walk (tT x i s l h) (tT x i s [] h0), w.length = l.length := by
  intro l
  induction l with
  | nil => intro h h0; exact ⟨Walk.nil, by simp⟩
  | cons b m ih =>
      intro h h0
      obtain ⟨w, hw⟩ := ih (TValid_tail h) h0
      have hadj : (TTree x n).Adj (tT x i s (b :: m) h) (tT x i s m (TValid_tail h)) :=
        Or.inl ⟨rfl, rfl, b, rfl⟩
      exact ⟨Walk.cons hadj w, by simp [hw]⟩

/-- **同一棵子树里两点之间的 walk**,长度 `|lu| + |lv|`(上到根再下来)。 -/
lemma exists_sameSubtreeWalk {i : Fin n} {s : Bool} {lu lv : List Bool}
    (hu : TValid x n (.treeV i s lu)) (hv : TValid x n (.treeV i s lv)) :
    ∃ w : (TTree x n).Walk (tT x i s lu hu) (tT x i s lv hv),
      w.length = lu.length + lv.length := by
  obtain ⟨w1, h1⟩ := exists_rootWalk lu hu (TValid_root hu)
  obtain ⟨w2, h2⟩ := exists_rootWalk lv hv (TValid_root hu)
  exact ⟨w1.append w2.reverse, by simp [h1, h2]⟩

/-! ## 3. (B4 的原料)带侧信息的上行路径 -/

/-- `exists_upPath_aux` 的加强版:支撑集额外记住**侧**。

`TreeWalks.lean` 里那条记的是 `tHeight` 上界与「是否端点」,够异块档用;
B4(两片叶子在 `vᵢ` 的两侧)必须靠侧来分开两半,故在此单独归纳一次,
**不改动已编译的 `TreeWalks.lean`**。 -/
lemma exists_upPath_sideAux {i : Fin n} {s : Bool} :
    ∀ (l : List Bool) (h : TValid x n (.treeV i s l)),
      ∃ p : (TTree x n).Walk (tT x i s l h) (tP x i),
        p.length = l.length + 1 ∧ p.IsPath ∧
        ∀ w ∈ p.support, tHeight w.val ≤ l.length + 1 ∧
          (w = tP x i ∨ ∃ l' : List Bool, w.val = TV.treeV i s l') := by
  intro l
  induction l with
  | nil =>
      intro h
      have hadj : (TTree x n).Adj (tT x i s [] h) (tP x i) := ⟨rfl, rfl⟩
      have hne : tT x i s [] h ≠ tP x i := fun hc => by
        have hcv : TV.treeV i s ([] : List Bool) = TV.pathV i := congrArg Subtype.val hc
        simp at hcv
      refine ⟨Walk.cons hadj Walk.nil, by simp, by simp [hne], ?_⟩
      intro w hw
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨by simp, Or.inr ⟨[], rfl⟩⟩
      · exact ⟨by simp, Or.inl rfl⟩
  | cons b m ih =>
      intro h
      obtain ⟨p, hlen, hpath, hsupp⟩ := ih (TValid_tail h)
      have hadj : (TTree x n).Adj (tT x i s (b :: m) h) (tT x i s m (TValid_tail h)) :=
        Or.inl ⟨rfl, rfl, b, rfl⟩
      refine ⟨Walk.cons hadj p, by simp [hlen], ?_, ?_⟩
      · rw [Walk.cons_isPath_iff]
        refine ⟨hpath, fun hmem => ?_⟩
        have hb := (hsupp _ hmem).1
        simp only [tT_val, tHeight_treeV, List.length_cons] at hb
        omega
      · intro w hw
        simp only [Walk.support_cons, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact ⟨by simp, Or.inr ⟨b :: m, rfl⟩⟩
        · obtain ⟨h1, h2⟩ := hsupp w hw
          exact ⟨by simp only [List.length_cons]; omega, h2⟩

/-! ## 4. (B5) 叶子的存在性 -/

/-- 第 `i` 块第 `s` 侧「一路向左」的那片叶子的 raw 路径:`replicate (xᵢ − 1) false`。 -/
lemma TValid_leftmostLeaf {i : Fin n} {s : Bool} (hs : s = false ∨ twoSided n i)
    (hx : 1 ≤ x (i : ℕ)) :
    TValid x n (.treeV i s (List.replicate (x (i : ℕ) - 1) false)) := by
  refine ⟨hs, ?_⟩
  simp only [List.length_replicate]
  omega

lemma isTLeafRaw_leftmostLeaf {i : Fin n} {s : Bool} (hx : 1 ≤ x (i : ℕ)) :
    IsTLeafRaw x n (.treeV i s (List.replicate (x (i : ℕ) - 1) false)) := by
  simp only [IsTLeafRaw, List.length_replicate]
  omega

/-! ## 5. (B3) 同一棵子树内的分叉路径,长度 `2m` -/

/-- **同子树分叉**:在第 `i` 块第 `s` 侧的子树里,取两片叶子,它们的最近公共祖先
在根下方 `m − 1` 层,于是它们之间的路径长恰为 `2m`(`1 ≤ m ≤ xᵢ − 1`)。

两片叶子:`treeV i s (replicate (m−1) false ++ false :: c)` 与
`treeV i s (replicate (m−1) false ++ true :: c)`,其中
`c := replicate (xᵢ − 1 − m) false` 是把深度补满到 `xᵢ − 1` 的填充。

路径 = (左叶 ⇝ `false :: c` ⇝ `c`) ++ (右叶 ⇝ `true :: c` ⇝ `c`)⁻¹。 -/
lemma hasLeafLeafPath_branch (hp : TParams x n) (i : Fin n) (s : Bool)
    (hs : s = false ∨ twoSided n i) {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ x (i : ℕ) - 1) :
    HasLeafLeafPath (TTree x n) (2 * m) := by
  classical
  have hx : 1 ≤ x (i : ℕ) := hp.pos _ i.2
  set c : List Bool := List.replicate (x (i : ℕ) - 1 - m) false with hcdef
  set A : List Bool := List.replicate (m - 1) false with hAdef
  have hclen : c.length = x (i : ℕ) - 1 - m := by simp [hcdef]
  have hAlen : A.length = m - 1 := by simp [hAdef]
  -- 四个结点的合法性
  have hvc : TValid x n (.treeV i s c) := ⟨hs, by rw [hclen]; omega⟩
  have hvb : ∀ b : Bool, TValid x n (.treeV i s (b :: c)) := fun b =>
    ⟨hs, by simp only [List.length_cons, hclen]; omega⟩
  have hvl : ∀ b : Bool, TValid x n (.treeV i s (A ++ b :: c)) := fun b =>
    ⟨hs, by simp only [List.length_append, List.length_cons, hclen, hAlen]; omega⟩
  -- 两半
  obtain ⟨w1, hw1len, hw1path, hw1supp⟩ :=
    exists_partialUp (x := x) (i := i) (s := s) (false :: c) A (hvl false) (hvb false)
  obtain ⟨w2, hw2len, hw2path, hw2supp⟩ :=
    exists_partialUp (x := x) (i := i) (s := s) (true :: c) A (hvl true) (hvb true)
  have e1 : (TTree x n).Adj (tT x i s (false :: c) (hvb false)) (tT x i s c hvc) :=
    Or.inl ⟨rfl, rfl, false, rfl⟩
  have e2 : (TTree x n).Adj (tT x i s (true :: c) (hvb true)) (tT x i s c hvc) :=
    Or.inl ⟨rfl, rfl, true, rfl⟩
  refine ⟨tT x i s (A ++ false :: c) (hvl false), tT x i s (A ++ true :: c) (hvl true),
    (w1.concat e1).append (w2.concat e2).reverse, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- `IsPath`:支撑集 = `w1.support ++ [root] ++ w2.support.reverse`,三块两两不交
    have hsupp_eq : ((w1.concat e1).append (w2.concat e2).reverse).support =
        (w1.support ++ [tT x i s c hvc]) ++ w2.support.reverse := by
      simp [Walk.support_append, Walk.support_concat, Walk.support_reverse]
    rw [Walk.isPath_def, hsupp_eq, List.nodup_append, List.nodup_append]
    have hw1nd : w1.support.Nodup := (Walk.isPath_def w1).mp hw1path
    have hw2nd : w2.support.Nodup := (Walk.isPath_def w2).mp hw2path
    -- 公共点 `root = treeV i s c` 不在任何一半里(那里的列表都比 `c` 长)
    have hroot : ∀ (d : Bool) (w : (TTree x n).Walk
        (tT x i s (A ++ d :: c) (hvl d)) (tT x i s (d :: c) (hvb d))),
        (∀ z ∈ w.support, ∃ q : List Bool, q.length ≤ A.length ∧
          z.val = TV.treeV i s (q ++ d :: c)) → tT x i s c hvc ∉ w.support := by
      intro d w hsupp hmem
      obtain ⟨q, -, hqe⟩ := hsupp _ hmem
      have he : TV.treeV i s c = TV.treeV i s (q ++ d :: c) := hqe
      have hl := congrArg (fun l : List Bool => l.length) (treeV_list_inj he)
      simp only [List.length_append, List.length_cons] at hl
      omega
    refine ⟨⟨hw1nd, by simp, ?_⟩, by simpa using hw2nd, ?_⟩
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact fun hab => hroot false w1 hw1supp (hab ▸ ha)
    · intro a ha b hb hab
      rw [List.mem_reverse] at hb
      obtain ⟨q2, -, hq2⟩ := hw2supp b hb
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · obtain ⟨q1, -, hq1⟩ := hw1supp a ha
        have heq : TV.treeV i s (q1 ++ false :: c) = TV.treeV i s (q2 ++ true :: c) := by
          rw [← hq1, ← hq2, hab]
        have e := treeV_list_inj heq
        have hlen := congrArg (fun l : List Bool => l.length) e
        simp only [List.length_append, List.length_cons] at hlen
        have h2 := (List.append_inj e (by omega)).2
        simp at h2
      · simp only [List.mem_singleton] at ha
        subst ha
        exact hroot true w2 hw2supp (hab ▸ hb)
  · -- 左端是叶子
    refine (isLeaf_iff hp _).mpr ?_
    simp only [tT_val, IsTLeafRaw, List.length_append, List.length_cons, hclen, hAlen]
    omega
  · refine (isLeaf_iff hp _).mpr ?_
    simp only [tT_val, IsTLeafRaw, List.length_append, List.length_cons, hclen, hAlen]
    omega
  · -- 两片叶子相异:去掉公共前缀 `A` 后首元素一个 `false` 一个 `true`
    intro hcon
    have hv : TV.treeV i s (A ++ false :: c) = TV.treeV i s (A ++ true :: c) :=
      congrArg Subtype.val hcon
    have h2 := List.append_cancel_left (treeV_list_inj hv)
    simp at h2
  · -- 长度 `(|A| + 1) + (|A| + 1) = 2m`
    rw [Walk.length_append, Walk.length_reverse, Walk.length_concat, Walk.length_concat,
      hw1len, hw2len, hAlen]
    omega

/-! ## 6. (B4) 穿过 `vᵢ` 的两侧路径,长度 `2xᵢ` -/

/-- **两侧穿心**:`i = 1` 或 `i = n` 时 `vᵢ` 挂了两棵子树,各取一片叶子,
路径「上到 `vᵢ` 再下去」长恰为 `2xᵢ`。

不交性只能靠**侧**:第一半的点要么是 `vᵢ` 要么形如 `treeV i false _`,
第二半(去掉首点 `vᵢ` 之后)全形如 `treeV i true _`。 -/
lemma hasLeafLeafPath_twoSided (hp : TParams x n) (i : Fin n) (hts : twoSided n i) :
    HasLeafLeafPath (TTree x n) (2 * x (i : ℕ)) := by
  classical
  have hx : 1 ≤ x (i : ℕ) := hp.pos _ i.2
  set l₀ : List Bool := List.replicate (x (i : ℕ) - 1) false with hl₀def
  have hl₀len : l₀.length = x (i : ℕ) - 1 := by simp [hl₀def]
  have hv0 : TValid x n (.treeV i false l₀) := TValid_leftmostLeaf (Or.inl rfl) hx
  have hv1 : TValid x n (.treeV i true l₀) := TValid_leftmostLeaf (Or.inr hts) hx
  obtain ⟨pu, hulen, hupath, husupp⟩ := exists_upPath_sideAux (x := x) (i := i) (s := false) l₀ hv0
  obtain ⟨pv, hvlen, hvpath, hvsupp⟩ := exists_upPath_sideAux (x := x) (i := i) (s := true) l₀ hv1
  refine ⟨tT x i false l₀ hv0, tT x i true l₀ hv1, pu.append pv.reverse, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
    refine ⟨(Walk.isPath_def pu).mp hupath,
      List.Nodup.sublist (List.tail_sublist _)
        ((Walk.isPath_def pv.reverse).mp hvpath.reverse), ?_⟩
    intro a ha b hb hab
    -- `b` 在 `pv.reverse.support.tail` 里 ⇒ `b ∈ pv.support` 且 `b ≠ vᵢ`
    have hbmem : b ∈ pv.support := by
      have h1 := List.mem_of_mem_tail hb
      rwa [Walk.support_reverse, List.mem_reverse] at h1
    have hbne : b ≠ tP x i := by
      intro hc; exact head_notMem_tail' hvpath.reverse (hc ▸ hb)
    obtain ⟨lb, hlb⟩ : ∃ l' : List Bool, b.val = TV.treeV i true l' := by
      rcases (hvsupp b hbmem).2 with hc | hc
      · exact absurd hc hbne
      · exact hc
    rcases (husupp a ha).2 with hc | ⟨la, hla⟩
    · -- `a = vᵢ` 是主路径点,`b` 是子树结点
      rw [hc] at hab
      have : TV.pathV i = TV.treeV i true lb := by rw [← hlb, ← hab]; rfl
      simp at this
    · -- 两边都是子树结点,但侧不同
      have : TV.treeV i false la = TV.treeV i true lb := by rw [← hla, ← hlb, hab]
      simp at this
  · exact (isLeaf_iff hp _).mpr (isTLeafRaw_leftmostLeaf hx)
  · exact (isLeaf_iff hp _).mpr (isTLeafRaw_leftmostLeaf hx)
  · intro hcon
    have hv : TV.treeV i false l₀ = TV.treeV i true l₀ := congrArg Subtype.val hcon
    simp at hv
  · rw [Walk.length_append, Walk.length_reverse, hulen, hvlen, hl₀len]
    omega

/-! ## 7. `[S4-11]` 的 ⟹ 方向需要的二分 -/

/-- **同块两片叶子的二分**:要么这一块是「两侧块」(`i = 1` 或 `i = n`),
要么两片叶子**同侧**,于是有一条长 `2(xᵢ − 1)` 的 walk 连接它们。

用途:`lemma_2_2_iii` 的 ⟹ 方向里,同块档给出 `p.length ≤ 2xᵢ`;若两叶同侧,
无圈图里 `p.length ≤ 2(xᵢ−1) < 2xᵢ = 2m`,与 `p.length = 2m` 矛盾 ——
于是必然落在 `twoSided` 那一侧。 -/
lemma twoSided_or_sameSideWalk_aux {k : Fin n} {su sv : Bool} {lu lv : List Bool}
    (hvalu : TValid x n (.treeV k su lu)) (hvalv : TValid x n (.treeV k sv lv))
    (hlu : lu.length + 1 = x (k : ℕ)) (hlv : lv.length + 1 = x (k : ℕ)) :
    twoSided n k ∨
      ∃ w : (TTree x n).Walk (tT x k su lu hvalu) (tT x k sv lv hvalv),
        w.length = 2 * (x (k : ℕ) - 1) := by
  by_cases hs : su = sv
  · subst hs
    obtain ⟨w, hw⟩ := exists_sameSubtreeWalk hvalu hvalv
    exact Or.inr ⟨w, by rw [hw]; omega⟩
  · refine Or.inl ?_
    cases su with
    | false =>
        cases sv with
        | false => exact absurd rfl hs
        | true =>
            rcases hvalv.1 with hc | hc
            · exact absurd hc (by simp)
            · exact hc
    | true =>
        rcases hvalu.1 with hc | hc
        · exact absurd hc (by simp)
        · exact hc

/-- 一般形态(顶点用 `TVtx`,不预设构造子形式)。 -/
lemma twoSided_or_sameSideWalk {u v : TVtx x n}
    (hu : IsTLeafRaw x n u.val) (hv : IsTLeafRaw x n v.val)
    (hidx : tIdx u.val = tIdx v.val) :
    twoSided n (tIdx u.val) ∨
      ∃ w : (TTree x n).Walk u v, w.length = 2 * (x ((tIdx u.val : ℕ)) - 1) := by
  rcases hau : u.val with k | ⟨k, su, lu⟩
  · rw [hau] at hu; exact absurd hu (by simp [IsTLeafRaw])
  · have hvalu : TValid x n (.treeV k su lu) := hau ▸ u.2
    have hlu : lu.length + 1 = x (k : ℕ) := by rw [hau] at hu; exact hu
    have hueq : u = tT x k su lu hvalu := TVtx_ext (by rw [hau]; rfl)
    subst hueq
    rcases hav : v.val with k' | ⟨k', sv, lv⟩
    · rw [hav] at hv; exact absurd hv (by simp [IsTLeafRaw])
    · have hvalv : TValid x n (.treeV k' sv lv) := hav ▸ v.2
      have hlv : lv.length + 1 = x (k' : ℕ) := by rw [hav] at hv; exact hv
      have hkk : k' = k := by
        have h := hidx
        rw [hav] at h
        exact h.symm
      subst hkk
      have hveq : v = tT x k' sv lv hvalv := TVtx_ext (by rw [hav]; rfl)
      subst hveq
      exact twoSided_or_sameSideWalk_aux hvalu hvalv hlu hlv

/-! ## 8. 异块:复用 `exists_leafPath_of_idx_ne` -/

/-- **异块构造**:任给 `i ≠ j`,存在长恰为 `xᵢ + xⱼ + |i−j|` 的 leaf-leaf 路径。 -/
lemma hasLeafLeafPath_of_idx_ne (hp : TParams x n) {i j : Fin n} (hij : i ≠ j) :
    HasLeafLeafPath (TTree x n) (x (i : ℕ) + x (j : ℕ) + idxDist i j) := by
  have hxi : 1 ≤ x (i : ℕ) := hp.pos _ i.2
  have hxj : 1 ≤ x (j : ℕ) := hp.pos _ j.2
  have hvi : TValid x n (.treeV i false (List.replicate (x (i : ℕ) - 1) false)) :=
    TValid_leftmostLeaf (Or.inl rfl) hxi
  have hvj : TValid x n (.treeV j false (List.replicate (x (j : ℕ) - 1) false)) :=
    TValid_leftmostLeaf (Or.inl rfl) hxj
  set u : TVtx x n := tT x i false (List.replicate (x (i : ℕ) - 1) false) hvi with hudef
  set v : TVtx x n := tT x j false (List.replicate (x (j : ℕ) - 1) false) hvj with hvdef
  have hlu : IsTLeafRaw x n u.val := isTLeafRaw_leftmostLeaf hxi
  have hlv : IsTLeafRaw x n v.val := isTLeafRaw_leftmostLeaf hxj
  have hiu : tIdx u.val = i := rfl
  have hiv : tIdx v.val = j := rfl
  have hne : tIdx u.val ≠ tIdx v.val := by rw [hiu, hiv]; exact hij
  obtain ⟨p, hpath, hplen⟩ := exists_leafPath_of_idx_ne hlu hlv hne
  refine ⟨u, v, p, ⟨hpath, (isLeaf_iff hp u).mpr hlu, (isLeaf_iff hp v).mpr hlv, ?_⟩, ?_⟩
  · intro hc; exact hne (congrArg (fun w : TVtx x n => tIdx w.val) hc)
  · rw [hplen, hiu, hiv]

end Erdos815
