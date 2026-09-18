/-
# `T(x₁ … xₙ)` 是 1-3 树(step 4 辅助文件)

论文一句话带过:*"Notice that for any sequence `x₁, . . . , xₙ` of positive integers,
the tree `T(x₁ . . . xₙ)` is a 1-3 tree."* —— 但「它确实是一棵**树**」在 Lean 里必须证。
本文件补三块:

1. **连通**:任意顶点沿子树往上走到 `vᵢ`,再沿主路径走到 `v₁`。
2. **无圈**:用 `isAcyclic_iff_forall_adj_isBridge` —— 对每条边给一个割函数
   (`TreeBasic.lean` 的 `cutSeg` / `cutRoot` / `cutIn`),证明删掉这条边后两端不可达。
   比「取圈上 rank 最大的点看它的两个圈邻居」那条路好写得多:后者要拆 Mathlib 的
   `IsCycle` 支撑结构,前者只是三个 `Bool` 函数的逐边验算。
3. **度只有 1 或 3**:直接引用 `TreeBasic.lean` 的 `pathV_isDeg3` / `treeV_isDeg3` /
   `treeV_isLeaf`。
-/
import Erdos815.TreeBasic

namespace Erdos815

open SimpleGraph

variable {n : ℕ} {x : ℕ → ℕ}

/-! ## 0. 由 raw 顶点等式恢复顶点的构造子形式

`TVtx x n` 是 `def` 包着的 subtype,**不能** `obtain ⟨w, hw⟩ := v` 拆开(拆出来的类型
只与 `TTree x n` 的顶点类型定义相等而非语法相等,后续 `Adj`/`Walk` 全部类型不匹配)。
正确姿势是对 `v.val` 做 `rcases`,再用下面两个引理把 `v` 本身写回 `tP` / `tT`。 -/

/-- 由 raw 顶点等式恢复 `tP` 形式。 -/
lemma eq_tP_of_val {a : TVtx x n} {k : Fin n} (h : a.val = TV.pathV k) : a = tP x k :=
  TVtx_ext (by simp [h])

/-- 由 raw 顶点等式恢复 `tT` 形式。 -/
lemma eq_tT_of_val {a : TVtx x n} {k : Fin n} {t : Bool} {l : List Bool}
    (h : a.val = TV.treeV k t l) (hv : TValid x n (TV.treeV k t l)) : a = tT x k t l hv :=
  TVtx_ext (by simp [h])

/-! ## 1. 连通性 -/

/-- 对根到结点的路径 `l` 归纳:`l = []` 时一条边 `uᵢ—vᵢ`;
`l = b :: m` 时先沿父边下降一层到 `m`(`|m| + 1 < |l| + 1 ≤ xᵢ`,故 `m` 合法),再用归纳假设。 -/
lemma reachable_tP_of_treeV_aux {i : Fin n} {s : Bool} : ∀ (l : List Bool)
    (h : TValid x n (TV.treeV i s l)), (TTree x n).Reachable (tT x i s l h) (tP x i) := by
  intro l
  induction l with
  | nil =>
      intro h
      exact SimpleGraph.Adj.reachable
        (show tAdjRaw n (TV.treeV i s []) (TV.pathV i) from ⟨rfl, rfl⟩)
  | cons b m ih =>
      intro h
      have hm : TValid x n (TV.treeV i s m) := by
        refine ⟨h.1, ?_⟩
        have := h.2
        simp only [List.length_cons] at this
        omega
      exact (SimpleGraph.Adj.reachable
        (show tAdjRaw n (TV.treeV i s (b :: m)) (TV.treeV i s m) from
          Or.inl ⟨rfl, rfl, b, rfl⟩)).trans (ih hm)

/-- 从子树结点沿父边走到该子树的根 `uᵢ`,再一步到 `vᵢ`。 -/
lemma reachable_tP_of_treeV {i : Fin n} {s : Bool} {l : List Bool}
    (h : TValid x n (.treeV i s l)) :
    (TTree x n).Reachable (tT x i s l h) (tP x i) :=
  reachable_tP_of_treeV_aux l h

/-- 沿主路径从 `v_{k+1}` 退一步到 `v_k`,对 `k` 归纳即得所有点可达 `v₁`。 -/
lemma reachable_tP_zero (h0 : 0 < n) (i : Fin n) :
    (TTree x n).Reachable (tP x i) (tP x ⟨0, h0⟩) := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ m ih =>
      have hm : m < n := by omega
      exact (SimpleGraph.Adj.reachable
        (show tAdjRaw n (TV.pathV (⟨m + 1, hk⟩ : Fin n)) (TV.pathV (⟨m, hm⟩ : Fin n)) from
          Or.inr rfl)).trans (ih hm)

/-- 主路径上任意两点互相可达。 -/
lemma reachable_tP_tP (i j : Fin n) : (TTree x n).Reachable (tP x i) (tP x j) := by
  -- [S4-5] 两端都先走到 `v₁`,再把其中一段反过来
  have h0 : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  exact (reachable_tP_zero h0 i).trans (reachable_tP_zero h0 j).symm

/-- `T(x₁…xₙ)` 连通。 -/
lemma TTree_preconnected (hp : TParams x n) : (TTree x n).Preconnected := by
  -- [S4-6] 每个顶点先走到某个 `vᵢ`(路径点自身即是,子树结点用 `reachable_tP_of_treeV`),
  -- 而所有 `vᵢ` 两两可达
  classical
  have key : ∀ v : TVtx x n, ∃ i : Fin n, (TTree x n).Reachable v (tP x i) := by
    intro v
    rcases hv : v.val with i | ⟨i, s, l⟩
    · refine ⟨i, ?_⟩
      rw [eq_tP_of_val hv]
    · have hval : TValid x n (TV.treeV i s l) := hv ▸ v.2
      refine ⟨i, ?_⟩
      rw [eq_tT_of_val hv hval]
      exact reachable_tP_of_treeV hval
  intro u v
  obtain ⟨i, hi⟩ := key u
  obtain ⟨j, hj⟩ := key v
  exact hi.trans ((reachable_tP_tP i j).trans hj.symm)

/-! ## 2. 无圈

每条边都是桥:删掉它之后两端不可达,见证者是 `TreeBasic.lean` 里的三族割函数。 -/

/-- 给一条边配一个割函数:它在**删掉这条边之后**的每条边上取值不变,而在这条边两端取值不同,
于是删边后两端不可达,即这条边是桥。 -/
lemma isBridge_of_cut {u v : TVtx x n} (χ : TV n → Bool)
    (hconst : ∀ a b : TVtx x n, (TTree x n).Adj a b → s(a, b) ≠ s(u, v) → χ a.val = χ b.val)
    (hne : χ u.val ≠ χ v.val) : (TTree x n).IsBridge s(u, v) := by
  classical
  rw [SimpleGraph.isBridge_iff]
  refine not_reachable_of_cut (fun w : TVtx x n => χ w.val) ?_ hne
  intro a b hab
  rw [SimpleGraph.deleteEdges_adj] at hab
  exact hconst a b hab.1 (by simpa using hab.2)

/-- 主路径边 `vᵢ—vⱼ`(`j = i+1`)是桥:割函数 `cutSeg i` 按块下标是否 `≤ i` 分边。
子树内部的边与 `vₖ—uₖ` 都不改变块下标,主路径上的边 `vₖ—vₖ₊₁` 只在 `k = i` 时改变割值,
而那正是被删掉的这条边。 -/
lemma isBridge_seg {i j : Fin n} (hij : (i : ℕ) + 1 = (j : ℕ)) :
    (TTree x n).IsBridge s(tP x i, tP x j) := by
  classical
  refine isBridge_of_cut (cutSeg (i : ℕ)) ?_ ?_
  · rintro a b hab hne
    rcases ha : a.val with k | ⟨k, t, l⟩ <;> rcases hb : b.val with k' | ⟨k', t', l'⟩ <;>
      simp only [TTree_adj, ha, hb, tAdjRaw] at hab
    · -- 两端都在主路径上
      simp only [cutSeg, ha, hb, tIdx_pathV, decide_eq_decide]
      rcases hab with h1 | h1
      · by_cases hki : (k : ℕ) ≤ (i : ℕ)
        · by_cases hki' : (k' : ℕ) ≤ (i : ℕ)
          · exact decide_eq_decide.mpr (iff_of_true hki hki')
          · refine absurd ?_ hne
            rw [eq_tP_of_val ha, eq_tP_of_val hb,
              show k = i from Fin.val_injective (by omega),
              show k' = j from Fin.val_injective (by omega)]
        · exact decide_eq_decide.mpr (iff_of_false hki (by omega))
      · by_cases hki' : (k' : ℕ) ≤ (i : ℕ)
        · by_cases hki : (k : ℕ) ≤ (i : ℕ)
          · exact decide_eq_decide.mpr (iff_of_true hki hki')
          · refine absurd ?_ hne
            rw [eq_tP_of_val ha, eq_tP_of_val hb,
              show k = j from Fin.val_injective (by omega),
              show k' = i from Fin.val_injective (by omega)]
            exact Sym2.eq_swap
        · exact decide_eq_decide.mpr (iff_of_false (by omega) hki')
    · -- `vₖ—uₖ`:块下标不变
      simp [cutSeg, hab.1]
    · simp [cutSeg, hab.1]
    · -- 子树内部:块下标不变
      rcases hab with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> simp [cutSeg]
  · have hji : ¬ ((j : ℕ) ≤ (i : ℕ)) := by omega
    simp [cutSeg, hji]

/-- 边 `vᵢ—uᵢ^{(s)}` 是桥:割函数 `cutRoot i s` 标记「落在第 `(i,s)` 棵子树里」。
路径点恒取 `false`;子树内部的边不改变 `(i,s)`;别的 `vₖ—uₖ^{(t)}` 两端都取 `false`。 -/
lemma isBridge_root {i : Fin n} {s : Bool} (hv : TValid x n (TV.treeV i s [])) :
    (TTree x n).IsBridge s(tP x i, tT x i s [] hv) := by
  classical
  refine isBridge_of_cut (cutRoot i s) ?_ (by simp [cutRoot])
  rintro a b hab hne
  rcases ha : a.val with k | ⟨k, t, l⟩ <;> rcases hb : b.val with k' | ⟨k', t', l'⟩ <;>
    simp only [TTree_adj, ha, hb, tAdjRaw] at hab <;>
    simp only [cutRoot, ha, hb]
  · obtain ⟨rfl, rfl⟩ := hab
    refine (decide_eq_false ?_).symm
    rintro ⟨rfl, rfl⟩
    exact hne (by rw [eq_tP_of_val ha, eq_tT_of_val hb hv])
  · obtain ⟨rfl, rfl⟩ := hab
    refine decide_eq_false ?_
    rintro ⟨rfl, rfl⟩
    refine hne ?_
    rw [eq_tT_of_val ha hv, eq_tP_of_val hb]
    exact Sym2.eq_swap
  · rcases hab with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> rfl

/-- `c = b :: m` 时,`c` 是 `d :: p` 的后缀但不是 `p` 的后缀,只能是 `c = d :: p`。 -/
lemma cons_eq_of_suffix_cons {b d : Bool} {m p : List Bool}
    (hs : (b :: m) <:+ d :: p) (hns : ¬ ((b :: m) <:+ p)) : b = d ∧ m = p := by
  rcases List.suffix_cons_iff.mp hs with heq | hs'
  · simpa only [List.cons.injEq] using heq
  · exact absurd hs' hns

/-- 子树内部边 `(b::m)—m` 是桥:割函数 `cutIn i s (b::m)` 标记「落在以 `b::m` 为根的子树里」。
沿子树边 `(d::p)—p` 割值改变当且仅当 `b::m <:+ d::p` 而 `¬ (b::m <:+ p)`,
由 `List.suffix_cons_iff` 这迫使 `b::m = d::p`,即这条边就是被删掉的那条;
`vₖ—uₖ^{(t)}` 与主路径边两端都取 `false`(`b::m` 不是 `[]` 的后缀)。 -/
lemma isBridge_in {i : Fin n} {s : Bool} {b : Bool} {m : List Bool}
    (h1 : TValid x n (TV.treeV i s (b :: m))) (h2 : TValid x n (TV.treeV i s m)) :
    (TTree x n).IsBridge s(tT x i s (b :: m) h1, tT x i s m h2) := by
  classical
  have hnot : ¬ ((b :: m) <:+ m) := by
    intro hs
    have := hs.length_le
    simp only [List.length_cons] at this
    omega
  refine isBridge_of_cut (cutIn i s (b :: m)) ?_ (by simp [cutIn, hnot])
  rintro p q hpq hne
  rcases hp : p.val with k | ⟨k, t, l⟩ <;> rcases hq : q.val with k' | ⟨k', t', l'⟩ <;>
    simp only [TTree_adj, hp, hq, tAdjRaw] at hpq <;>
    simp only [cutIn, hp, hq]
  · obtain ⟨rfl, rfl⟩ := hpq
    simp
  · obtain ⟨rfl, rfl⟩ := hpq
    simp
  · rcases hpq with ⟨rfl, rfl, d, rfl⟩ | ⟨rfl, rfl, d, rfl⟩
    · by_cases hki : k = i ∧ t = s
      · obtain ⟨rfl, rfl⟩ := hki
        simp only [decide_eq_decide, true_and, and_true]
        constructor
        · intro hs
          by_contra hns
          obtain ⟨rfl, rfl⟩ := cons_eq_of_suffix_cons hs hns
          exact hne (by rw [eq_tT_of_val hp h1, eq_tT_of_val hq h2])
        · intro hs
          exact hs.trans (List.suffix_cons d l')
      · simp only [decide_eq_decide]
        constructor
        · rintro ⟨e1, e2, -⟩; exact absurd ⟨e1, e2⟩ hki
        · rintro ⟨e1, e2, -⟩; exact absurd ⟨e1, e2⟩ hki
    · by_cases hki : k = i ∧ t = s
      · obtain ⟨rfl, rfl⟩ := hki
        simp only [decide_eq_decide, true_and, and_true]
        constructor
        · intro hs
          exact hs.trans (List.suffix_cons d l)
        · intro hs
          by_contra hns
          obtain ⟨rfl, rfl⟩ := cons_eq_of_suffix_cons hs hns
          refine hne ?_
          rw [eq_tT_of_val hp h2, eq_tT_of_val hq h1]
          exact Sym2.eq_swap
      · simp only [decide_eq_decide]
        constructor
        · rintro ⟨e1, e2, -⟩; exact absurd ⟨e1, e2⟩ hki
        · rintro ⟨e1, e2, -⟩; exact absurd ⟨e1, e2⟩ hki

/-- 主路径边的另一个朝向。 -/
lemma isBridge_seg' {i j : Fin n} (hij : (i : ℕ) + 1 = (j : ℕ)) :
    (TTree x n).IsBridge s(tP x j, tP x i) := by
  rw [Sym2.eq_swap]; exact isBridge_seg hij

/-- `uᵢ^{(s)}—vᵢ` 朝向。 -/
lemma isBridge_root' {i : Fin n} {s : Bool} (hv : TValid x n (TV.treeV i s [])) :
    (TTree x n).IsBridge s(tT x i s [] hv, tP x i) := by
  rw [Sym2.eq_swap]; exact isBridge_root hv

/-- `m—(b::m)` 朝向。 -/
lemma isBridge_in' {i : Fin n} {s : Bool} {b : Bool} {m : List Bool}
    (h1 : TValid x n (TV.treeV i s (b :: m))) (h2 : TValid x n (TV.treeV i s m)) :
    (TTree x n).IsBridge s(tT x i s m h2, tT x i s (b :: m) h1) := by
  rw [Sym2.eq_swap]; exact isBridge_in h1 h2

lemma TTree_isAcyclic : (TTree x n).IsAcyclic := by
  -- [S4-7] `isAcyclic_iff_forall_adj_isBridge`:逐边按「主路径边 / `vᵢuᵢ` / 子树内部边」
  -- 三类分派到三族割函数,两个朝向各用一次
  classical
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  rcases hu : u.val with k | ⟨k, t, l⟩ <;> rcases hv : v.val with k' | ⟨k', t', l'⟩ <;>
    simp only [TTree_adj, hu, hv, tAdjRaw] at huv
  · rw [eq_tP_of_val hu, eq_tP_of_val hv]
    rcases huv with h | h
    · exact isBridge_seg h
    · exact isBridge_seg' h
  · obtain ⟨rfl, rfl⟩ := huv
    have hval : TValid x n v.val := v.2
    rw [hv] at hval
    rw [eq_tP_of_val hu, eq_tT_of_val hv hval]
    exact isBridge_root hval
  · obtain ⟨rfl, rfl⟩ := huv
    have hval : TValid x n u.val := u.2
    rw [hu] at hval
    rw [eq_tT_of_val hu hval, eq_tP_of_val hv]
    exact isBridge_root' hval
  · have hu2 : TValid x n u.val := u.2
    have hv2 : TValid x n v.val := v.2
    rcases huv with ⟨rfl, rfl, d, rfl⟩ | ⟨rfl, rfl, d, rfl⟩
    · rw [hu] at hu2
      rw [hv] at hv2
      rw [eq_tT_of_val hu hu2, eq_tT_of_val hv hv2]
      exact isBridge_in hu2 hv2
    · rw [hu] at hu2
      rw [hv] at hv2
      rw [eq_tT_of_val hu hu2, eq_tT_of_val hv hv2]
      exact isBridge_in' hv2 hu2

/-! ## 3. 1-3 树 -/

/-- `T(x₁…xₙ)` 的顶点集非空(`n ≥ 2` 给出 `v₁`)。 -/
lemma TTree_nonempty (hp : TParams x n) : Nonempty (TVtx x n) :=
  ⟨tP x ⟨0, by have := hp.two_le; omega⟩⟩

/-- `T(x₁…xₙ)` 是树。 -/
theorem TTree_isTree (hp : TParams x n) : (TTree x n).IsTree where
  connected := haveI := TTree_nonempty hp; ⟨TTree_preconnected hp⟩
  isAcyclic := TTree_isAcyclic

/-- **论文的 "the tree `T(x₁ . . . xₙ)` is a 1-3 tree"。** -/
theorem TTree_is13Tree (hp : TParams x n) : Is13Tree (TTree x n) where
  isTree := TTree_isTree hp
  deg := by
    intro v
    rcases hv : v.val with i | ⟨i, s, l⟩
    · right
      rw [show v = tP x i from TVtx_ext (by simp [hv])]
      exact pathV_isDeg3 hp i
    · have hval : TValid x n (.treeV i s l) := hv ▸ v.2
      rw [show v = tT x i s l hval from TVtx_ext (by simp [hv])]
      rcases lt_or_eq_of_le hval.2 with hlt | heq
      · exact Or.inr (treeV_isDeg3 hval hlt)
      · exact Or.inl (treeV_isLeaf hval heq)

end Erdos815
