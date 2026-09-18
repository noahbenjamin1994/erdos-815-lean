/-
# `T(x₁ … xₙ)` 的基础结构(step 4 辅助文件)

`Defs.lean` 只给出了 `T(x₁…xₙ)` 的顶点类型 `TVtx` 与邻接 `tAdjRaw`。本文件补齐
后面两个文件(`TreeStruct.lean` 证 1-3 树,`TreePaths.lean` 证 Lemma 2.2)共用的
**坐标系统**:

| 函数 | 含义 | 关键性质 |
|---|---|---|
| `tIdx v` | 顶点所属的「块」下标 `i`(路径点 `vᵢ` 与挂在它上面的子树结点同属块 `i`) | 只在主路径的边上变化,且变化量恰为 1 |
| `tHeight v` | 顶点在所属子树里的深度 `+1`(路径点记 `0`) | 只在子树内部的边与 `vᵢuᵢ` 上变化,变化量恰为 1 |
| `tRank v` | `tIdx v + tHeight v`,即到 `v₁` 的距离 | **每条边上恰好变化 1** —— 整个图是分级的 |

`tRank` 逐边变化 1 立刻给出一个 `Bool` 2-染色 `tColor`,而 odd-even 条件恰好使
**所有叶子同色**,于是 Lemma 2.2(i)(偶树)不需要任何路径分类就能得到。
这是本步最大的一处简化:论文用「路径与主路径的交」三分类来推出偶性,
我们用染色直接给出,逻辑上更短且完全忠实(结论一致)。

另外本文件给出三族**割函数**(cut functions),`TreeStruct.lean` 用它们证无圈:
对每条边给一个在「删掉该边后的图」上沿边恒定、而在该边两端取值不同的 `Bool` 函数,
即证明了每条边都是桥,由 `isAcyclic_iff_forall_adj_isBridge` 得无圈。
-/
import Erdos815.Defs
import Erdos815.GTreeCritical
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

namespace Erdos815

open SimpleGraph

variable {n : ℕ} {x : ℕ → ℕ}

/-! ## 0. 参数约定

论文的构造默认 `n ≥ 2` 且每个 `xᵢ ≥ 1`(`xᵢ` 是「正整数序列」,深度 `xᵢ − 1 ≥ 0`)。
这两条都是必需的,不是技术性附加:

* `n = 1` 时 `v₁` 同时是首尾,只挂两棵子树而没有主路径邻居,度为 2 —— 不是 1-3 树;
* `xᵢ = 0` 时第 `i` 棵子树为空(`TValid` 要求 `|l| + 1 ≤ xᵢ`,无解),`vᵢ` 的度掉到 2。

论文写 "a path on `n` vertices" 并画出 Figure 3,隐含 `n ≥ 2`;
写 "a sequence of positive integers" 即 `xᵢ ≥ 1`。 -/

/-- `T(x₁…xₙ)` 构造的参数条件(论文隐含)。 -/
structure TParams (x : ℕ → ℕ) (n : ℕ) : Prop where
  /-- 主路径至少两个点。 -/
  two_le : 2 ≤ n
  /-- 序列取正整数值。 -/
  pos : ∀ i, i < n → 1 ≤ x i

/-- **odd-even 序列**(有限、0-based 版本)。

论文写 `xᵢ ≡ i (mod 2)`,下标 `i` 从 **1** 起。`Defs.lean` 里 `TTree x n` 取 `x` 在
`0, …, n−1` 上的值,即我们的 `x i` 是论文的 `x_{i+1}`,故条件写成 `x i ≡ i + 1 (mod 2)`。
step 5 里 `x i := aSeq (i + 1)`,而 `aSeq I ≡ I (mod 2)`,正好对上。 -/
def IsOddEvenFin (x : ℕ → ℕ) (n : ℕ) : Prop := ∀ i, i < n → x i % 2 = (i + 1) % 2

/-! ## 1. 顶点的构造子简写 -/

/-- 主路径点 `v_{i+1}`(0-based 下标 `i`)。 -/
def tP (x : ℕ → ℕ) {n : ℕ} (i : Fin n) : TVtx x n := ⟨.pathV i, trivial⟩

/-- 挂在 `vᵢ` 上、第 `s` 侧子树里根到该点路径为 `l` 的结点。 -/
def tT (x : ℕ → ℕ) {n : ℕ} (i : Fin n) (s : Bool) (l : List Bool)
    (h : TValid x n (.treeV i s l)) : TVtx x n := ⟨.treeV i s l, h⟩

@[simp] lemma tP_val (i : Fin n) : (tP x i).val = TV.pathV i := rfl

@[simp] lemma tT_val (i : Fin n) (s : Bool) (l : List Bool)
    (h : TValid x n (.treeV i s l)) : (tT x i s l h).val = TV.treeV i s l := rfl

lemma TVtx_ext {u v : TVtx x n} (h : u.val = v.val) : u = v := Subtype.ext h

/-! ## 2. 三个坐标函数

外加主路径上的下标距离 `idxDist`。 -/

/-- 主路径上两个块的下标距离 `|i − j|`。

写成 `Int.natAbs` 是为了和 `Defs.lean` 里 `IsKAvoiding` 的
`a i + a j + (i - j).natAbs ≠ k` **逐字同形** —— step 5 组装时只需做一次
`x i = aSeq (i+1)` 的下标平移,不必再转换距离的写法。 -/
def idxDist {n : ℕ} (i j : Fin n) : ℕ := (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)).natAbs

lemma idxDist_comm {n : ℕ} (i j : Fin n) : idxDist i j = idxDist j i := by
  unfold idxDist; omega


/-- 顶点所属的块下标:`vᵢ` 与挂在 `vᵢ` 上的子树结点都记为 `i`。 -/
def tIdx : TV n → Fin n
  | .pathV i => i
  | .treeV i _ _ => i

/-- 顶点在所属子树里的深度 `+1`;主路径点记 `0`。 -/
def tHeight : TV n → ℕ
  | .pathV _ => 0
  | .treeV _ _ l => l.length + 1

/-- 到 `v₁` 的距离(分级函数)。 -/
def tRank (v : TV n) : ℕ := (tIdx v : ℕ) + tHeight v

@[simp] lemma tIdx_pathV (i : Fin n) : tIdx (TV.pathV i) = i := rfl
@[simp] lemma tIdx_treeV (i : Fin n) (s : Bool) (l : List Bool) :
    tIdx (TV.treeV i s l) = i := rfl
@[simp] lemma tHeight_pathV (i : Fin n) : tHeight (TV.pathV i) = 0 := rfl
@[simp] lemma tHeight_treeV (i : Fin n) (s : Bool) (l : List Bool) :
    tHeight (TV.treeV i s l) = l.length + 1 := rfl

/-- **分级性**:每条边恰好把 `tRank` 改变 1。

这是整个构造的骨架:主路径的边改变 `tIdx`,子树里的边(含 `vᵢuᵢ`)改变 `tHeight`,
两者不会同时变。 -/
lemma tRank_adj {u v : TV n} (h : tAdjRaw n u v) :
    tRank u = tRank v + 1 ∨ tRank v = tRank u + 1 := by
  rcases u with i | ⟨i, s, l⟩ <;> rcases v with j | ⟨j, t, m⟩ <;>
    simp only [tAdjRaw] at h <;> simp only [tRank, tIdx, tHeight]
  · omega
  · obtain ⟨rfl, rfl⟩ := h; simp
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rcases h with ⟨rfl, rfl, b, rfl⟩ | ⟨rfl, rfl, b, rfl⟩ <;> simp <;> omega

/-! ## 3. 2-染色与 Lemma 2.2(i) 的引擎 -/

/-- 由分级函数导出的 `Bool` 2-染色。 -/
def tColor (v : TVtx x n) : Bool := decide (tRank v.val % 2 = 1)

lemma tColor_ne_of_adj {u v : TVtx x n} (h : (TTree x n).Adj u v) :
    tColor u ≠ tColor v := by
  have := tRank_adj (u := u.val) (v := v.val) h
  simp only [tColor, ne_eq, decide_eq_decide]
  omega

/-- `T(x₁…xₙ)` 的 2-染色(它是树,当然二部;这里给出**显式**的那个)。 -/
def tColoring (x : ℕ → ℕ) (n : ℕ) : (TTree x n).Coloring Bool :=
  SimpleGraph.Coloring.mk tColor (fun h => tColor_ne_of_adj h)

/-! ## 4. 叶子 -/

/-- `T(x₁…xₙ)` 的叶子(raw 层刻画):某棵子树里深度最大的那一层结点。

主路径点永远不是叶子(`TParams` 下度恒为 3)。 -/
def IsTLeafRaw (x : ℕ → ℕ) (n : ℕ) : TV n → Prop
  | .pathV _ => False
  | .treeV i _ l => l.length + 1 = x (i : ℕ)

/-! ### 邻居清单(三条度数引理共用)

`tAdjRaw` 是对两个顶点的构造子做的四路模式匹配,直接在度数证明里反复展开很啰嗦。
这里先按「起点是主路径点 / 起点是子树结点」各解包一次,得到两份**显式的邻居清单**,
后面三条引理就只剩下标算术、合法性检查与去重。 -/

/-- 顶点是子类型:`.val` 不同则顶点不同(`TVtx_ext` 的逆用)。 -/
private lemma TVtx_val_ne {u v : TVtx x n} (h : u.val ≠ v.val) : u ≠ v :=
  fun he => h (congrArg (fun w : TVtx x n => w.val) he)

/-- 主路径点之间的不等性:块下标不同即不同(用 `tIdx` 区分)。 -/
private lemma tP_ne_tP {i j : Fin n} (hij : (i : ℕ) ≠ (j : ℕ)) : tP x i ≠ tP x j :=
  TVtx_val_ne (fun hh => hij (congrArg (fun z : TV n => ((tIdx z : ℕ))) hh))

/-- 主路径点永远不等于子树结点(用 `tHeight` 区分:路径点是 0,子树结点 ≥ 1)。 -/
private lemma tP_ne_tT {i j : Fin n} {s : Bool} {l : List Bool}
    (h : TValid x n (.treeV j s l)) : tP x i ≠ tT x j s l h := by
  refine TVtx_val_ne (fun hh => ?_)
  have h0 : (0 : ℕ) = l.length + 1 := congrArg tHeight hh
  omega

/-- 两个子树结点相等蕴含三个分量都相等。 -/
private lemma tT_ne_tT {i j : Fin n} {s t : Bool} {l m : List Bool}
    (h₁ : TValid x n (.treeV i s l)) (h₂ : TValid x n (.treeV j t m))
    (hne : ¬ (i = j ∧ s = t ∧ l = m)) : tT x i s l h₁ ≠ tT x j t m h₂ := by
  refine TVtx_val_ne (fun hh => hne ?_)
  have hv : TV.treeV i s l = TV.treeV j t m := hh
  injection hv with e1 e2 e3
  exact ⟨e1, e2, e3⟩

/-- 深度不同的两个子树结点必不相同(区分父亲与儿子)。 -/
private lemma tT_ne_of_len {i j : Fin n} {s t : Bool} {l m : List Bool}
    (h₁ : TValid x n (.treeV i s l)) (h₂ : TValid x n (.treeV j t m))
    (hlen : l.length ≠ m.length) : tT x i s l h₁ ≠ tT x j t m h₂ :=
  tT_ne_tT h₁ h₂ (fun hh => hlen (congrArg List.length hh.2.2))

/-- **`vᵢ` 的邻居清单**:主路径上下标相差 1 的点,或挂在 `vᵢ` 上某棵子树的根 `treeV i t []`。 -/
private lemma tP_adj_iff (i : Fin n) (w : TVtx x n) :
    (TTree x n).Adj (tP x i) w ↔
      (∃ j : Fin n, w.val = TV.pathV j ∧ ((i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ))) ∨
      (∃ t : Bool, w.val = TV.treeV i t []) := by
  constructor
  · intro hadj
    have hraw : tAdjRaw n (TV.pathV i) w.val := hadj
    rcases hwv : w.val with j | ⟨j, t, m⟩
    · rw [hwv] at hraw
      exact Or.inl ⟨j, rfl, hraw⟩
    · rw [hwv] at hraw
      obtain ⟨rfl, rfl⟩ := hraw
      exact Or.inr ⟨t, rfl⟩
  · intro hw
    show tAdjRaw n (TV.pathV i) w.val
    rcases hw with ⟨j, hj, hcase⟩ | ⟨t, ht⟩
    · rw [hj]; exact hcase
    · rw [ht]; exact ⟨rfl, rfl⟩

/-- **子树结点 `treeV i s l` 的邻居清单**:`l = []` 时的 `vᵢ`、父亲(`l = b :: m`)、
以及两个儿子(`m = b :: l`)。注意这里还没有用到合法性,儿子是否真的存在由 `TValid` 决定。 -/
private lemma tT_adj_iff {i : Fin n} {s : Bool} {l : List Bool}
    (h : TValid x n (.treeV i s l)) (w : TVtx x n) :
    (TTree x n).Adj (tT x i s l h) w ↔
      (w.val = TV.pathV i ∧ l = []) ∨
      (∃ m : List Bool, w.val = TV.treeV i s m ∧ ((∃ b, l = b :: m) ∨ (∃ b, m = b :: l))) := by
  constructor
  · intro hadj
    have hraw : tAdjRaw n (TV.treeV i s l) w.val := hadj
    rcases hwv : w.val with j | ⟨j, t, m⟩
    · rw [hwv] at hraw
      obtain ⟨rfl, rfl⟩ := hraw
      exact Or.inl ⟨rfl, rfl⟩
    · rw [hwv] at hraw
      rcases hraw with ⟨rfl, rfl, b, hb⟩ | ⟨rfl, rfl, b, hb⟩
      · exact Or.inr ⟨m, rfl, Or.inl ⟨b, hb⟩⟩
      · exact Or.inr ⟨m, rfl, Or.inr ⟨b, hb⟩⟩
  · intro hw
    show tAdjRaw n (TV.treeV i s l) w.val
    rcases hw with ⟨hj, hl⟩ | ⟨m, hm, hcase⟩
    · rw [hj]; exact ⟨rfl, hl⟩
    · rw [hm]
      rcases hcase with ⟨b, hb⟩ | ⟨b, hb⟩
      · exact Or.inl ⟨rfl, rfl, b, hb⟩
      · exact Or.inr ⟨rfl, rfl, b, hb⟩

/-- 主路径点 `vᵢ` 的度恒为 3。

三个邻居:
* `0 < i` 时是 `v_{i−1}`,`i = 0` 时是第二棵子树的根 `u₁^{(2)}`(`twoSided` 保证合法);
* `i + 1 < n` 时是 `v_{i+1}`,`i = n − 1` 时同样是 `u_i^{(2)}`;
* 永远有第一棵子树的根 `uᵢ`(`= tT x i false []`,`xᵢ ≥ 1` 保证合法)。

`n ≥ 2` 保证前两条不会同时退化。 -/
lemma pathV_isDeg3 (hp : TParams x n) (i : Fin n) : IsDeg3 (TTree x n) (tP x i) := by
  -- 证明框架:按 `i` 是否落在主路径两端分三种情形(`i = 0` / 内部 / `i = n−1`),
  -- 每种情形显式给出三个邻居,再用 `tP_adj_iff` 把「是邻居」化归为下标算术。
  -- `hx : 1 ≤ xᵢ` 保证子树根合法;`hn2 : 2 ≤ n` 排除 `i` 同时是首和尾的退化情形。
  have hi : (i : ℕ) < n := i.2
  have hx : 1 ≤ x (i : ℕ) := hp.pos _ hi
  have hn2 : 2 ≤ n := hp.two_le
  -- 第一棵子树的根永远合法
  have hc : TValid x n (.treeV i false []) := ⟨Or.inl rfl, by simp only [List.length_nil]; omega⟩
  by_cases h0 : (i : ℕ) = 0
  · -- 情形一:`i = 0`,左邻居退化为第二棵子树的根 `u₁^{(2)}`,右邻居是 `v₂`
    have h2 : TValid x n (.treeV i true []) :=
      ⟨Or.inr (Or.inl h0), by simp only [List.length_nil]; omega⟩
    have hn1 : (i : ℕ) + 1 < n := by omega
    refine ⟨tT x i true [] h2, tP x ⟨(i : ℕ) + 1, hn1⟩, tT x i false [] hc,
      Ne.symm (tP_ne_tT h2), tT_ne_tT h2 hc (by simp), tP_ne_tT hc, ?_⟩
    intro w
    rw [tP_adj_iff]
    constructor
    · rintro (⟨j, hj, hcase⟩ | ⟨t, ht⟩)
      · have hjeq : j = (⟨(i : ℕ) + 1, hn1⟩ : Fin n) := by
          apply Fin.ext; show (j : ℕ) = (i : ℕ) + 1; omega
        exact Or.inr (Or.inl (TVtx_ext (by simp only [tP_val, hj, hjeq])))
      · cases t
        · exact Or.inr (Or.inr (TVtx_ext ht))
        · exact Or.inl (TVtx_ext ht)
    · rintro (rfl | rfl | rfl)
      · exact Or.inr ⟨true, rfl⟩
      · exact Or.inl ⟨⟨(i : ℕ) + 1, hn1⟩, rfl, Or.inl rfl⟩
      · exact Or.inr ⟨false, rfl⟩
  · have hipos : 0 < (i : ℕ) := by omega
    have hpre : (i : ℕ) - 1 < n := by omega
    by_cases h1 : (i : ℕ) + 1 < n
    · -- 情形二:`0 < i < n − 1`,两个主路径邻居 `v_{i−1}`、`v_{i+1}`,外加唯一的子树根
      refine ⟨tP x ⟨(i : ℕ) - 1, hpre⟩, tP x ⟨(i : ℕ) + 1, h1⟩, tT x i false [] hc,
        tP_ne_tP (by show (i : ℕ) - 1 ≠ (i : ℕ) + 1; omega), tP_ne_tT hc, tP_ne_tT hc, ?_⟩
      intro w
      rw [tP_adj_iff]
      constructor
      · rintro (⟨j, hj, hcase⟩ | ⟨t, ht⟩)
        · rcases hcase with hcs | hcs
          · have hjeq : j = (⟨(i : ℕ) + 1, h1⟩ : Fin n) := by
              apply Fin.ext; show (j : ℕ) = (i : ℕ) + 1; omega
            exact Or.inr (Or.inl (TVtx_ext (by simp only [tP_val, hj, hjeq])))
          · have hjeq : j = (⟨(i : ℕ) - 1, hpre⟩ : Fin n) := by
              apply Fin.ext; show (j : ℕ) = (i : ℕ) - 1; omega
            exact Or.inl (TVtx_ext (by simp only [tP_val, hj, hjeq]))
        · -- `s = true` 需要 `twoSided`,但此时 `0 < i < n − 1`,矛盾
          have hval : TValid x n (TV.treeV i t []) := by rw [← ht]; exact w.2
          cases t
          · exact Or.inr (Or.inr (TVtx_ext ht))
          · rcases hval.1 with hcon | hcon
            · exact absurd hcon (by simp)
            · exact absurd hcon (by simp only [twoSided]; omega)
      · rintro (rfl | rfl | rfl)
        · exact Or.inl ⟨⟨(i : ℕ) - 1, hpre⟩, rfl, Or.inr (by show (i : ℕ) - 1 + 1 = (i : ℕ); omega)⟩
        · exact Or.inl ⟨⟨(i : ℕ) + 1, h1⟩, rfl, Or.inl rfl⟩
        · exact Or.inr ⟨false, rfl⟩
    · -- 情形三:`i = n − 1`,右邻居退化为第二棵子树的根 `uₙ^{(2)}`
      have hlast : (i : ℕ) = n - 1 := by omega
      have h2 : TValid x n (.treeV i true []) :=
        ⟨Or.inr (Or.inr hlast), by simp only [List.length_nil]; omega⟩
      refine ⟨tP x ⟨(i : ℕ) - 1, hpre⟩, tT x i true [] h2, tT x i false [] hc,
        tP_ne_tT h2, tP_ne_tT hc, tT_ne_tT h2 hc (by simp), ?_⟩
      intro w
      rw [tP_adj_iff]
      constructor
      · rintro (⟨j, hj, hcase⟩ | ⟨t, ht⟩)
        · have hj1 : (j : ℕ) < n := j.2
          have hjeq : j = (⟨(i : ℕ) - 1, hpre⟩ : Fin n) := by
            apply Fin.ext; show (j : ℕ) = (i : ℕ) - 1; omega
          exact Or.inl (TVtx_ext (by simp only [tP_val, hj, hjeq]))
        · cases t
          · exact Or.inr (Or.inr (TVtx_ext ht))
          · exact Or.inr (Or.inl (TVtx_ext ht))
      · rintro (rfl | rfl | rfl)
        · exact Or.inl ⟨⟨(i : ℕ) - 1, hpre⟩, rfl, Or.inr (by show (i : ℕ) - 1 + 1 = (i : ℕ); omega)⟩
        · exact Or.inr ⟨true, rfl⟩
        · exact Or.inr ⟨false, rfl⟩

/-- 非最深层的子树结点度为 3:父亲 + 两个儿子。 -/
lemma treeV_isDeg3 {i : Fin n} {s : Bool} {l : List Bool}
    (h : TValid x n (.treeV i s l)) (hd : l.length + 1 < x (i : ℕ)) :
    IsDeg3 (TTree x n) (tT x i s l h) := by
  -- 证明框架:对 `l` 分 `[]` / `d :: m` 两种情形写出父亲(分别是 `vᵢ` 与 `treeV i s m`),
  -- 两个儿子一律是 `false :: l`、`true :: l`。`hd` 给出儿子的合法性
  -- (`|l| + 2 ≤ xᵢ`),父亲的合法性由 `|l.tail| + 1 ≤ |l| + 1 ≤ xᵢ` 得到。
  cases l with
  | nil =>
    have hch : ∀ b : Bool, TValid x n (.treeV i s [b]) :=
      fun b => ⟨h.1, by simp only [List.length_cons, List.length_nil] at hd ⊢; omega⟩
    refine ⟨tP x i, tT x i s [false] (hch false), tT x i s [true] (hch true),
      tP_ne_tT (hch false), tP_ne_tT (hch true),
      tT_ne_tT (hch false) (hch true) (by simp), ?_⟩
    intro w
    rw [tT_adj_iff]
    constructor
    · rintro (⟨hj, -⟩ | ⟨m', hm, hcase⟩)
      · exact Or.inl (TVtx_ext hj)
      · rcases hcase with ⟨b, hb⟩ | ⟨b, hb⟩
        · exact absurd hb (by simp)
        · subst hb
          cases b
          · exact Or.inr (Or.inl (TVtx_ext hm))
          · exact Or.inr (Or.inr (TVtx_ext hm))
    · rintro (rfl | rfl | rfl)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨[false], rfl, Or.inr ⟨false, rfl⟩⟩
      · exact Or.inr ⟨[true], rfl, Or.inr ⟨true, rfl⟩⟩
  | cons d m =>
    have hpar : TValid x n (.treeV i s m) :=
      ⟨h.1, by simp only [List.length_cons] at hd ⊢; omega⟩
    have hch : ∀ b : Bool, TValid x n (.treeV i s (b :: d :: m)) :=
      fun b => ⟨h.1, by simp only [List.length_cons] at hd ⊢; omega⟩
    refine ⟨tT x i s m hpar, tT x i s (false :: d :: m) (hch false),
      tT x i s (true :: d :: m) (hch true),
      tT_ne_of_len hpar (hch false) (by simp only [List.length_cons]; omega),
      tT_ne_of_len hpar (hch true) (by simp only [List.length_cons]; omega),
      tT_ne_tT (hch false) (hch true) (by simp), ?_⟩
    intro w
    rw [tT_adj_iff]
    constructor
    · rintro (⟨-, hnil⟩ | ⟨m', hm, hcase⟩)
      · exact absurd hnil (by simp)
      · rcases hcase with ⟨b, hb⟩ | ⟨b, hb⟩
        · -- `d :: m = b :: m'` ⇒ `m' = m`,即父亲
          have hmm : m' = m := by
            simp only [List.cons.injEq] at hb; exact hb.2.symm
          subst hmm
          exact Or.inl (TVtx_ext hm)
        · subst hb
          cases b
          · exact Or.inr (Or.inl (TVtx_ext hm))
          · exact Or.inr (Or.inr (TVtx_ext hm))
    · rintro (rfl | rfl | rfl)
      · exact Or.inr ⟨m, rfl, Or.inl ⟨d, rfl⟩⟩
      · exact Or.inr ⟨false :: d :: m, rfl, Or.inr ⟨false, rfl⟩⟩
      · exact Or.inr ⟨true :: d :: m, rfl, Or.inr ⟨true, rfl⟩⟩

/-- 最深层的子树结点是叶子:只有父亲(`l = []` 时父亲是 `vᵢ`)。 -/
lemma treeV_isLeaf {i : Fin n} {s : Bool} {l : List Bool}
    (h : TValid x n (.treeV i s l)) (hd : l.length + 1 = x (i : ℕ)) :
    IsLeaf (TTree x n) (tT x i s l h) := by
  -- 证明框架:仍按 `l` 分两种情形给出父亲作为唯一邻居。
  -- 儿子 `b :: l` 的合法性要求 `|l| + 2 ≤ xᵢ = |l| + 1`,不可能 ——
  -- 于是 `tT_adj_iff` 的「儿子」分支被顶点自带的 `w.2` 直接否掉。
  cases l with
  | nil =>
    refine ⟨tP x i, (tT_adj_iff h (tP x i)).mpr (Or.inl ⟨rfl, rfl⟩), ?_⟩
    intro y hy
    rw [tT_adj_iff] at hy
    rcases hy with ⟨hj, -⟩ | ⟨m', hm, hcase⟩
    · exact TVtx_ext hj
    · rcases hcase with ⟨b, hb⟩ | ⟨b, hb⟩
      · exact absurd hb (by simp)
      · exfalso
        subst hb
        have hval : TValid x n (TV.treeV i s (b :: [])) := by rw [← hm]; exact y.2
        have h2 := hval.2
        simp only [List.length_cons, List.length_nil] at h2 hd
        omega
  | cons d m =>
    have hpar : TValid x n (.treeV i s m) :=
      ⟨h.1, by simp only [List.length_cons] at hd ⊢; omega⟩
    refine ⟨tT x i s m hpar,
      (tT_adj_iff h (tT x i s m hpar)).mpr (Or.inr ⟨m, rfl, Or.inl ⟨d, rfl⟩⟩), ?_⟩
    intro y hy
    rw [tT_adj_iff] at hy
    rcases hy with ⟨-, hnil⟩ | ⟨m', hm, hcase⟩
    · exact absurd hnil (by simp)
    · rcases hcase with ⟨b, hb⟩ | ⟨b, hb⟩
      · have hmm : m' = m := by
          simp only [List.cons.injEq] at hb; exact hb.2.symm
        subst hmm
        exact TVtx_ext hm
      · exfalso
        subst hb
        have hval : TValid x n (TV.treeV i s (b :: d :: m)) := by rw [← hm]; exact y.2
        have h2 := hval.2
        simp only [List.length_cons] at h2 hd
        omega

/-- **叶子刻画**:`T(x₁…xₙ)` 的叶子恰是各子树最深一层的结点。 -/
theorem isLeaf_iff (hp : TParams x n) (v : TVtx x n) :
    IsLeaf (TTree x n) v ↔ IsTLeafRaw x n v.val := by
  constructor
  · intro hl
    rcases hv : v.val with i | ⟨i, s, l⟩
    · exact absurd hl ((pathV_isDeg3 hp i).not_isLeaf ∘
        (fun h => by rw [show v = tP x i from TVtx_ext (by simp [hv])] at h; exact h))
    · simp only [IsTLeafRaw]
      by_contra hne
      have hval : TValid x n (.treeV i s l) := hv ▸ v.2
      have hlt : l.length + 1 < x (i : ℕ) := lt_of_le_of_ne hval.2 hne
      refine (treeV_isDeg3 hval hlt).not_isLeaf ?_
      rw [show tT x i s l hval = v from TVtx_ext (by simp [hv])]
      exact hl
  · intro h
    rcases hv : v.val with i | ⟨i, s, l⟩
    · rw [hv] at h; exact absurd h (by simp [IsTLeafRaw])
    · have hval : TValid x n (.treeV i s l) := hv ▸ v.2
      rw [hv] at h
      rw [show v = tT x i s l hval from TVtx_ext (by simp [hv])]
      exact treeV_isLeaf hval h

/-- 叶子的 `tRank` 是 `i + xᵢ`。 -/
lemma tRank_of_leaf {v : TVtx x n} (h : IsTLeafRaw x n v.val) :
    tRank v.val = (tIdx v.val : ℕ) + x (tIdx v.val : ℕ) := by
  rcases hv : v.val with i | ⟨i, s, l⟩
  · rw [hv] at h; exact absurd h (by simp [IsTLeafRaw])
  · rw [hv] at h; simp only [IsTLeafRaw] at h
    simp [tRank, hv, h]

/-- **odd-even 下所有叶子同色。**

叶子的 rank 是 `i + xᵢ`,而 `xᵢ ≡ i + 1 (mod 2)`,故 `i + xᵢ ≡ 2i + 1 ≡ 1 (mod 2)`
—— 与 `i` 无关,所有叶子都染成 `true`。 -/
lemma leaf_tColor (hoe : IsOddEvenFin x n) {v : TVtx x n} (h : IsTLeafRaw x n v.val) :
    tColor v = true := by
  have hlt : ((tIdx v.val : ℕ)) < n := (tIdx v.val).2
  have := hoe _ hlt
  simp only [tColor, decide_eq_true_eq, tRank_of_leaf h]
  omega

/-! ## 5. 割函数(`TreeStruct.lean` 证无圈用)

对每一类边给出一个 `Bool` 函数,它在**除该边以外**的所有边上取值相同,而在该边两端不同。 -/

/-- 主路径边 `vᵢvᵢ₊₁` 的割:按块下标是否 `≤ i` 分边。 -/
def cutSeg (i : ℕ) (w : TV n) : Bool := decide ((tIdx w : ℕ) ≤ i)

/-- 边 `vᵢuᵢ^{(s)}` 的割:是否落在第 `(i, s)` 棵子树里。 -/
def cutRoot (i : Fin n) (s : Bool) : TV n → Bool
  | .pathV _ => false
  | .treeV j t _ => decide (j = i ∧ t = s)

/-- 子树内部边 `(b :: m) — m` 的割:是否落在以 `b :: m` 为根的那棵子树里。 -/
def cutIn (i : Fin n) (s : Bool) (c : List Bool) : TV n → Bool
  | .pathV _ => false
  | .treeV j t l => decide (j = i ∧ t = s ∧ c <:+ l)

/-- 沿着一条 walk,一个「在所有边上取值相同」的函数保持常值。 -/
lemma cut_const {W : Type*} {H : SimpleGraph W} (χ : W → Bool)
    (hχ : ∀ a b, H.Adj a b → χ a = χ b) : ∀ {u v : W} (p : H.Walk u v), χ u = χ v := by
  intro u v p
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hχ _ _ h).trans ih

/-- 由割函数得到不可达。 -/
lemma not_reachable_of_cut {W : Type*} {H : SimpleGraph W} (χ : W → Bool)
    (hχ : ∀ a b, H.Adj a b → χ a = χ b) {u v : W} (huv : χ u ≠ χ v) :
    ¬ H.Reachable u v := by
  rintro ⟨p⟩
  exact huv (cut_const χ hχ p)

end Erdos815
