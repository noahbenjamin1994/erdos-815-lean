/-
# Theorem 1.3(ii) 与 Theorem 1.2 —— 组装(step 5)

T1.3(ii): `Tₙ` 无长 20 的 leaf-leaf 路径 = T2.5(20-avoiding)+ Lemma 2.2(iv) 的 only-if。
T1.2:     `Gₙ = G(Tₙ)` 是 degree 3-critical 且无长 23 的圈 = P-crit + Lemma 2.1(i) + T1.3(ii)。

论文 Proof of Theorem 1.2(全文):

> Let `(aᵢ)` be the sequence from Theorem 2.5, and let `Tₙ = T(a₁ … aₙ)`. By Theorem 1.3(ii),
> `Tₙ` contains no leaf-leaf path of length 20. Since `Tₙ` is an even 1-3-tree, we can use
> part (i) of Lemma 2.1 to conclude that `Gₙ = G(Tₙ)` contains no cycle of length 23.
> Since `Tₙ` is a 1-3 tree, `Gₙ` is degree 3-critical.

## 本文件的四块

| 块 | 内容 |
|---|---|
| §1 | `TVtx x n` 的有限性(`Fintype` 实例)—— Lean 里必须显式给,论文里是「显然」 |
| §2 | 参数核对:`xA := aSeq (·+1)` 满足 `TParams` / `IsOddEvenFin` / `xMax < 10` |
| §3 | **T1.3(ii)**:`theorem_1_3_ii` |
| §4 | **T1.2**:`theorem_1_2` 与蓝图定死的最终陈述 `erdos_815` |

## 下标平移(全文件唯一容易错的地方,写死在这里)

论文的序列是 `a₁, a₂, …`(从 **1** 起),`Tₙ = T(a₁ … aₙ)`。
`TTree x n` 取 `x` 在 `0, …, n−1` 上的值,故

```
xA i := aSeq (i + 1)      -- 我们的 x i  =  论文的 a_{i+1}
```

与 `TreeBasic.IsOddEvenFin` 的 `x i % 2 = (i+1) % 2` 正好对上(`aSeq I ≡ I (mod 2)`),
也与 `Sequence.aSeq_matches_paper` 锁死的「`aSeq 1 … aSeq 24` = 论文印的那 24 个数」对上。

## 为什么是 `m = 10` 而不是 `m = 11`

`lemma_2_2_iv_only_if` 要 `xMax x n < m` 且路径长 `2 * m`。我们要排除的路径长是 **20**,
故 `m = 10`,需要 `xMax < 10` 即 `aSeq i ≤ 9`。论文写的正是
「`20 > 2 · maxᵢ aᵢ = 18`」—— 用的是**实际最大值 9**,不是 Definition 2.3 那条较松的
`aᵢ ≤ k/2 = 10`。`Sequence.aSeq_le_nine` 是 step 5 为此补的有限检查。
-/
import Erdos815.Defs
import Erdos815.Sequence
import Erdos815.GTreeCritical
import Erdos815.GTreeCycles
import Erdos815.TreePaths
import Erdos815.Transport
import Mathlib.Data.Set.Finite.List

namespace Erdos815

open SimpleGraph

/-! ## 1. `TVtx x n` 的有限性

论文里「`T(x₁…xₙ)` 是有限树」是不言而喻的;Lean 里 `TVtx x n` 的 `treeV` 构造子带一个
`List Bool`,类型层面无界,有限性**完全来自** `TValid` 里的 `l.length + 1 ≤ x i`。

做法:把合法顶点塞进一个显然有限的类型的**像**里,再 `Set.Finite.subset`。
枚举函数 `tEnum` 刻意写成**非依赖的全函数**(值域是 raw 类型 `TV n`,不是 `TVtx x n`)
—— 否则 match 里要拖着 `TValid` 证明项,写不出来。 -/

section Finiteness

variable (x : ℕ → ℕ) (n : ℕ)

/-- 合法顶点的枚举函数:下标 + 侧 + 一个长度受 `xMax` 约束的 `Bool` 串。

不要求它是单射或满射,只要求合法顶点全落在它的**像**里。 -/
def tEnum : Fin n ⊕ (Fin n × Bool × {l : List Bool // l.length ≤ xMax x n}) → TV n
  | .inl i => .pathV i
  | .inr (i, s, l) => .treeV i s l.val

lemma tValid_subset_range :
    {v : TV n | TValid x n v} ⊆ Set.range (tEnum x n) := by
  rintro (i | ⟨i, s, l⟩) hv
  · exact ⟨.inl i, rfl⟩
  · obtain ⟨-, hl⟩ := hv
    have hxi : x (i : ℕ) ≤ xMax x n := le_xMax i.2
    exact ⟨.inr (i, s, ⟨l, by omega⟩), rfl⟩

instance TVtx_finite : Finite (TVtx x n) := by
  have : Finite {l : List Bool // l.length ≤ xMax x n} :=
    (List.finite_length_le Bool (xMax x n)).to_subtype
  have h : {v : TV n | TValid x n v}.Finite :=
    Set.Finite.subset (Set.finite_range (tEnum x n)) (tValid_subset_range x n)
  exact h.to_subtype

/-- `TVtx x n` 的 `Fintype`。

**声明成 `instance` 而不是每处现做**:`IsDegree3Critical` 把 `Fintype` 收在
instance-implicit 位置上,两个不同来源的实例会给出两个只**命题相等**、不语法相同的陈述
(step 2 踩过这个坑)。全文件统一走这一个实例,就不必到处 `Subsingleton.elim`。 -/
noncomputable instance TVtx_fintype : Fintype (TVtx x n) := Fintype.ofFinite _

/-- 主路径的 `n` 个点给出 `Fin n ↪ TVtx x n`,于是顶点数 `≥ n`。

这是 §4 里「顶点数无上界」的**唯一**来源 —— 不需要精确计数公式(那要数
完美二叉树的结点数,是纯粹的额外工作量,而我们只需要无上界)。 -/
lemma card_TVtx_ge : n ≤ Fintype.card (TVtx x n) := by
  have hinj : Function.Injective (fun i : Fin n => tP x i) := by
    intro a b hab
    have : TV.pathV a = TV.pathV b := congrArg Subtype.val hab
    simpa using this
  simpa using Fintype.card_le_of_injective _ hinj

end Finiteness

/-! ## 2. 参数核对:论文序列满足构造的全部前提 -/

/-- **论文的 `Tₙ = T(a₁ … aₙ)` 用的那个序列**,平移到 0-based:`xA i = a_{i+1}`。 -/
def xA (i : ℕ) : ℕ := aSeq ((i : ℤ) + 1)

lemma xA_pos (i : ℕ) : 1 ≤ xA i := aSeq_pos _

lemma xA_le_nine (i : ℕ) : xA i ≤ 9 := aSeq_le_nine _

/-- `xA` 满足构造的隐含前提(`n ≥ 2`、取正整数值)。 -/
lemma xA_tParams {n : ℕ} (hn : 2 ≤ n) : TParams xA n :=
  ⟨hn, fun i _ => xA_pos i⟩

/-- `xA` 是 odd-even 序列(0-based 版本)。

论文 `aᵢ ≡ i (mod 2)`(下标从 1 起)⟹ `xA i = a_{i+1} ≡ i + 1 (mod 2)`。 -/
lemma xA_isOddEven (n : ℕ) : IsOddEvenFin xA n := by
  intro i _
  have h := aSeq_isOddEven ((i : ℤ) + 1)
  -- `h : ((aSeq (i+1) : ℤ) - (i+1)) % 2 = 0`
  unfold xA
  omega

/-- `maxᵢ aᵢ = 9 < 10`。论文的「`20 > 2 · max xᵢ = 18`」就是这一条。 -/
lemma xA_xMax_lt (n : ℕ) : xMax xA n < 10 := by
  have : xMax xA n ≤ 9 := Finset.sup_le fun i _ => xA_le_nine i
  omega

/-! ## 3. Theorem 1.3(ii) -/

/-- **Theorem 1.3(ii).** *`Tₙ` contains no leaf-leaf path of length 20.*

论文的论证(Proof of Theorem 1.3):`20 > 2 · maxᵢ aᵢ = 18`,故可用 Lemma 2.2(iv);
若有长 20 的 leaf-leaf 路径,则存在 `i ≠ j` 使 `aᵢ + aⱼ + |i − j| = 20`,
与 Theorem 2.5 的「该序列 20-avoiding」矛盾。

Lean 里唯一的额外动作是**下标平移回 ℤ**:`lemma_2_2_iv_only_if` 产出的是
`Fin n` 上的 `i, j` 与 `idxDist`,`aSeq_isKAvoiding` 要的是 `ℤ` 上的 `I, J` 与
`(I − J).natAbs`。取 `I = i + 1`、`J = j + 1`,两者逐字对上。 -/
theorem theorem_1_3_ii {n : ℕ} (hn : 2 ≤ n) :
    ¬ HasLeafLeafPath (TTree xA n) 20 := by
  intro hpath
  -- `20 = 2 * 10`,且 `xMax < 10` —— 这正是论文的 `20 > 2 · max aᵢ`。
  obtain ⟨i, j, hij, heq⟩ :=
    lemma_2_2_iv_only_if (xA_tParams hn) (m := 10) (xA_xMax_lt n)
      (by simpa using hpath)
  -- 平移到 ℤ:`I = i + 1`,`J = j + 1`(论文的下标从 1 起)
  set I : ℤ := (i : ℕ) + 1 with hI
  set J : ℤ := (j : ℕ) + 1 with hJ
  have hIJ : I ≠ J := by
    intro hc
    exact hij (Fin.ext (by omega))
  have hdist : (I - J).natAbs = idxDist i j := by
    unfold idxDist
    omega
  have := (aSeq_isKAvoiding).2 I J hIJ
  rw [hdist] at this
  exact this (by simpa [xA, hI, hJ] using heq)

/-! ## 4. Theorem 1.2 与最终陈述 -/

/-- 论文的 `Gₙ = G(Tₙ)`(顶点类型是 `TVtx xA n ⊕ Bool`)。 -/
abbrev GN (n : ℕ) : SimpleGraph (TVtx xA n ⊕ Bool) := GT (TTree xA n)

/-- **Theorem 1.2(原顶点类型上的版本)。** `Gₙ` 是 degree 3-critical 且无长 23 的圈。 -/
theorem theorem_1_2 {n : ℕ} (hn : 2 ≤ n) :
    IsDegree3Critical (GN n) ∧ ¬ HasCycleOfLength (GN n) 23 := by
  have h13 : Is13Tree (TTree xA n) := TTree_is13Tree (xA_tParams hn)
  refine ⟨gt_isDegree3Critical h13, ?_⟩
  -- L2.1(i) 的接口:1-3 树 + 偶树 + 无长 20 的 leaf-leaf 路径 ⟹ 无长 23 的圈
  exact no_cycle_23_of_no_leaf_path_20 h13
    (TTree_isEvenTree (xA_tParams hn) (xA_isOddEven n)) (theorem_1_3_ii hn)

/-- 搬到 `Fin N` 上的那一族(下标从 0 起,对应论文的 `n = i + 2`)。

取 `n = i + 2` 是为了自动满足 `TParams` 的 `2 ≤ n`。 -/
noncomputable def famG (i : ℕ) : Σ N : ℕ, SimpleGraph (Fin N) := finGraph (GN (i + 2))

lemma famG_isDegree3Critical (i : ℕ) : IsDegree3Critical (famG i).2 :=
  finGraph_isDegree3Critical (theorem_1_2 (by omega)).1

lemma famG_no_cycle (i : ℕ) : ¬ HasCycleOfLength (famG i).2 23 :=
  finGraph_no_cycle (theorem_1_2 (by omega)).2

/-- 这一族的顶点数无上界:`|V(Gₙ)| = |V(Tₙ)| + 2 ≥ n + 2`。 -/
lemma famG_unbounded (B : ℕ) : ∃ i : ℕ, B < (famG i).1 := by
  refine ⟨B, ?_⟩
  show B < Fintype.card (TVtx xA (B + 2) ⊕ Bool)
  have h1 : B + 2 ≤ Fintype.card (TVtx xA (B + 2)) := card_TVtx_ge xA (B + 2)
  have h2 : Fintype.card (TVtx xA (B + 2) ⊕ Bool)
      = Fintype.card (TVtx xA (B + 2)) + 2 := by simp
  omega

/-- 从无上界的一族里挑出顶点数**严格递增**的子列(下标选择函数)。

论文说 "an infinite sequence of degree 3-critical graphs";蓝图 §0 把「无穷多」
刻画成顶点数严格递增(理由见蓝图:裸的 `ℕ → …` 允许常序列,只给出一个图)。

`Tₙ` 的顶点数其实**本来就**随 `n` 递增,但在 Lean 里证「严格递增」要精确计数公式
(得数完美二叉树的结点数 `2^{xᵢ} − 1` 并对下标求和);而我们真正需要的只是
「任意大」。于是改用**贪心选下标**:每次取一个顶点数比前一个大的成员。
这给出的结论与逐项递增完全一样,且**没有削弱最终陈述** —— 蓝图定死的
`∀ i j, i < j → (G i).1 < (G j).1` 一字未改。 -/
noncomputable def pickIdx : ℕ → ℕ
  | 0 => (famG_unbounded 0).choose
  | (m + 1) => (famG_unbounded (famG (pickIdx m)).1).choose

lemma pickIdx_lt (m : ℕ) : (famG (pickIdx m)).1 < (famG (pickIdx (m + 1))).1 :=
  (famG_unbounded (famG (pickIdx m)).1).choose_spec

/-- **最终定理(蓝图 §0 定死的陈述,一字未改)。**

*There is an infinite sequence of degree 3-critical graphs `(Gₙ)^∞_{n=1}` which do not
contain a cycle of length 23.* —— Narins–Pokrovskiy–Szabó, Theorem 1.2。 -/
theorem erdos_815 :
    ∃ G : ℕ → (Σ n : ℕ, SimpleGraph (Fin n)),
      (∀ i, IsDegree3Critical (G i).2) ∧
      (∀ i j, i < j → (G i).1 < (G j).1) ∧
      (∀ i, ¬ HasCycleOfLength (G i).2 23) := by
  refine ⟨fun i => famG (pickIdx i), fun i => famG_isDegree3Critical _, ?_,
    fun i => famG_no_cycle _⟩
  have hmono : StrictMono (fun i => (famG (pickIdx i)).1) :=
    strictMono_nat_of_lt_succ pickIdx_lt
  exact fun i j hij => hmono hij

end Erdos815
