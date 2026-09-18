/-
# Theorem 2.5 —— 存在 20-avoiding 的 odd-even 序列

Narins–Pokrovskiy–Szabó, *Graphs without proper subgraphs of minimum degree 3 and
short cycles*, Combinatorica 37 (2017) 495–519, arXiv:1408.5289, §2.1。

论文的证明是「看 Figure 4」:把序列画成图,目测没有点落在别的点的 fault line 上。
那套 fault line / Proposition 2.4 的几何语言是**为人眼检查服务的等价重述**,不是逻辑上
必需的一步。我们绕过 Prop 2.4,直接按 Definition 2.3 的字面定义做有限枚举 —— 这不损失
任何东西(Prop 2.4 本就是 Def 2.3 的等价改写),而且给出的是机器可验的证明而不是一张图。

核心是一条**有限化归约**:周期性 + `aᵢ ≥ 1` 把 `∀ i ≠ j ∈ ℤ` 的条件压成
`∀ r < 24, ∀ 1 ≤ d ≤ 18` 的 24×18 次检查,由 `decide` 在内核里判定。

⚠ 全文只用内核 `decide`。**编译期求值版的那个 tactic(名字见验收脚本)一律禁用** ——
它会引入额外的求值公理,违反本任务「只允许 propext / Classical.choice / Quot.sound」的口径。
-/
import Erdos815.Defs

namespace Erdos815

open List

/-! ## 1. 序列本身 -/

/-- 论文 §2.1 Theorem 2.5 的周期 24 序列

`. . . , 1, 2, 1, 4, 3, 2, 7, 6, 5, 6, 7, 2, 3, 4, 1, 2, 1, 8, 9, 6, 5, 6, 9, 8, . . .`

论文把这串写成 `a₁ … a₂₄`。这里按 `a₀ … a₂₃` 存储,即把末项 `8` 旋到开头,
于是 `aSeq 1 = 1, aSeq 2 = 2, …, aSeq 24 = 8` 与论文的下标完全一致
(见 `aSeq_matches_paper`)。 -/
def seqList : List ℕ :=
  [8, 1, 2, 1, 4, 3, 2, 7, 6, 5, 6, 7, 2, 3, 4, 1, 2, 1, 8, 9, 6, 5, 6, 9]

/-- 按下标取值(越界给 `0`,实际只在 `r < 24` 上使用)。 -/
def seqAt (r : ℕ) : ℕ := seqList.getD r 0

/-- 论文的两侧无穷序列 `(aᵢ)_{i∈ℤ}`:以 24 为周期延拓 `seqList`。 -/
def aSeq (i : ℤ) : ℕ := seqAt (i % 24).toNat

lemma aSeq_def (i : ℤ) : aSeq i = seqAt (i % 24).toNat := rfl

/-- 下标对齐自检:`aSeq 1 … aSeq 24` 逐项等于论文正文里印的那 24 个数。 -/
theorem aSeq_matches_paper :
    (List.range 24).map (fun t => aSeq (t + 1)) =
      [1, 2, 1, 4, 3, 2, 7, 6, 5, 6, 7, 2, 3, 4, 1, 2, 1, 8, 9, 6, 5, 6, 9, 8] := by
  decide

/-! ## 2. 有限检查(全部由 `decide` 在内核里判定)

写成 `List.all … = true` 而不是 `∀ r < 24, …`:`List.all` 在内核里是直接求值,
比展开 `Nat.decidableBallLT` 的判定实例高效得多。 -/

/-- 每项都 `≥ 1`(Definition 2.3 要求正整数序列)。 -/
def allPosOK : Bool := (range 24).all fun r => decide (1 ≤ seqAt r)

/-- 每项都满足 `aᵢ ≤ k/2`,这里写成无除法的 `2 * aᵢ ≤ 20`。 -/
def allBoundOK : Bool := (range 24).all fun r => decide (2 * seqAt r ≤ 20)

/-- 序列的**实际**最大值是 `9`(论文写 `aᵢ ≤ 10 = 20/2` 是为了对齐 Definition 2.3
的 `≤ k/2`,并非声称取到 10)。step 5 的 `lemma_2_2_iv_only_if` 需要
`xMax < 10` 这个**严格**不等式,`2 * aᵢ ≤ 20`(即 `≤ 10`)不够,故单独查一次。 -/
def allBound9OK : Bool := (range 24).all fun r => decide (seqAt r ≤ 9)

/-- odd-even:`aᵢ ≡ i (mod 2)`。周期 24 是偶数,故只需在一个周期上查。 -/
def allParityOK : Bool := (range 24).all fun r => decide (seqAt r % 2 = r % 2)

/-- 无冲突的有限检查:`r < 24`、`1 ≤ d ≤ 18` 时 `a r + a (r+d) + d ≠ 20`。

`d` 只查到 18:`aᵢ ≥ 1` 使得 `d ≥ 19` 时左边 `≥ 1 + 1 + 19 = 21 > 20`,自动成立。 -/
def noConflictOK : Bool :=
  (range 24).all fun r =>
    (range 19).all fun d =>
      decide (d = 0) || decide (seqAt r + seqAt ((r + d) % 24) + d ≠ 20)

theorem allPosOK_eq : allPosOK = true := by decide
theorem allBoundOK_eq : allBoundOK = true := by decide
theorem allBound9OK_eq : allBound9OK = true := by decide
theorem allParityOK_eq : allParityOK = true := by decide
theorem noConflictOK_eq : noConflictOK = true := by decide

/-! ## 3. 从 Bool 检查回到命题 -/

lemma seqAt_pos {r : ℕ} (hr : r < 24) : 1 ≤ seqAt r := by
  have h := allPosOK_eq
  unfold allPosOK at h
  rw [List.all_eq_true] at h
  simpa using h r (List.mem_range.mpr hr)

lemma seqAt_bound {r : ℕ} (hr : r < 24) : 2 * seqAt r ≤ 20 := by
  have h := allBoundOK_eq
  unfold allBoundOK at h
  rw [List.all_eq_true] at h
  simpa using h r (List.mem_range.mpr hr)

lemma seqAt_le_nine {r : ℕ} (hr : r < 24) : seqAt r ≤ 9 := by
  have h := allBound9OK_eq
  unfold allBound9OK at h
  rw [List.all_eq_true] at h
  simpa using h r (List.mem_range.mpr hr)

lemma seqAt_parity {r : ℕ} (hr : r < 24) : seqAt r % 2 = r % 2 := by
  have h := allParityOK_eq
  unfold allParityOK at h
  rw [List.all_eq_true] at h
  simpa using h r (List.mem_range.mpr hr)

lemma seqAt_noConflict {r d : ℕ} (hr : r < 24) (hd0 : d ≠ 0) (hd : d ≤ 18) :
    seqAt r + seqAt ((r + d) % 24) + d ≠ 20 := by
  have h := noConflictOK_eq
  unfold noConflictOK at h
  rw [List.all_eq_true] at h
  have h1 := h r (List.mem_range.mpr hr)
  rw [List.all_eq_true] at h1
  have h2 := h1 d (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 hd0
  · exact h2

/-! ## 4. 周期性与移位 -/

lemma emod24_lt (i : ℤ) : (i % 24).toNat < 24 := by omega

/-- 周期 24。 -/
theorem aSeq_periodic (i : ℤ) : aSeq (i + 24) = aSeq i := by
  unfold aSeq
  congr 1
  omega

/-- 把 `aSeq (i + d)` 化成只依赖 `i % 24` 与 `d` 的形式(`d < 24`)。
这是「有限化归约」的技术核心。 -/
lemma aSeq_add_nat (i : ℤ) {d : ℕ} (hd : d < 24) :
    aSeq (i + (d : ℤ)) = seqAt (((i % 24).toNat + d) % 24) := by
  unfold aSeq
  congr 1
  omega

/-! ## 5. 序列的三条性质 -/

lemma aSeq_pos (i : ℤ) : 1 ≤ aSeq i := seqAt_pos (emod24_lt i)

/-- 论文:"It is clearly an odd-even sequence"。 -/
theorem aSeq_isOddEven : IsOddEvenSeq aSeq := by
  intro i
  have hlt := emod24_lt i
  have hpar := seqAt_parity hlt
  unfold aSeq
  omega

/-- 论文:"and `aᵢ ≤ 10 = 20/2` for all `i ∈ ℤ`"。

(实际该序列的最大值是 9;论文写 `≤ 10` 是为对齐 Definition 2.3 里的 `≤ k/2`。) -/
lemma aSeq_le_half (i : ℤ) : 2 * aSeq i ≤ 20 := seqAt_bound (emod24_lt i)

/-- 序列的实际最大值是 `9`。T1.3(ii) 里论文写的「`20 > 2 · max xᵢ = 18`」用的正是这个
(而不是 Definition 2.3 里那条较松的 `aᵢ ≤ k/2 = 10`)。 -/
lemma aSeq_le_nine (i : ℤ) : aSeq i ≤ 9 := seqAt_le_nine (emod24_lt i)

/-- 无冲突条件,先在 `i < j` 上证(定义里的条件对 `i, j` 对称)。 -/
lemma aSeq_noConflict_of_lt {i j : ℤ} (hij : i < j) :
    aSeq i + aSeq j + (i - j).natAbs ≠ 20 := by
  -- `d := j - i ≥ 1`
  obtain ⟨d, hd0, hdj⟩ : ∃ d : ℕ, d ≠ 0 ∧ j = i + (d : ℤ) :=
    ⟨(j - i).toNat, by omega, by omega⟩
  have habs : (i - j).natAbs = d := by omega
  subst hdj
  rw [habs]
  by_cases hbig : 19 ≤ d
  · -- `d` 太大:两项都 `≥ 1`,和 `≥ d + 2 ≥ 21 > 20`
    have h1 := aSeq_pos i
    have h2 := aSeq_pos (i + (d : ℤ))
    omega
  · -- `d ≤ 18`:落进有限检查
    push_neg at hbig
    rw [aSeq_add_nat i (by omega : d < 24), aSeq_def]
    exact seqAt_noConflict (emod24_lt i) hd0 (by omega)

/-- **Theorem 2.5.** *There is a 20-avoiding odd-even sequence.*

`aSeq` 就是那个序列:它是 odd-even 的(`aSeq_isOddEven`),并且是 20-avoiding 的。 -/
theorem aSeq_isKAvoiding : IsKAvoiding 20 aSeq := by
  refine ⟨aSeq_le_half, ?_⟩
  intro i j hij
  rcases lt_trichotomy i j with h | h | h
  · exact aSeq_noConflict_of_lt h
  · exact absurd h hij
  · -- 对称:交换 i, j
    have hji := aSeq_noConflict_of_lt h
    have habs : (j - i).natAbs = (i - j).natAbs := by omega
    omega

/-- **Theorem 2.5**(存在性形式,与论文陈述逐字对应)。 -/
theorem theorem_2_5 : ∃ a : ℤ → ℕ, IsOddEvenSeq a ∧ IsKAvoiding 20 a :=
  ⟨aSeq, aSeq_isOddEven, aSeq_isKAvoiding⟩

end Erdos815
