/-
# 沿图同构搬运 `IsDegree3Critical` 与 `HasCycleOfLength`(step 5 辅助文件)

蓝图 §0 把最终陈述定死为

```lean
∃ G : ℕ → (Σ n : ℕ, SimpleGraph (Fin n)), …
```

即顶点类型必须是 `Fin N`。而我们构造出来的图 `G(T(x₁…xₙ))` 的顶点类型是
`TVtx x n ⊕ Bool` —— 一个由归纳类型 + 子类型 + `Sum` 拼出来的东西。二者当然同构,
但「同构」这件事在 Lean 里不是自动的:必须把两条性质逐一搬过去。

**为什么最终陈述要用 `Fin n` 而不是直接 `Σ V : Type, SimpleGraph V`**:
`IsDegree3Critical` 里的 `edgeFinset.card` 与 `Fintype.card V` 要求 `Fintype`,
而 `Fin n` 免费给出它,且 `(G i).1 < (G j).1` 直接就是「顶点数严格递增」的写法,
不必再套一层 `Fintype.card`。代价就是本文件 —— 一次性付清。

本文件证两条:

| 引理 | 内容 |
|---|---|
| `IsDegree3Critical.of_iso` | 同构保持 degree 3-critical |
| `hasCycleOfLength_of_iso` | 同构保持「含长 `ℓ` 的圈」(两个方向) |

**关键坑(与 step 2 记的是同一个)**:`IsDegree3Critical` 的定义带
`open scoped Classical`,里面的 `Fintype ↥s` / `DecidableRel` 实例是**定义里固化的闭项**,
与证明中 `inferInstance` 现场合成的只**定义相等**、不语法相同。所以本文件里凡是碰
`degree` 的地方都用 `Subsingleton.elim` / `convert` 把实例强行对齐,不指望 `simp` 自己配上。
-/
import Erdos815.Defs
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Erdos815

open SimpleGraph

universe u v

variable {V : Type u} {W : Type v}

/-! ## 1. 圈的搬运 -/

/-- 同构把长 `ℓ` 的圈搬到长 `ℓ` 的圈。

`Walk.map` 沿 `f.toHom` 推走,长度不变(`Walk.length_map`),`IsCycle` 由
`IsCycle.map` 保持(`f` 单射)。 -/
lemma hasCycleOfLength_of_iso {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) {ℓ : ℕ}
    (h : HasCycleOfLength G ℓ) : HasCycleOfLength H ℓ := by
  obtain ⟨a, c, hcyc, hlen⟩ := h
  refine ⟨f a, c.map f.toHom, ?_, ?_⟩
  · exact hcyc.map (f.toEquiv.injective)
  · simpa using hlen

/-! ## 2. degree 3-critical 的搬运

两半分开做:边数(用 `Iso.card_edgeFinset_eq`)与临界性(把顶点集 `s` 沿 `f` 搬过去)。 -/

section Critical

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- 导出子图上的度沿同构不变。

🔴 **两个 `Fintype` 实例写成显式参数**(step 2 踩过的坑):调用处的实例来自
`IsDegree3Critical` 定义里固化的 `open scoped Classical` 闭项,与这里 `inferInstance`
合成的只**定义相等**、不语法相同。写成显式参数后对任意实例都成立,调用处传 `_ _`
让 Lean 从目标反填即可。`Fintype` 是 `Subsingleton`,这样写不损失任何东西。

`hiso a` 与 `⟨f a.val, hbij.mapsTo a.2⟩` 是定义相等的(`Subtype` 的证明分量无关),
故 `Iso.degree_eq` 可直接 `exact`。 -/
lemma induce_degree_eq_of_iso (f : G ≃g H) {s : Set V} {t : Set W}
    (hbij : Set.BijOn (f : V → W) s t) (a : s)
    (i₁ : Fintype ((G.induce s).neighborSet a))
    (i₂ : Fintype ((H.induce t).neighborSet ⟨f a.val, hbij.mapsTo a.2⟩)) :
    @SimpleGraph.degree _ (H.induce t) ⟨f a.val, hbij.mapsTo a.2⟩ i₂
      = @SimpleGraph.degree _ (G.induce s) a i₁ := by
  -- `letI`(而非 `haveI`):let 绑定是透明的,`exact` 才能把它与显式参数 `i₁`/`i₂` 对上;
  -- `haveI` 引入的是不透明 fvar,定义相等检查过不去。
  let _ := i₁
  let _ : Fintype ((H.induce t).neighborSet ((f.induce hbij) a)) := i₂
  exact (f.induce hbij).degree_eq a

/-- **degree 3-critical 沿同构搬运。** -/
theorem IsDegree3Critical.of_iso [Fintype V] [Fintype W] (f : G ≃g H) (hG : IsDegree3Critical G) :
    IsDegree3Critical H := by
  classical
  obtain ⟨hedge, hcrit⟩ := hG
  constructor
  · -- 边数:`Iso.card_edgeFinset_eq` + 顶点数相等
    have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr f.toEquiv
    have he : G.edgeFinset.card = H.edgeFinset.card := f.card_edgeFinset_eq
    rw [← he, hedge, hcard]
  · -- 临界性:把 `t ⊆ W` 拉回成 `s := f⁻¹ '' t ⊆ V`
    intro t htne htuniv
    set s : Set V := (f.symm : W → V) '' t with hs
    have hbij : Set.BijOn (f : V → W) s t := by
      refine ⟨?_, f.toEquiv.injective.injOn, ?_⟩
      · rintro a ⟨w, hw, rfl⟩; simpa using hw
      · exact fun w hw => ⟨f.symm w, ⟨w, hw, rfl⟩, by simp⟩
    have hsne : s.Nonempty := by
      obtain ⟨w, hw⟩ := htne
      exact ⟨f.symm w, ⟨w, hw, rfl⟩⟩
    have hsuniv : s ≠ Set.univ := by
      intro hc
      refine htuniv (Set.eq_univ_of_forall fun w => ?_)
      have : f.symm w ∈ s := hc ▸ Set.mem_univ _
      obtain ⟨w', hw', hww'⟩ := this
      have : w' = w := by
        have := congrArg (f : V → W) hww'
        simpa using this
      exact this ▸ hw'
    obtain ⟨a, ha⟩ := hcrit s hsne hsuniv
    -- 实例传 `_ _`:第二个从目标反填(定义里的 classical 实例),第一个从 `ha` 反填。
    exact ⟨⟨f a.val, hbij.mapsTo a.2⟩,
      le_trans (le_of_eq (induce_degree_eq_of_iso f hbij a _ _)) ha⟩

end Critical

/-! ## 3. 搬到 `Fin N` 上

`Fintype V` 给出 `V ≃ Fin (Fintype.card V)`(`Fintype.equivFin`,noncomputable —— 无所谓,
我们只在 `Prop` 层用它),`Iso.map` 把它抬成图同构。 -/

/-- 把任意有限顶点类型上的图搬到 `Fin (card V)` 上,并保持两条性质。

返回的是 `Σ n, SimpleGraph (Fin n)`,其第一分量**恰为** `Fintype.card V` ——
这一点由 `finGraph_fst` 记录,顶点数递增的论证要用。 -/
noncomputable def finGraph [Fintype V] (G : SimpleGraph V) : Σ n : ℕ, SimpleGraph (Fin n) :=
  ⟨Fintype.card V, G.map (Fintype.equivFin V).toEmbedding⟩

@[simp] lemma finGraph_fst [Fintype V] (G : SimpleGraph V) :
    (finGraph G).1 = Fintype.card V := rfl

/-- `G ≃g (finGraph G).2` —— 搬运用的那个同构。 -/
noncomputable def finGraphIso [Fintype V] (G : SimpleGraph V) : G ≃g (finGraph G).2 :=
  Iso.map (Fintype.equivFin V) G

lemma finGraph_isDegree3Critical [Fintype V] {G : SimpleGraph V}
    (h : IsDegree3Critical G) : IsDegree3Critical (finGraph G).2 :=
  h.of_iso (finGraphIso G)

lemma finGraph_no_cycle [Fintype V] {G : SimpleGraph V} {ℓ : ℕ}
    (h : ¬ HasCycleOfLength G ℓ) : ¬ HasCycleOfLength (finGraph G).2 ℓ := by
  intro hc
  exact h (hasCycleOfLength_of_iso (finGraphIso G).symm hc)

end Erdos815
