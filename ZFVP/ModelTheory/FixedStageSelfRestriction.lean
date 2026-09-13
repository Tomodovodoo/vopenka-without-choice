import ZFVP.ModelTheory.CriticalSequenceFixedPoint
import ZFVP.ModelTheory.CriticalPointRestriction

/-! Restricting an embedding between two rank stages to the stage of an ordinal it fixes.

If `f` embeds `hierarchy δ` into `hierarchy ε` and `f ‘ η = η` for an ordinal `η` above the
critical point, then `f ↾ (hierarchy η)` is an embedding of `hierarchy η` into itself with the
same critical point and the same critical sequence. This is the step used in Bagaria's converse
arguments, where Kunen's theorem is applied to the restricted self-embedding. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The restriction of `f` to the stage of a fixed ordinal `η` above the critical point is an
embedding of `hierarchy η` into itself. -/
theorem selfRestriction_of_fixed_ordinal {k l : ℕ} {δ ε f η κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hη : IsOrdinal η) (hηδ : η ∈ hierarchy δ) (hfix : f ‘ η = η) (hκη : κ ∈ η) :
    IsCodedMembershipEmbedding (hierarchy η) (hierarchy η) (f ↾ (hierarchy η)) := by
  let := hη
  let := hκ.ordinal
  have hne : IsNonempty (hierarchy η) := ⟨κ, ordinal_mem_hierarchy_iff.mpr hκη⟩
  have hr := rankEmbedding_restrict hδ hε h (hδ.hierarchy_closed hη hηδ) hne
  rwa [(rankEmbedding_value_hierarchy hδ hε h hη hηδ).2, hfix] at hr

/-- The restricted embedding has the same critical point. -/
theorem criticalPoint_selfRestriction {k l : ℕ} {δ ε f η κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hη : IsOrdinal η) (hηδ : η ∈ hierarchy δ) (hfix : f ‘ η = η) (hκη : κ ∈ η) :
    IsCriticalPoint (hierarchy η) (f ↾ (hierarchy η)) κ := by
  let := hη
  let := hκ.ordinal
  let := hδ.ordinal
  let := hierarchy_transitive δ
  let := hierarchy_transitive η
  exact hκ.restrict h.function
    (IsTransitive.transitive (hierarchy η) (hδ.hierarchy_closed hη hηδ))
    (ordinal_mem_hierarchy_iff.mpr hκη)

/-- Every critical iterate stays below a fixed ordinal above the critical point. -/
theorem criticalIterate_mem_fixed_ordinal {k l : ℕ} {δ ε f η κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hη : IsOrdinal η) (hηδ : η ∈ hierarchy δ) (hfix : f ‘ η = η) (hκη : κ ∈ η) :
    ∀ n ∈ (ω : V), criticalIterate f κ n ∈ η := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  have hsub : η ⊆ hierarchy δ := IsTransitive.transitive η hηδ
  apply naturalNumber_induction (fun n ↦ criticalIterate f κ n ∈ η) (by definability)
  · simpa using hκη
  · intro n hn ih
    rw [criticalIterate_succ f κ hn, ← hfix]
    exact (h.value_mem_iff (hsub _ ih) hηδ).mpr ih

/-- The restricted embedding produces the same critical iterates. -/
theorem criticalIterate_selfRestriction {k l : ℕ} {δ ε f η κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hη : IsOrdinal η) (hηδ : η ∈ hierarchy δ) (hfix : f ‘ η = η) (hκη : κ ∈ η) :
    ∀ n ∈ (ω : V), criticalIterate (f ↾ (hierarchy η)) κ n = criticalIterate f κ n := by
  let := hη
  let := hδ.ordinal
  let := hierarchy_transitive δ
  have : IsFunction f := IsFunction.of_mem h.function
  have hsub : η ⊆ hierarchy δ := IsTransitive.transitive η hηδ
  have hstage : ∀ x ∈ η, x ∈ hierarchy η := by
    intro x hx
    let := IsOrdinal.of_mem hx
    exact ordinal_mem_hierarchy_iff.mpr hx
  have hbelow := criticalIterate_mem_fixed_ordinal hδ hε h hκ hη hηδ hfix hκη
  apply naturalNumber_induction
    (fun n ↦ criticalIterate (f ↾ (hierarchy η)) κ n = criticalIterate f κ n) (by definability)
  · simp
  · intro n hn ih
    rw [criticalIterate_succ (f ↾ (hierarchy η)) κ hn, criticalIterate_succ f κ hn, ih]
    exact value_restrict
      (by rw [domain_eq_of_mem_function h.function]; exact hsub _ (hbelow n hn))
      (hstage _ (hbelow n hn))

/-- The restricted embedding has the same critical limit. -/
theorem criticalLimit_selfRestriction {k l : ℕ} {δ ε f η κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hη : IsOrdinal η) (hηδ : η ∈ hierarchy δ) (hfix : f ‘ η = η) (hκη : κ ∈ η) :
    criticalLimit (f ↾ (hierarchy η)) κ = criticalLimit f κ := by
  have hit := criticalIterate_selfRestriction hδ hε h hκ hη hηδ hfix hκη
  apply mem_ext
  intro x
  rw [mem_criticalLimit_iff, mem_criticalLimit_iff]
  constructor
  · rintro ⟨n, hn, hx⟩
    exact ⟨n, hn, hit n hn ▸ hx⟩
  · rintro ⟨n, hn, hx⟩
    exact ⟨n, hn, (hit n hn).symm ▸ hx⟩

end ZFVP
