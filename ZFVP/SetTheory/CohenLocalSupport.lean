import ZFVP.SetTheory.CohenLeastSupport
import ZFVP.SetTheory.LocalizedSaturatedName
import ZFVP.SetTheory.NameOrbit

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem cohen_localizedSaturatedName_support {U τ E p : V}
    (hτ : IsForcingName (cohenConditions (ω : V)) τ)
    (hE : IsCohenNameSupport τ E) (hp : p ∈ cohenConditions (ω : V))
    (hU : ∀ π, IsInternalPermutation (ω : V) π → ∀ ν,
      IsForcingName (cohenConditions (ω : V)) ν →
      (nameAction (cohenPermutation (ω : V) π) ν ∈ U ↔ ν ∈ U)) :
    IsCohenNameSupport
      (localizedSaturatedName (cohenConditions (ω : V)) (cohenOrder (ω : V)) U τ p)
      (E ∪ cohenSupport p) := by
  refine ⟨?_, internallyFinite_union hE.2.1 (cohenSupport_finite hp), ?_⟩
  · intro i hi
    exact (mem_union_iff.mp hi).elim (hE.1 i) (cohenSupport_subset hp i)
  · intro π hπ hfix
    apply nameAction_localizedSaturatedName_fixed (cohenPermutation_automorphism hπ) hτ hp
      (hE.2.2 π hπ (fun i hi ↦ hfix i (mem_union_iff.mpr (Or.inl hi))))
    · rw [cohenPermutation_value hp]
      exact cohenConditionAction_fix hp (fun i hi ↦ hfix i (mem_union_iff.mpr (Or.inr hi)))
    · exact hU π hπ

theorem cohenName_hereditarilySymmetric_of_support {τ E : V}
    (hτ : IsForcingName (cohenConditions (ω : V)) τ) (hE : IsCohenNameSupport τ E)
    (hsub : ∀ ν p, ⟨ν, p⟩ₖ ∈ τ → IsHereditarilySymmetricName
      (cohenConditions (ω : V)) (cohenGroup (ω : V)) (cohenFilter (ω : V)) ν) :
    IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ := by
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨hτ, ?_⟩, hsub⟩
  apply (mem_cohenFilter_iff (ω : V) _).mpr
  refine ⟨nameStabilizer_subgroup (cohenGroup_group (ω : V)) hτ, E, hE.1, hE.2.1, ?_⟩
  intro π hπ hfix
  exact mem_sep_iff.mpr ⟨(mem_cohenGroup (ω : V) _).mpr ⟨π, hπ, rfl⟩, hE.2.2 π hπ hfix⟩

/-- Names equal below `p` admit an actual common representative supported by the intersection
of their supports together with the coordinates of `p`. No quotient action is assumed. -/
theorem cohen_common_representative_below {τ σ E F p : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ)
    (hσ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) σ)
    (hE : IsCohenNameSupport τ E) (hF : IsCohenNameSupport σ F)
    (hp : p ∈ cohenConditions (ω : V))
    (he : p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) τ σ) :
    ∃ ν, IsHereditarilySymmetricName (cohenConditions (ω : V))
        (cohenGroup (ω : V)) (cohenFilter (ω : V)) ν ∧
      p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) ν τ ∧
      IsCohenNameSupport ν ((E ∩ F) ∪ cohenSupport p) := by
  let B := domain τ ∪ domain σ
  let U := nameOrbit (cohenGroup (ω : V)) B
  have hΓ := cohenGroup_group (ω : V)
  have hH := forcingGroup_subgroup_self hΓ
  have hB : ∀ μ ∈ B, IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) μ := by
    intro μ hμ
    rcases mem_union_iff.mp hμ with hμ | hμ
    · obtain ⟨q, hq⟩ := mem_domain_iff.mp hμ
      exact (hereditarilySymmetric_iff _ _ _ _).mp hτ |>.2 μ q hq
    · obtain ⟨q, hq⟩ := mem_domain_iff.mp hμ
      exact (hereditarilySymmetric_iff _ _ _ _).mp hσ |>.2 μ q hq
  have hBU : B ⊆ U := subset_nameOrbit hH (fun μ hμ ↦ (hB μ hμ).1)
  have hUhs : ∀ μ ∈ U, IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) μ :=
    fun _ hμ ↦ hereditarilySymmetric_mem_nameOrbit hΓ (cohenFilter_normal (ω : V)) hH hB hμ
  have hU : ∀ π, IsInternalPermutation (ω : V) π → ∀ μ,
      IsForcingName (cohenConditions (ω : V)) μ →
      (nameAction (cohenPermutation (ω : V) π) μ ∈ U ↔ μ ∈ U) := by
    intro π hπ μ hμ
    exact nameOrbit_action_iff hΓ hH (fun μ hμ ↦ (hB μ hμ).1)
      ((mem_cohenGroup (ω : V) _).mpr ⟨π, hπ, rfl⟩) hμ
  let ν := localizedSaturatedName (cohenConditions (ω : V)) (cohenOrder (ω : V)) U τ p
  have hν := localizedSaturatedName_isName (cohenConditions (ω : V)) (cohenOrder (ω : V)) U τ p
  have hEν : IsCohenNameSupport ν (E ∪ cohenSupport p) :=
    cohen_localizedSaturatedName_support hτ.1 hE hp hU
  have hνhs : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) ν := by
    apply cohenName_hereditarilySymmetric_of_support hν hEν
    intro μ q hμq
    exact hUhs μ ((pair_mem_localizedSaturatedName _ _ _ _ _ _ _).mp hμq).1
  have hFν : IsCohenNameSupport ν (F ∪ cohenSupport p) := by
    have hh := cohen_localizedSaturatedName_support hσ.1 hF hp hU
    have heq := localizedSaturatedName_eq_of_atomicEquality (U := U) (cohen_poset (ω : V)).1 he
    rwa [← heq] at hh
  refine ⟨ν, hνhs, localizedSaturatedName_atomicEquality (cohen_poset (ω : V)).1 hτ.1
    (fun μ hμ ↦ hBU μ (mem_union_iff.mpr (Or.inl hμ))) hp, ?_⟩
  have hs := hEν.inter hνhs hFν
  have heq : (E ∪ cohenSupport p) ∩ (F ∪ cohenSupport p) = (E ∩ F) ∪ cohenSupport p := by
    apply mem_ext
    intro i
    simp only [mem_inter_iff, mem_union_iff]
    tauto
  rwa [heq] at hs

end ZFVP
