import ZFVP.SetTheory.SaturatedNameEquality
import ZFVP.SetTheory.AtomicForcingAction
import ZFVP.SetTheory.NameActionMembership

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Saturate the membership of `τ` using names in `U`, retaining only conditions below `p`. -/
noncomputable def localizedSaturatedName (P R U τ p : V) : V :=
  {z ∈ U ×ˢ P ; IsForcingName P (kpair.π₁ z) ∧
    ⟨kpair.π₂ z, p⟩ₖ ∈ R ∧ kpair.π₂ z ∈ atomicMembership P R (kpair.π₁ z) τ}

theorem pair_mem_localizedSaturatedName (P R U τ p ν q : V) :
    ⟨ν, q⟩ₖ ∈ localizedSaturatedName P R U τ p ↔
      ν ∈ U ∧ q ∈ P ∧ IsForcingName P ν ∧ ⟨q, p⟩ₖ ∈ R ∧
        q ∈ atomicMembership P R ν τ := by
  simp only [localizedSaturatedName, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

theorem localizedSaturatedName_isName (P R U τ p : V) :
    IsForcingName P (localizedSaturatedName P R U τ p) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨ν, hν, q, hq, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  exact ⟨ν, q, hq, rfl, ((pair_mem_localizedSaturatedName _ _ _ _ _ _ _).mp hz).2.2.1⟩

/-- Below its localization condition, the saturated name has the original value. -/
theorem localizedSaturatedName_atomicEquality {P R U τ p : V}
    (hR : IsForcingPreorder P R) (hτ : IsForcingName P τ)
    (hU : domain τ ⊆ U) (hp : p ∈ P) :
    p ∈ atomicEquality P R (localizedSaturatedName P R U τ p) τ := by
  apply (atomicEquality_iff_membership _ _ _ _ _ hR).mpr
  refine ⟨hp, ?_, ?_⟩
  · intro ν s hs q hq _ hqs
    have hh := (pair_mem_localizedSaturatedName _ _ _ _ _ _ _).mp hs
    exact atomicMembership_mono hR hh.2.2.2.2 hq hqs
  · intro ν s hs q hq hqp hqs
    apply atomicMembership_of_pair hR hq
    exact (pair_mem_localizedSaturatedName _ _ _ _ _ _ _).mpr
      ⟨hU _ (mem_domain_of_kpair_mem hs), hq, forcingName_subname hτ hs, hqp,
        atomicMembership_mono hR
          (atomicMembership_of_pair hR (forcingName_condition hτ hs) hs) hq hqs⟩

/-- Equality forced at `p` becomes literal equality of the localized saturated names. -/
theorem localizedSaturatedName_eq_of_atomicEquality {P R U τ σ p : V}
    (hR : IsForcingPreorder P R) (he : p ∈ atomicEquality P R τ σ) :
    localizedSaturatedName P R U τ p = localizedSaturatedName P R U σ p := by
  apply mem_ext
  intro z
  by_cases hz : z ∈ U ×ˢ P
  · obtain ⟨ν, hν, q, hq, rfl⟩ := mem_prod_iff.mp hz
    rw [pair_mem_localizedSaturatedName, pair_mem_localizedSaturatedName]
    constructor
    · rintro ⟨hν, hq, hn, hqp, hm⟩
      exact ⟨hν, hq, hn, hqp,
        ((atomicEquality_membership_iff hR (atomicEquality_mono hR he hq hqp) ν).2).mp hm⟩
    · rintro ⟨hν, hq, hn, hqp, hm⟩
      exact ⟨hν, hq, hn, hqp,
        ((atomicEquality_membership_iff hR (atomicEquality_mono hR he hq hqp) ν).2).mpr hm⟩
  · exact iff_of_false (fun h ↦ hz (mem_sep_iff.mp h).1)
      (fun h ↦ hz (mem_sep_iff.mp h).1)

theorem nameAction_localizedSaturatedName_fixed {P R U τ p π : V}
    (hπ : IsForcingAutomorphism P R π) (hτ : IsForcingName P τ) (hp : p ∈ P)
    (hτfix : nameAction π τ = τ) (hpfix : π ‘ p = p)
    (hU : ∀ ν, IsForcingName P ν → (nameAction π ν ∈ U ↔ ν ∈ U)) :
    nameAction π (localizedSaturatedName P R U τ p) = localizedSaturatedName P R U τ p := by
  apply nameAction_eq_of_pair_iff hπ (localizedSaturatedName_isName _ _ _ _ _)
    (localizedSaturatedName_isName _ _ _ _ _)
  intro ν hν q hq
  rw [pair_mem_localizedSaturatedName, pair_mem_localizedSaturatedName]
  have horder : ⟨π ‘ q, p⟩ₖ ∈ R ↔ ⟨q, p⟩ₖ ∈ R := by
    conv_lhs => rw [← hpfix]
    exact (hπ.2.2.2 q hq p hp).symm
  have hmem : π ‘ q ∈ atomicMembership P R (nameAction π ν) τ ↔
      q ∈ atomicMembership P R ν τ := by
    conv_lhs => rw [← hτfix]
    exact atomicMembership_nameAction_iff hπ hν hτ hq
  exact and_congr (hU ν hν) (and_congr
    (iff_of_true (function_value_mem hπ.1 hq) hq)
    (and_congr (iff_of_true (nameAction_isName hπ.1 hν) hν)
      (and_congr horder hmem)))

end ZFVP
