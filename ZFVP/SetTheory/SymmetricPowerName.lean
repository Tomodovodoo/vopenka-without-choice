import ZFVP.SetTheory.SymmetricFormulaForcing
import ZFVP.SetTheory.NameActionBounds

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def symmetricSubsetConditions (P R Γ F ρ τ : V) : V :=
  symmetricForcingFormula P R Γ F isSubsetOf (standardTuple ![ρ, τ])

instance symmetricSubsetConditions_definable (P R Γ F : V) :
    ℒₛₑₜ-function₂[V] (symmetricSubsetConditions P R Γ F) := by
  unfold symmetricSubsetConditions standardTuple
  definability

noncomputable def symmetricPowerName (P R Γ F τ : V) : V :=
  {z ∈ ℘ (domain τ ×ˢ P) ×ˢ P ; IsHereditarilySymmetricName P Γ F (kpair.π₁ z) ∧
    kpair.π₂ z ∈ symmetricSubsetConditions P R Γ F (kpair.π₁ z) τ}

theorem mem_symmetricPowerName_iff (P R Γ F τ ρ p : V) :
    ⟨ρ, p⟩ₖ ∈ symmetricPowerName P R Γ F τ ↔
      ρ ⊆ domain τ ×ˢ P ∧ p ∈ P ∧ IsHereditarilySymmetricName P Γ F ρ ∧
        p ∈ symmetricSubsetConditions P R Γ F ρ τ := by
  simp only [symmetricPowerName, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, mem_power_iff]
  tauto

theorem symmetricPowerName_isName (P R Γ F τ : V) : IsForcingName P (symmetricPowerName P R Γ F τ) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨ρ, _, p, hp, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  exact ⟨ρ, p, hp, rfl, ((mem_symmetricPowerName_iff _ _ _ _ _ _ _).mp hz).2.2.1.1⟩

theorem symmetricSubsetConditions_action_iff {P R Γ F π ρ τ p : V}
    (hR : IsForcingPreorder P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hπ : π ∈ Γ)
    (hρ : IsHereditarilySymmetricName P Γ F ρ) (hτ : IsHereditarilySymmetricName P Γ F τ)
    (hp : p ∈ P) :
    π ‘ p ∈ symmetricSubsetConditions P R Γ F (nameAction π ρ) (nameAction π τ) ↔
      p ∈ symmetricSubsetConditions P R Γ F ρ τ := by
  have hh := symmetricForcingFormula_nameAction_iff hR hΓ hF hπ isSubsetOf ![ρ, τ]
    (fun i ↦ Fin.cases hρ (fun j ↦ Fin.cases hτ (fun k ↦ Fin.elim0 k) j) i) hp
  have he : (fun i ↦ nameAction π (![ρ, τ] i)) = ![nameAction π ρ, nameAction π τ] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  simpa only [he, symmetricSubsetConditions] using hh

theorem nameAction_symmetricPowerName_fixed {P R Γ F π τ : V}
    (hR : IsForcingPreorder P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hπ : π ∈ Γ)
    (hτ : IsHereditarilySymmetricName P Γ F τ) (hfix : nameAction π τ = τ) :
    nameAction π (symmetricPowerName P R Γ F τ) = symmetricPowerName P R Γ F τ := by
  have ha := hΓ.1 π hπ
  have hn := symmetricPowerName_isName P R Γ F τ
  apply nameAction_eq_of_pair_iff ha hn hn
  intro ρ hρ p hp
  rw [mem_symmetricPowerName_iff, mem_symmetricPowerName_iff]
  have hb : nameAction π ρ ⊆ domain τ ×ˢ P ↔ ρ ⊆ domain τ ×ˢ P := by
    simpa only [hfix] using nameAction_bounded_iff ha hρ hτ.1
  have hH := hereditarilySymmetric_nameAction_iff hΓ hF hπ hρ
  constructor
  · rintro ⟨hB, _, hρH, hpF⟩
    have hρH' := hH.mp hρH
    refine ⟨hb.mp hB, hp, hρH', ?_⟩
    have hh := symmetricSubsetConditions_action_iff hR hΓ hF hπ hρH' hτ hp
    rw [hfix] at hh
    exact hh.mp hpF
  · rintro ⟨hB, _, hρH, hpF⟩
    refine ⟨hb.mpr hB, function_value_mem ha.1 hp, hH.mpr hρH, ?_⟩
    have hh := symmetricSubsetConditions_action_iff hR hΓ hF hπ hρH hτ hp
    rw [hfix] at hh
    exact hh.mpr hpF

theorem hereditarilySymmetric_symmetricPowerName {P R Γ F τ : V}
    (hR : IsForcingPreorder P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hτ : IsHereditarilySymmetricName P Γ F τ) :
    IsHereditarilySymmetricName P Γ F (symmetricPowerName P R Γ F τ) := by
  have hn := symmetricPowerName_isName P R Γ F τ
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨hn, ?_⟩, ?_⟩
  · apply hF.2.2.1 _ (hereditarilySymmetric_symmetric hτ).2 _ (nameStabilizer_subgroup hΓ hn)
    intro π hπ
    obtain ⟨hπΓ, hfix⟩ := mem_sep_iff.mp hπ
    exact mem_sep_iff.mpr ⟨hπΓ, nameAction_symmetricPowerName_fixed hR hΓ hF hπΓ hτ hfix⟩
  · intro ρ p hp
    exact ((mem_symmetricPowerName_iff _ _ _ _ _ _ _).mp hp).2.2.1

end ZFVP
