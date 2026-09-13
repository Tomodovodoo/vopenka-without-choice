import ZFVP.SetTheory.FormulaForcing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingSubsetConditions (P R ρ τ : V) : V :=
  forcingFormula P R isSubsetOf (standardTuple ![ρ, τ])

instance forcingSubsetConditions_definable (P R : V) :
    ℒₛₑₜ-function₂[V] (forcingSubsetConditions P R) := by
  unfold forcingSubsetConditions standardTuple
  definability

noncomputable def forcingPowerName (P R τ : V) : V :=
  {z ∈ ℘ (domain τ ×ˢ P) ×ˢ P ; IsForcingName P (kpair.π₁ z) ∧
    kpair.π₂ z ∈ forcingSubsetConditions P R (kpair.π₁ z) τ}

theorem mem_forcingPowerName_iff (P R τ ρ p : V) :
    ⟨ρ, p⟩ₖ ∈ forcingPowerName P R τ ↔
      ρ ⊆ domain τ ×ˢ P ∧ p ∈ P ∧ IsForcingName P ρ ∧ p ∈ forcingSubsetConditions P R ρ τ := by
  simp only [forcingPowerName, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair,
    mem_power_iff]
  tauto

theorem forcingPowerName_isName (P R τ : V) : IsForcingName P (forcingPowerName P R τ) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨ρ, _, p, hp, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  exact ⟨ρ, p, hp, rfl, ((mem_forcingPowerName_iff _ _ _ _ _).mp hz).2.2.1⟩

end ZFVP
