import ZFVP.SetTheory.ForcingNames
import ZFVP.SetTheory.ForcingRegular

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingSelectedName (P R τ : V) (F : V → V) (hF : ℒₛₑₜ-function₁ F) : V :=
  {z ∈ domain τ ×ˢ P ; ∃ s, ⟨kpair.π₁ z, s⟩ₖ ∈ τ ∧
    ⟨kpair.π₂ z, s⟩ₖ ∈ R ∧ kpair.π₂ z ∈ F (kpair.π₁ z)}

theorem mem_forcingSelectedName_iff (P R τ : V) (F : V → V) (hF : ℒₛₑₜ-function₁ F) (ν q : V) :
    ⟨ν, q⟩ₖ ∈ forcingSelectedName P R τ F hF ↔
      q ∈ P ∧ ∃ s, ⟨ν, s⟩ₖ ∈ τ ∧ ⟨q, s⟩ₖ ∈ R ∧ q ∈ F ν := by
  simp only [forcingSelectedName, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  constructor
  · rintro ⟨⟨_, hq⟩, h⟩
    exact ⟨hq, h⟩
  · rintro ⟨hq, s, hs, hqs, hFq⟩
    exact ⟨⟨mem_domain_of_kpair_mem hs, hq⟩, s, hs, hqs, hFq⟩

theorem forcingSelectedName_subset (P R τ : V) (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    forcingSelectedName P R τ F hF ⊆ domain τ ×ˢ P := fun _ h ↦ (mem_sep_iff.mp h).1

theorem forcingSelectedName_isName {P R τ : V} (hτ : IsForcingName P τ)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) : IsForcingName P (forcingSelectedName P R τ F hF) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨ν, _, q, hq, rfl⟩ := mem_prod_iff.mp (forcingSelectedName_subset _ _ _ _ _ _ hz)
  obtain ⟨_, s, hs, _, _⟩ := (mem_forcingSelectedName_iff _ _ _ _ _ _ _).mp hz
  exact ⟨ν, q, hq, rfl, forcingName_subname hτ hs⟩

end ZFVP
