import ZFVP.SetTheory.ForcingNames
import ZFVP.SetTheory.Collection

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingImageWitnessBound (P τ : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    ∃ B : V, ∀ σ ∈ domain τ, ∀ p ∈ P,
      (∃ ν, IsForcingName P ν ∧ p ∈ F σ ν) →
        ∃ ν ∈ B, IsForcingName P ν ∧ p ∈ F σ ν := by
  let A : V := {z ∈ domain τ ×ˢ P ; ∃ ν, IsForcingName P ν ∧ kpair.π₂ z ∈ F (kpair.π₁ z) ν}
  obtain ⟨B, hB⟩ := collection A
    (fun z ν ↦ IsForcingName P ν ∧ kpair.π₂ z ∈ F (kpair.π₁ z) ν) (by definability)
    (fun z hz ↦ (mem_sep_iff.mp hz).2)
  refine ⟨B, ?_⟩
  intro σ hσ p hp hex
  have hz : ⟨σ, p⟩ₖ ∈ A := by
    simpa only [A, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair] using ⟨⟨hσ, hp⟩, hex⟩
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hB ⟨σ, p⟩ₖ hz

noncomputable def forcingImageName (P R τ B : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) : V :=
  {z ∈ B ×ˢ P ; IsForcingName P (kpair.π₁ z) ∧ ∃ σ s, ⟨σ, s⟩ₖ ∈ τ ∧
    ⟨kpair.π₂ z, s⟩ₖ ∈ R ∧ kpair.π₂ z ∈ F σ (kpair.π₁ z)}

theorem mem_forcingImageName_iff (P R τ B : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (ν p : V) :
    ⟨ν, p⟩ₖ ∈ forcingImageName P R τ B F hF ↔
      ν ∈ B ∧ p ∈ P ∧ IsForcingName P ν ∧ ∃ σ s, ⟨σ, s⟩ₖ ∈ τ ∧ ⟨p, s⟩ₖ ∈ R ∧ p ∈ F σ ν := by
  simp only [forcingImageName, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

theorem forcingImageName_isName (P R τ B : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    IsForcingName P (forcingImageName P R τ B F hF) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨ν, _, p, hp, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  exact ⟨ν, p, hp, rfl, ((mem_forcingImageName_iff _ _ _ _ F hF _ _).mp hz).2.2.1⟩

end ZFVP
