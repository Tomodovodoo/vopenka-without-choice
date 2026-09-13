import ZFVP.SetTheory.Collection
import ZFVP.SetTheory.NameOrbit

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem classForcingImageWitnessBound (P τ : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    (A : V → V → V) (hA : ℒₛₑₜ-function₂ A) :
    ∃ B : V, (∀ ν ∈ B, N ν) ∧ ∀ σ ∈ domain τ, ∀ p ∈ P,
      (∃ ν, N ν ∧ p ∈ A σ ν) → ∃ ν ∈ B, p ∈ A σ ν := by
  let C : V := {z ∈ domain τ ×ˢ P ; ∃ ν, N ν ∧ kpair.π₂ z ∈ A (kpair.π₁ z) ν}
  obtain ⟨B, hB⟩ := collection C
    (fun z ν ↦ N ν ∧ kpair.π₂ z ∈ A (kpair.π₁ z) ν) (by definability)
    (fun z hz ↦ (mem_sep_iff.mp hz).2)
  refine ⟨sep B N hN, fun ν hν ↦ (mem_sep_iff.mp hν).2, ?_⟩
  intro σ hσ p hp hex
  have hz : ⟨σ, p⟩ₖ ∈ C := by
    simpa only [C, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair] using ⟨⟨hσ, hp⟩, hex⟩
  obtain ⟨ν, hνB, hνN, hνA⟩ := hB ⟨σ, p⟩ₖ hz
  exact ⟨ν, mem_sep_iff.mpr ⟨hνB, hνN⟩, by simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hνA⟩

theorem symmetricImageWitnessBound {P R Γ F H : V}
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hF : IsNormalSubgroupFilter P Γ F)
    (hH : H ∈ F) (τ : V) (A : V → V → V) (hA : ℒₛₑₜ-function₂ A) :
    ∃ B : V, (∀ ν ∈ B, IsHereditarilySymmetricName P Γ F ν) ∧
      (∀ π ∈ H, ∀ ν, IsForcingName P ν → (nameAction π ν ∈ B ↔ ν ∈ B)) ∧
      ∀ σ ∈ domain τ, ∀ p ∈ P,
        (∃ ν, IsHereditarilySymmetricName P Γ F ν ∧ p ∈ A σ ν) → ∃ ν ∈ B, p ∈ A σ ν := by
  obtain ⟨C, hC, hbound⟩ := classForcingImageWitnessBound P τ
    (IsHereditarilySymmetricName P Γ F) (by definability) A hA
  have hCN : ∀ ν ∈ C, IsForcingName P ν := fun ν hν ↦ (hC ν hν).1
  refine ⟨nameOrbit H C, fun ν hν ↦ hereditarilySymmetric_mem_nameOrbit hΓ hF (hF.1 H hH) hC hν,
    fun π hπ ν hν ↦ nameOrbit_action_iff hΓ (hF.1 H hH) hCN hπ hν, ?_⟩
  intro σ hσ p hp hex
  obtain ⟨ν, hν, hνA⟩ := hbound σ hσ p hp hex
  exact ⟨ν, subset_nameOrbit (hF.1 H hH) hCN ν hν, hνA⟩

end ZFVP
