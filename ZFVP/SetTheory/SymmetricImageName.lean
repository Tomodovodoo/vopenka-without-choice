import ZFVP.SetTheory.ForcingImageName
import ZFVP.SetTheory.NameActionMembership

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameAction_forcingImageName_fixed {P R Γ F π τ B : V}
    (hπ : IsForcingAutomorphism P R π) (hτ : IsHereditarilySymmetricName P Γ F τ)
    (hfix : nameAction π τ = τ) (hB : ∀ ν ∈ B, IsHereditarilySymmetricName P Γ F ν)
    (hstable : ∀ ν, IsForcingName P ν → (nameAction π ν ∈ B ↔ ν ∈ B))
    (A : V → V → V) (hA : ℒₛₑₜ-function₂ A)
    (he : ∀ σ ν, IsHereditarilySymmetricName P Γ F σ → IsHereditarilySymmetricName P Γ F ν →
      ∀ p ∈ P, π ‘ p ∈ A (nameAction π σ) (nameAction π ν) ↔ p ∈ A σ ν) :
    nameAction π (forcingImageName P R τ B A hA) = forcingImageName P R τ B A hA := by
  have hn := forcingImageName_isName P R τ B A hA
  apply nameAction_eq_of_pair_iff hπ hn hn
  intro ν hν p hp
  rw [mem_forcingImageName_iff, mem_forcingImageName_iff]
  constructor
  · rintro ⟨hνB, _, _, σ', s', hs', hps', hpA⟩
    have hνB' := (hstable ν hν).mp hνB
    obtain ⟨σ, s, hs, hepair⟩ := (mem_nameAction_iff hτ.1 π _).mp (hfix.symm ▸ hs')
    obtain ⟨heσ, hes⟩ := kpair_iff.mp hepair
    subst σ'
    subst s'
    have hσH := (hereditarilySymmetric_iff _ _ _ _).mp hτ |>.2 σ s hs
    exact ⟨hνB', hp, hν, σ, s, hs,
      (hπ.2.2.2 p hp s (forcingName_condition hτ.1 hs)).mpr hps',
      (he σ ν hσH (hB ν hνB') p hp).mp hpA⟩
  · rintro ⟨hνB, _, _, σ, s, hs, hps, hpA⟩
    have hσH := (hereditarilySymmetric_iff _ _ _ _).mp hτ |>.2 σ s hs
    exact ⟨(hstable ν hν).mpr hνB, function_value_mem hπ.1 hp, nameAction_isName hπ.1 hν,
      nameAction π σ, π ‘ s, hfix ▸ (mem_nameAction_iff hτ.1 π _).mpr ⟨σ, s, hs, rfl⟩,
      (hπ.2.2.2 p hp s (forcingName_condition hτ.1 hs)).mp hps,
      (he σ ν hσH (hB ν hνB) p hp).mpr hpA⟩

theorem hereditarilySymmetric_forcingImageName {P R Γ F H τ B : V}
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hF : IsNormalSubgroupFilter P Γ F)
    (hH : H ∈ F) (hτ : IsHereditarilySymmetricName P Γ F τ)
    (hfix : ∀ π ∈ H, nameAction π τ = τ) (hB : ∀ ν ∈ B, IsHereditarilySymmetricName P Γ F ν)
    (hstable : ∀ π ∈ H, ∀ ν, IsForcingName P ν → (nameAction π ν ∈ B ↔ ν ∈ B))
    (A : V → V → V) (hA : ℒₛₑₜ-function₂ A)
    (he : ∀ π ∈ H, ∀ σ ν, IsHereditarilySymmetricName P Γ F σ → IsHereditarilySymmetricName P Γ F ν →
      ∀ p ∈ P, π ‘ p ∈ A (nameAction π σ) (nameAction π ν) ↔ p ∈ A σ ν) :
    IsHereditarilySymmetricName P Γ F (forcingImageName P R τ B A hA) := by
  have hn := forcingImageName_isName P R τ B A hA
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨hn, ?_⟩, ?_⟩
  · apply hF.2.2.1 H hH _ (nameStabilizer_subgroup hΓ hn)
    intro π hπ
    have hπΓ := (hF.1 H hH).1 π hπ
    exact mem_sep_iff.mpr ⟨hπΓ,
      nameAction_forcingImageName_fixed (hΓ.1 π hπΓ) hτ (hfix π hπ) hB (hstable π hπ) A hA (he π hπ)⟩
  · intro ν p hp
    exact hB ν ((mem_forcingImageName_iff _ _ _ _ A hA _ _).mp hp).1

end ZFVP
