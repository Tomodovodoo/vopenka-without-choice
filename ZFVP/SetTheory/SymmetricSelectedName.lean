import ZFVP.SetTheory.ForcingSelectedName
import ZFVP.SetTheory.NameActionMembership

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameAction_forcingSelectedName_fixed {P R Γ F π τ : V}
    (hπ : IsForcingAutomorphism P R π) (hτ : IsHereditarilySymmetricName P Γ F τ)
    (hfix : nameAction π τ = τ) (A : V → V) (hA : ℒₛₑₜ-function₁ A)
    (he : ∀ ν, IsHereditarilySymmetricName P Γ F ν → ∀ p ∈ P,
      π ‘ p ∈ A (nameAction π ν) ↔ p ∈ A ν) :
    nameAction π (forcingSelectedName P R τ A hA) = forcingSelectedName P R τ A hA := by
  have hn := forcingSelectedName_isName (R := R) hτ.1 A hA
  apply nameAction_eq_of_pair_iff hπ hn hn
  intro ν hν q hq
  rw [mem_forcingSelectedName_iff, mem_forcingSelectedName_iff]
  constructor
  · rintro ⟨_, s', hs', hqs', hAq⟩
    obtain ⟨s, hs, rfl⟩ := forcingAutomorphism_surjective hπ s' (forcingName_condition hτ.1 hs')
    have hpair : ⟨ν, s⟩ₖ ∈ τ := (nameAction_pair_mem_iff hπ hτ.1 hν hs).mp (hfix.symm ▸ hs')
    have hνH := (hereditarilySymmetric_iff _ _ _ _).mp hτ |>.2 ν s hpair
    exact ⟨hq, s, hpair, (hπ.2.2.2 q hq s hs).mpr hqs', (he ν hνH q hq).mp hAq⟩
  · rintro ⟨_, s, hs, hqs, hAq⟩
    have hsP := forcingName_condition hτ.1 hs
    have hνH := (hereditarilySymmetric_iff _ _ _ _).mp hτ |>.2 ν s hs
    exact ⟨function_value_mem hπ.1 hq, π ‘ s,
      hfix ▸ (nameAction_pair_mem_iff hπ hτ.1 hν hsP).mpr hs,
      (hπ.2.2.2 q hq s hsP).mp hqs, (he ν hνH q hq).mpr hAq⟩

theorem hereditarilySymmetric_forcingSelectedName {P R Γ F τ H : V}
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hF : IsNormalSubgroupFilter P Γ F)
    (hτ : IsHereditarilySymmetricName P Γ F τ) (hH : H ∈ F)
    (hfix : ∀ π ∈ H, nameAction π τ = τ) (A : V → V) (hA : ℒₛₑₜ-function₁ A)
    (he : ∀ π ∈ H, ∀ ν, IsHereditarilySymmetricName P Γ F ν → ∀ p ∈ P,
      π ‘ p ∈ A (nameAction π ν) ↔ p ∈ A ν) :
    IsHereditarilySymmetricName P Γ F (forcingSelectedName P R τ A hA) := by
  have hn := forcingSelectedName_isName (R := R) hτ.1 A hA
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨hn, ?_⟩, ?_⟩
  · apply hF.2.2.1 H hH _ (nameStabilizer_subgroup hΓ hn)
    intro π hπ
    have hπΓ := (hF.1 H hH).1 π hπ
    exact mem_sep_iff.mpr ⟨hπΓ,
      nameAction_forcingSelectedName_fixed (hΓ.1 π hπΓ) hτ (hfix π hπ) A hA (he π hπ)⟩
  · intro ν q hq
    obtain ⟨_, s, hs, _, _⟩ := (mem_forcingSelectedName_iff _ _ _ _ _ _ _).mp hq
    exact (hereditarilySymmetric_iff _ _ _ _).mp hτ |>.2 ν s hs

end ZFVP
