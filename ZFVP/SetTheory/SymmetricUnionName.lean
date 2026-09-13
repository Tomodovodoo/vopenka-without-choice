import ZFVP.SetTheory.ForcingUnionName
import ZFVP.SetTheory.NameActionMembership

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameAction_forcingUnionName {P R π τ : V} (hπ : IsForcingAutomorphism P R π)
    (hτ : IsForcingName P τ) :
    nameAction π (forcingUnionName P R τ) = forcingUnionName P R (nameAction π τ) := by
  apply nameAction_eq_of_pair_iff hπ (forcingUnionName_isName hτ)
    (forcingUnionName_isName (nameAction_isName hπ.1 hτ))
  intro ν hν q hq
  rw [mem_forcingUnionName_iff, mem_forcingUnionName_iff]
  constructor
  · rintro ⟨_, σ', s', t', hs', ht', hqs', hqt'⟩
    obtain ⟨σ, s, hs, he⟩ := (mem_nameAction_iff hτ π _).mp hs'
    obtain ⟨heσ, hes⟩ := kpair_iff.mp he
    subst σ'
    subst s'
    have hσ := forcingName_subname hτ hs
    obtain ⟨t, ht, rfl⟩ := forcingAutomorphism_surjective hπ t'
      (forcingName_condition (nameAction_isName hπ.1 hσ) ht')
    exact ⟨hq, σ, s, t, hs, (nameAction_pair_mem_iff hπ hσ hν ht).mp ht',
      (hπ.2.2.2 q hq s (forcingName_condition hτ hs)).mpr hqs',
      (hπ.2.2.2 q hq t ht).mpr hqt'⟩
  · rintro ⟨_, σ, s, t, hs, ht, hqs, hqt⟩
    have hσ := forcingName_subname hτ hs
    exact ⟨function_value_mem hπ.1 hq, nameAction π σ, π ‘ s, π ‘ t,
      (nameAction_pair_mem_iff hπ hτ hσ (forcingName_condition hτ hs)).mpr hs,
      (nameAction_pair_mem_iff hπ hσ hν (forcingName_condition hσ ht)).mpr ht,
      (hπ.2.2.2 q hq s (forcingName_condition hτ hs)).mp hqs,
      (hπ.2.2.2 q hq t (forcingName_condition hσ ht)).mp hqt⟩

theorem hereditarilySymmetric_forcingUnionName {P R Γ F τ : V}
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hF : IsNormalSubgroupFilter P Γ F)
    (hτ : IsHereditarilySymmetricName P Γ F τ) :
    IsHereditarilySymmetricName P Γ F (forcingUnionName P R τ) := by
  have hn := forcingUnionName_isName (R := R) hτ.1
  apply (hereditarilySymmetric_iff _ _ _ _).mpr
  refine ⟨⟨hn, ?_⟩, ?_⟩
  · apply hF.2.2.1 _ (hereditarilySymmetric_symmetric hτ).2 _ (nameStabilizer_subgroup hΓ hn)
    intro π hπ
    obtain ⟨hπΓ, hfix⟩ := mem_sep_iff.mp hπ
    refine mem_sep_iff.mpr ⟨hπΓ, ?_⟩
    rw [nameAction_forcingUnionName (hΓ.1 π hπΓ) hτ.1, hfix]
  · intro ν q hq
    obtain ⟨_, σ, s, t, hs, ht, _, _⟩ := (mem_forcingUnionName_iff _ _ _ _ _).mp hq
    have hσ := (hereditarilySymmetric_iff _ _ _ _).mp hτ |>.2 σ s hs
    exact (hereditarilySymmetric_iff _ _ _ _).mp hσ |>.2 ν t ht

end ZFVP
