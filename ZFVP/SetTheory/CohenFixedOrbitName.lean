import ZFVP.SetTheory.CohenLocalSupport

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Join all translates of a name by row permutations fixing `C`. -/
noncomputable def cohenFixedOrbitName (C N : V) : V :=
  ⋃ˢ repl (fun π ↦ nameAction (cohenPermutation (ω : V) π) N) (by definability)
    {π ∈ internalPermutations (ω : V) ; ∀ i ∈ C, π ‘ i = i}

theorem mem_cohenFixedOrbitName {C N : V}
    (hN : IsForcingName (cohenConditions (ω : V)) N) (z : V) :
    z ∈ cohenFixedOrbitName C N ↔
      ∃ π, IsInternalPermutation (ω : V) π ∧ (∀ i ∈ C, π ‘ i = i) ∧
        ∃ μ s, ⟨μ, s⟩ₖ ∈ N ∧
          z = ⟨nameAction (cohenPermutation (ω : V) π) μ,
            (cohenPermutation (ω : V) π) ‘ s⟩ₖ := by
  simp only [cohenFixedOrbitName, mem_sUnion_iff, repl_spec, mem_sep_iff,
    mem_internalPermutations]
  constructor
  · rintro ⟨M, ⟨π, ⟨hπ, hfix⟩, rfl⟩, hz⟩
    obtain ⟨μ, s, hs, he⟩ := (mem_nameAction_iff hN _ z).mp hz
    exact ⟨π, hπ, hfix, μ, s, hs, he⟩
  · rintro ⟨π, hπ, hfix, μ, s, hs, he⟩
    exact ⟨_, ⟨π, ⟨hπ, hfix⟩, rfl⟩, (mem_nameAction_iff hN _ z).mpr ⟨μ, s, hs, he⟩⟩

theorem cohenFixedOrbitName_isName {C N : V}
    (hN : IsForcingName (cohenConditions (ω : V)) N) :
    IsForcingName (cohenConditions (ω : V)) (cohenFixedOrbitName C N) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨π, hπ, _, μ, s, hs, rfl⟩ := (mem_cohenFixedOrbitName hN z).mp hz
  have ha := cohenPermutation_automorphism hπ
  exact ⟨_, _, function_value_mem ha.1 (forcingName_condition hN hs), rfl,
    nameAction_isName ha.1 (forcingName_subname hN hs)⟩

theorem cohenFixedOrbitName_pair_closed {C N π μ q : V}
    (hCω : C ⊆ (ω : V)) (hN : IsForcingName (cohenConditions (ω : V)) N)
    (hπ : IsInternalPermutation (ω : V) π) (hfix : ∀ i ∈ C, π ‘ i = i)
    (hm : ⟨μ, q⟩ₖ ∈ cohenFixedOrbitName C N) :
    ⟨nameAction (cohenPermutation (ω : V) π) μ, (cohenPermutation (ω : V) π) ‘ q⟩ₖ ∈
      cohenFixedOrbitName C N := by
  obtain ⟨ρ, hρ, hρfix, ν, s, hs, he⟩ := (mem_cohenFixedOrbitName hN _).mp hm
  obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
  apply (mem_cohenFixedOrbitName hN _).mpr
  refine ⟨compose ρ π, hρ.comp hπ, ?_, ν, s, hs, ?_⟩
  · intro i hi
    rw [value_compose_of_mem_function hρ.1 hπ.1 (hCω i hi), hρfix i hi, hfix i hi]
  · rw [cohenPermutation_compose hρ hπ,
      nameAction_compose (cohenPermutation_automorphism hρ).1
        (cohenPermutation_automorphism hπ).1 (forcingName_subname hN hs),
      value_compose_of_mem_function (cohenPermutation_automorphism hρ).1
        (cohenPermutation_automorphism hπ).1 (forcingName_condition hN hs)]

theorem cohenFixedOrbitName_fixed {C N π : V}
    (hCω : C ⊆ (ω : V)) (hN : IsForcingName (cohenConditions (ω : V)) N)
    (hπ : IsInternalPermutation (ω : V) π) (hfix : ∀ i ∈ C, π ‘ i = i) :
    nameAction (cohenPermutation (ω : V) π) (cohenFixedOrbitName C N) = cohenFixedOrbitName C N := by
  have ha := cohenPermutation_automorphism hπ
  apply nameAction_eq_of_pair_iff ha (cohenFixedOrbitName_isName hN) (cohenFixedOrbitName_isName hN)
  intro μ hμ q hq
  constructor
  · intro hm
    have hinvfix : ∀ i ∈ C, (converseGraph π) ‘ i = i := by
      intro i hi
      have hh := hπ.inv_value (hCω i hi)
      rwa [hfix i hi] at hh
    have hh := cohenFixedOrbitName_pair_closed hCω hN hπ.inv hinvfix hm
    rwa [cohenPermutation_inverse hπ, nameAction_inverse_cancel ha hμ,
      converseGraph_value_value ha.1 ha.2.1 hq] at hh
  · exact cohenFixedOrbitName_pair_closed hCω hN hπ hfix

theorem cohenFixedOrbitName_hereditarilySymmetric {C N : V}
    (hCω : C ⊆ (ω : V)) (hCf : IsInternallyFinite C)
    (hN : IsForcingName (cohenConditions (ω : V)) N)
    (hsub : ∀ μ q, ⟨μ, q⟩ₖ ∈ N → IsHereditarilySymmetricName
      (cohenConditions (ω : V)) (cohenGroup (ω : V)) (cohenFilter (ω : V)) μ) :
    IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) (cohenFixedOrbitName C N) := by
  apply cohenName_hereditarilySymmetric_of_support (cohenFixedOrbitName_isName hN)
    ⟨hCω, hCf, fun π hπ hfix ↦ cohenFixedOrbitName_fixed hCω hN hπ hfix⟩
  intro μ q hm
  obtain ⟨π, hπ, _, ν, s, hs, he⟩ := (mem_cohenFixedOrbitName hN _).mp hm
  rw [(kpair_iff.mp he).1]
  exact hereditarilySymmetric_nameAction (cohenGroup_group (ω : V)) (cohenFilter_normal (ω : V))
    ((mem_cohenGroup (ω : V) _).mpr ⟨π, hπ, rfl⟩) (hsub ν s hs)

end ZFVP
