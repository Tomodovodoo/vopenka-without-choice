import ZFVP.ModelTheory.NormalizedTwoStepPrefix
import ZFVP.ModelTheory.NormalizedTwoStepExtension
import ZFVP.ModelTheory.ForcingProjectionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R one δ Q S : V} [IsOrdinal δ]

local notation "Cₛ" => boundedNameTwoStep P R δ Q
local notation "Cₙ" => normalizedNameTwoStep P R one δ Q
local notation "Rₛ" => nameTwoStepOrderOn P R S Cₛ
local notation "Rₙ" => nameTwoStepOrderOn P R S Cₙ

theorem normalizedTwoStepRetraction_prefix_comp
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅) :
    compose (normalizedTwoStepRetraction P R one δ Q) (nameTwoStepPrefix Cₙ) =
      nameTwoStepPrefix Cₛ := by
  have hr := normalizedTwoStepRetraction_spec hR ht hδ hP hI
  have hn := normalizedNameTwoStep_prefix_projection hR ht hI (δ := δ)
  have hs := boundedNameTwoStep_prefix_projection hR ht hI (δ := δ)
  apply function_eq_of_values (compose_function hr.maps hn.maps) hs.maps
  intro z hz
  rw [value_compose_of_mem_function hr.maps hn.maps hz,
    nameTwoStepPrefix_value (function_value_mem hr.maps hz), nameTwoStepPrefix_value hz]
  exact normalizedTwoStepRetraction_prefix hz

/-- The specified retraction commutes with every map out of the preceding stage. -/
theorem normalizedTwoStepRetraction_earlier_comp {A π : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅)
    (hπ : π ∈ A ^ P) :
    compose (normalizedTwoStepRetraction P R one δ Q) (compose (nameTwoStepPrefix Cₙ) π) =
      compose (nameTwoStepPrefix Cₛ) π := by
  have hr := normalizedTwoStepRetraction_spec hR ht hδ hP hI
  have hn := normalizedNameTwoStep_prefix_projection hR ht hI (δ := δ)
  have hs := boundedNameTwoStep_prefix_projection hR ht hI (δ := δ)
  apply function_eq_of_values (compose_function hr.maps (compose_function hn.maps hπ))
    (compose_function hs.maps hπ)
  intro z hz
  rw [value_compose_of_mem_function hr.maps (compose_function hn.maps hπ) hz,
    value_compose_of_mem_function hn.maps hπ (function_value_mem hr.maps hz),
    value_compose_of_mem_function hs.maps hπ hz,
    nameTwoStepPrefix_value (function_value_mem hr.maps hz), nameTwoStepPrefix_value hz,
    normalizedTwoStepRetraction_prefix hz]

theorem normalizedTwoStepRetraction_earlier_nameAction {A π τ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅)
    (hπ : π ∈ A ^ P) (hτ : IsForcingName Cₛ τ) :
    nameAction (compose (nameTwoStepPrefix Cₙ) π)
      (nameAction (normalizedTwoStepRetraction P R one δ Q) τ) =
        nameAction (compose (nameTwoStepPrefix Cₛ) π) τ := by
  rw [nameAction_compose (normalizedTwoStepRetraction_spec hR ht hδ hP hI).maps
    (compose_function (normalizedNameTwoStep_prefix_projection hR ht hI).maps hπ) hτ,
    normalizedTwoStepRetraction_earlier_comp hR ht hδ hP hI hπ]

theorem normalizedTwoStep_earlierGeneric_eq {A T π : V} {G : Set V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅)
    (hπ : π ∈ A ^ P) (hG : IsExternalForcingFilter Cₛ Rₛ G) :
    forcingProjectionGeneric A T (compose (nameTwoStepPrefix Cₛ) π) G =
      forcingProjectionGeneric A T (compose (nameTwoStepPrefix Cₙ) π)
        {z | z ∈ G ∧ z ∈ Cₙ} := by
  have hn := normalizedNameTwoStep_prefix_projection hR ht hI (δ := δ)
  have hs := boundedNameTwoStep_prefix_projection hR ht hI (δ := δ)
  apply Set.ext
  intro p
  constructor
  · rintro ⟨hp, z, hzG, hzp⟩
    have hz := hG.1 z hzG
    have hzN := (guardedTwoStepCode_generic_iff hR ht hδ hP hI hG hz).mpr hzG
    refine ⟨hp, guardedTwoStepCode P R one z, hzN, ?_⟩
    rw [value_compose_of_mem_function hn.maps hπ hzN.2,
      nameTwoStepPrefix_value hzN.2, guardedTwoStepCode_prefix]
    rwa [value_compose_of_mem_function hs.maps hπ hz, nameTwoStepPrefix_value hz] at hzp
  · rintro ⟨hp, z, hz, hzp⟩
    refine ⟨hp, z, hz.1, ?_⟩
    rw [value_compose_of_mem_function hs.maps hπ (hG.1 z hz.1),
      nameTwoStepPrefix_value (hG.1 z hz.1)]
    rwa [value_compose_of_mem_function hn.maps hπ hz.2, nameTwoStepPrefix_value hz.2] at hzp

end ZFVP
