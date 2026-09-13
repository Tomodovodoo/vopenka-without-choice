import ZFVP.ModelTheory.ForcingIsomorphismGenericContext
import ZFVP.ModelTheory.ForcingProjectionComposition
import ZFVP.SetTheory.ForcingAutomorphisms

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The conditions whose image under a member of the specified ground family
extends the target condition. -/
noncomputable def forcingAutomorphismOrbit (P R A t : V) : V :=
  {p ∈ P ; ∃ f ∈ A, ⟨f ‘ p, t⟩ₖ ∈ R}

instance forcingAutomorphismOrbit_definable : ℒₛₑₜ-function₄[V] forcingAutomorphismOrbit := by
  have h : ℒₛₑₜ-relation₅[V] (fun D P R A t ↦ ∀ p, p ∈ D ↔
    p ∈ P ∧ ∃ f ∈ A, ⟨f ‘ p, t⟩ₖ ∈ R) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [forcingAutomorphismOrbit, mem_sep_iff]
  rfl

theorem forcingAutomorphismOrbit_denseBelow {P R A t a : V}
    (hA : ∀ f ∈ A, IsForcingAutomorphism P R f)
    (hmove : ∀ p ∈ P, ⟨p, a⟩ₖ ∈ R →
      ∃ f ∈ A, ForcingCompatible P R (f ‘ p) t) :
    ForcingDenseBelow P R (forcingAutomorphismOrbit P R A t) a := by
  refine ⟨sep_subset, ?_⟩
  intro p hp hpa
  obtain ⟨f, hfA, r, hr, hrp, hrt⟩ := hmove p hp hpa
  have hf : IsForcingIsomorphism P R P R f := hA f hfA
  have hs := function_value_mem hf.inverse_maps hr
  refine ⟨(converseGraph f) ‘ r, mem_sep_iff.mpr ⟨hs, f, hfA, ?_⟩, ?_⟩
  · rwa [hf.value_inverse hr]
  · apply (hf.2.2.2 _ hs p hp).mpr
    rwa [hf.value_inverse hr]

/-- Relative generic adjustment follows from the ground automorphism common-
extension property below a condition already in the generic. -/
theorem externalGeneric_move_automorphism {P R A t a : V} {G : Set V}
    (hR : IsForcingPreorder P R) (hG : IsExternalForcingGeneric P R G)
    (ht : t ∈ P) (ha : a ∈ G)
    (hA : ∀ f ∈ A, IsForcingAutomorphism P R f)
    (hmove : ∀ p ∈ P, ⟨p, a⟩ₖ ∈ R →
      ∃ f ∈ A, ForcingCompatible P R (f ‘ p) t) :
    ∃ f ∈ A, IsExternalForcingGeneric P R (forcingProjectionGeneric P R f G) ∧
      t ∈ forcingProjectionGeneric P R f G := by
  obtain ⟨p, hpG, hpD⟩ := externalForcingGeneric_meets_denseBelow hR hG ha
    (forcingAutomorphismOrbit_denseBelow hA hmove)
  obtain ⟨_, f, hfA, hft⟩ := mem_sep_iff.mp hpD
  have hf : IsForcingIsomorphism P R P R f := hA f hfA
  exact ⟨f, hfA, hf.projection.generic hR hG, ht, p, hpG, hft⟩

/-- Commuting with the ground projection preserves the projected generic. -/
theorem forcingProjectionGeneric_automorphism_fixed {P R Q S π f : V} {G : Set V}
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (hπ : IsForcingProjection Q S P R π) (hf : IsForcingAutomorphism P R f)
    (hG : IsExternalForcingFilter P R G)
    (hfix : ∀ p ∈ P, π ‘ (f ‘ p) = π ‘ p) :
    forcingProjectionGeneric Q S π (forcingProjectionGeneric P R f G) =
      forcingProjectionGeneric Q S π G := by
  have hf' : IsForcingIsomorphism P R P R f := hf
  rw [forcingProjectionGeneric_comp hπ hf'.projection hS hR hG]
  have he : compose f π = π := by
    let := IsFunction.of_mem (compose_function hf.1 hπ.maps)
    let := IsFunction.of_mem hπ.maps
    apply functions_eq_of_domain_values
    · rw [domain_eq_of_mem_function (compose_function hf.1 hπ.maps),
        domain_eq_of_mem_function hπ.maps]
    · intro p hp
      rw [domain_eq_of_mem_function (compose_function hf.1 hπ.maps)] at hp
      rw [value_compose_of_mem_function hf.1 hπ.maps hp, hfix p hp]
  rw [he]

noncomputable def projectionFixingAutomorphisms (P R π : V) : V :=
  {f ∈ forcingAutomorphisms P R ; ∀ p ∈ P, π ‘ (f ‘ p) = π ‘ p}

instance projectionFixingAutomorphisms_definable :
    ℒₛₑₜ-function₃[V] projectionFixingAutomorphisms := by
  have h : ℒₛₑₜ-relation₄[V] (fun A P R π ↦ ∀ f, f ∈ A ↔
    f ∈ forcingAutomorphisms P R ∧ ∀ p ∈ P, π ‘ (f ‘ p) = π ‘ p) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [projectionFixingAutomorphisms, mem_sep_iff]
  rfl

/-- The exact generic-adjustment consequence of relative homogeneity. The
homogeneity premise concerns ground conditions and ground automorphisms only. -/
theorem externalGeneric_relative_movement_of_homogeneity
    {P R Q S π E t : V} {G : Set V}
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (hsplit : IsForcingSplitProjection Q S P R π E)
    (hG : IsExternalForcingGeneric P R G) (ht : t ∈ P)
    (htG : π ‘ t ∈ forcingProjectionGeneric Q S π G)
    (hhom : ∀ p ∈ P, ⟨π ‘ p, π ‘ t⟩ₖ ∈ S →
      ∃ f, IsForcingAutomorphism P R f ∧
        (∀ q ∈ P, π ‘ (f ‘ q) = π ‘ q) ∧ ForcingCompatible P R (f ‘ p) t) :
    ∃ f, IsForcingAutomorphism P R f ∧
      IsExternalForcingGeneric P R (forcingProjectionGeneric P R f G) ∧
      t ∈ forcingProjectionGeneric P R f G ∧
      forcingProjectionGeneric Q S π (forcingProjectionGeneric P R f G) =
        forcingProjectionGeneric Q S π G ∧
      forcingProjectionGeneric P R (converseGraph f) (forcingProjectionGeneric P R f G) = G := by
  have htQ := function_value_mem hsplit.projection.maps ht
  have ha : E ‘ (π ‘ t) ∈ G := (hsplit.generic_iff_section hS hG.1 htQ).mp htG
  have hA : ∀ f ∈ projectionFixingAutomorphisms P R π, IsForcingAutomorphism P R f :=
    fun f hf ↦ (mem_forcingAutomorphisms_iff P R f).mp (mem_sep_iff.mp hf).1
  have hm : ∀ p ∈ P, ⟨p, E ‘ (π ‘ t)⟩ₖ ∈ R →
      ∃ f ∈ projectionFixingAutomorphisms P R π, ForcingCompatible P R (f ‘ p) t := by
    intro p hp hpa
    obtain ⟨f, hf, hfix, hcompat⟩ := hhom p hp ((hsplit.below p hp _ htQ).mp hpa)
    exact ⟨f, mem_sep_iff.mpr ⟨(mem_forcingAutomorphisms_iff P R f).mpr hf, hfix⟩, hcompat⟩
  obtain ⟨f, hfA, hfG, htfG⟩ := externalGeneric_move_automorphism hR hG ht ha hA hm
  have hf : IsForcingIsomorphism P R P R f := hA f hfA
  exact ⟨f, hf, hfG, htfG,
    forcingProjectionGeneric_automorphism_fixed hR hS hsplit.projection hf hG.1 (mem_sep_iff.mp hfA).2,
    hf.generic_inverse_image hG.1 hR hR⟩

end ZFVP
