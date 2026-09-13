import ZFVP.SetTheory.ForcingRetraction
import ZFVP.ModelTheory.ForcingModel

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable (A B : ForcingContext V) {π : V} (hπ : IsForcingRetraction A.P A.R B.P B.R π)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)

include hπ hG

theorem retraction_generic_value {p : V} (hp : p ∈ B.G) : π ‘ p ∈ A.G := by
  have hpB := B.generic.1.1 p hp
  have hπp := function_value_mem hπ.maps hpB
  exact (hG _).mpr ⟨B.generic.1.2.2.1 p hp _ (hπ.inclusion _ hπp)
    ((hπ.below p hpB _ hπp).mpr (A.order.2.1 _ hπp)), hπp⟩

theorem retraction_generic_equality (σ τ : ForcingName A.P) :
    GenericMeets B.G (atomicEquality B.P B.R σ.val τ.val) ↔
      GenericMeets A.G (atomicEquality A.P A.R σ.val τ.val) := by
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨π ‘ p, retraction_generic_value A B hπ hG hp,
      (hπ.atomicEquality_iff σ.property τ.property (B.generic.1.1 p hp)).mp he⟩
  · rintro ⟨p, hp, he⟩
    have hpA := A.generic.1.1 p hp
    exact ⟨p, ((hG p).mp hp).1,
      (hπ.atomicEquality_iff σ.property τ.property (hπ.inclusion p hpA)).mpr
        ((hπ.fixes p hpA).symm ▸ he)⟩

theorem retraction_generic_membership (σ τ : ForcingName A.P) :
    GenericMeets B.G (atomicMembership B.P B.R σ.val τ.val) ↔
      GenericMeets A.G (atomicMembership A.P A.R σ.val τ.val) := by
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨π ‘ p, retraction_generic_value A B hπ hG hp,
      (hπ.atomicMembership_iff σ.property τ.property (B.generic.1.1 p hp)).mp he⟩
  · rintro ⟨p, hp, he⟩
    have hpA := A.generic.1.1 p hp
    exact ⟨p, ((hG p).mp hp).1,
      (hπ.atomicMembership_iff σ.property τ.property (hπ.inclusion p hpA)).mpr
        ((hπ.fixes p hpA).symm ▸ he)⟩

noncomputable def retractionInclusion : A.Model → B.Model :=
  Quotient.lift (fun σ : ForcingName A.P ↦ B.ofName ⟨σ.val, σ.property.mono hπ.inclusion⟩)
    (fun σ τ he ↦ (forcingQuotientMk_eq_iff B.P B.R B.G B.order B.generic.1 _ _).mpr
      ((retraction_generic_equality A B hπ hG σ τ).mpr he))

theorem retractionInclusion_ofName (τ : ForcingName A.P) :
    retractionInclusion A B hπ hG (A.ofName τ) =
      B.ofName ⟨τ.val, τ.property.mono hπ.inclusion⟩ := rfl

set_option maxHeartbeats 800000 in
theorem retractionInclusion_injective : Function.Injective (retractionInclusion A B hπ hG) := by
  intro x y he
  obtain ⟨σ, rfl⟩ := A.ofName_surjective x
  obtain ⟨τ, rfl⟩ := A.ofName_surjective y
  exact (forcingQuotientMk_eq_iff A.P A.R A.G A.order A.generic.1 σ τ).mpr
    ((retraction_generic_equality A B hπ hG σ τ).mp
      ((forcingQuotientMk_eq_iff B.P B.R B.G B.order B.generic.1
        ⟨σ.val, σ.property.mono hπ.inclusion⟩ ⟨τ.val, τ.property.mono hπ.inclusion⟩).mp he))

theorem retractionInclusion_mem_iff (x y : A.Model) :
    retractionInclusion A B hπ hG x ∈ retractionInclusion A B hπ hG y ↔ x ∈ y := by
  obtain ⟨σ, rfl⟩ := A.ofName_surjective x
  obtain ⟨τ, rfl⟩ := A.ofName_surjective y
  exact retraction_generic_membership A B hπ hG σ τ

theorem retractionInclusion_endExtension (x : A.Model) (y : B.Model)
    (hy : y ∈ retractionInclusion A B hπ hG x) :
    ∃ z ∈ x, y = retractionInclusion A B hπ hG z := by
  obtain ⟨τ, rfl⟩ := A.ofName_surjective x
  obtain ⟨ν, p, _, hp, he⟩ := (B.mem_ofName_iff _ y).mp hy
  let νA : ForcingName A.P := ⟨ν.val, forcingName_subname τ.property hp⟩
  have hz : y = retractionInclusion A B hπ hG (A.ofName νA) := he
  refine ⟨A.ofName νA, ?_, hz⟩
  exact (retractionInclusion_mem_iff A B hπ hG _ _).mp (hz ▸ hy)

noncomputable def retractionEmbedding : MembershipEndExtension A.Model B.Model where
  toFun := retractionInclusion A B hπ hG
  injective := retractionInclusion_injective A B hπ hG
  mem_iff := retractionInclusion_mem_iff A B hπ hG
  endExtension := retractionInclusion_endExtension A B hπ hG

theorem retractionInclusion_check (hone : A.one = B.one) (x : V) :
    retractionInclusion A B hπ hG (A.check x) = B.check x := by
  change B.ofName ⟨checkName A.one x, _⟩ = B.ofName ⟨checkName B.one x, _⟩
  congr 1
  exact Subtype.ext (congrArg (fun one ↦ checkName one x) hone)

end ForcingContext
end ZFVP
