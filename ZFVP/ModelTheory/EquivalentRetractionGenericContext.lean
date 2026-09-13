import ZFVP.ModelTheory.EquivalentRetractionModel
import ZFVP.ModelTheory.ForcingIsomorphismGenericContext
import ZFVP.SetTheory.ForcingRetractionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext
variable (A : ForcingContext V) {N T n : V}
  (hr : IsForcingRetraction N T A.P A.R n) (hT : IsForcingPreorder N T)
  (hone : A.one ∈ N)

noncomputable def retractionImage : ForcingContext V :=
  ⟨N, T, A.one, forcingProjectionGeneric N T n A.G, hT,
    hr.top_of_mem A.top hone, hr.projection.generic hT A.generic⟩

theorem retractionImage_generic (p : V) :
    p ∈ (A.retractionImage hr hT hone).G ↔ p ∈ A.G ∧ p ∈ N := by
  constructor
  · rintro ⟨hp, q, hq, hqp⟩
    exact ⟨A.generic.1.2.2.1 q hq p (hr.inclusion p hp)
      ((hr.below q (A.generic.1.1 q hq) p hp).mpr hqp), hp⟩
  · rintro ⟨hp, hpN⟩
    exact ⟨hpN, p, hp, by rw [hr.fixes p hpN]; exact hT.2.1 p hpN⟩

variable (he : ∀ p ∈ A.P, ⟨n ‘ p, p⟩ₖ ∈ A.R)

noncomputable def retractionImageEquiv : A.Model ≃ (A.retractionImage hr hT hone).Model :=
  ((A.retractionImage hr hT hone).equivalentRetractionModelEquiv A hr
    (A.retractionImage_generic hr hT hone) he).symm

theorem retractionImageEquiv_mem (x y : A.Model) :
    A.retractionImageEquiv hr hT hone he x ∈ A.retractionImageEquiv hr hT hone he y ↔ x ∈ y := by
  exact ((A.retractionImage hr hT hone).equivalentRetractionModelEquiv_mem_iff A hr
    (A.retractionImage_generic hr hT hone) he _ _).symm.trans (by simp [retractionImageEquiv])

theorem retractionImageEquiv_check (x : V) :
    A.retractionImageEquiv hr hT hone he (A.check x) = (A.retractionImage hr hT hone).check x := by
  apply ((A.retractionImage hr hT hone).equivalentRetractionModelEquiv A hr
    (A.retractionImage_generic hr hT hone) he).injective
  simp only [retractionImageEquiv, Equiv.apply_symm_apply]
  exact ((A.retractionImage hr hT hone).equivalentRetractionModelEquiv_check A hr
    (A.retractionImage_generic hr hT hone) he rfl x).symm

theorem retractionImageEquiv_name (τ : ForcingName A.P) :
    A.retractionImageEquiv hr hT hone he (A.ofName τ) =
      (A.retractionImage hr hT hone).ofName
        ⟨nameAction n τ.val, nameAction_isName hr.maps τ.property⟩ := by
  apply ((A.retractionImage hr hT hone).equivalentRetractionModelEquiv A hr
    (A.retractionImage_generic hr hT hone) he).injective
  simp only [retractionImageEquiv, Equiv.apply_symm_apply]
  rw [(A.retractionImage hr hT hone).equivalentRetractionModelEquiv_name A hr
    (A.retractionImage_generic hr hT hone) he]
  apply (forcingQuotientMk_eq_iff A.P A.R A.G A.order A.generic.1 _ _).mpr
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  refine ⟨p, hp, ?_⟩
  apply nameAction_forced_equal_of_equivalent_conditions A.order
    (mem_function_of_mem_function_of_subset hr.maps hr.inclusion) ?_ τ.property p (A.generic.1.1 p hp)
  intro q hq
  have hqn := function_value_mem hr.maps hq
  exact ⟨he q hq, (hr.below q hq _ hqn).mpr (hT.2.1 _ hqn)⟩

variable {Q S f : V} (hf : IsForcingIsomorphism N T Q S f) (hS : IsForcingPreorder Q S)

noncomputable def retractionIsomorphismImage : ForcingContext V :=
  (A.retractionImage hr hT hone).isomorphismImage hf hS

noncomputable def retractionIsomorphismImageEquiv :
    A.Model ≃ (A.retractionIsomorphismImage hr hT hone hf hS).Model :=
  (A.retractionImageEquiv hr hT hone he).trans
    ((A.retractionImage hr hT hone).isomorphismImageEquiv hf hS)

theorem retractionIsomorphismImageEquiv_mem (x y : A.Model) :
    A.retractionIsomorphismImageEquiv hr hT hone he hf hS x ∈
      A.retractionIsomorphismImageEquiv hr hT hone he hf hS y ↔ x ∈ y :=
  ((A.retractionImage hr hT hone).isomorphismImageEquiv_mem hf hS _ _).trans
    (A.retractionImageEquiv_mem hr hT hone he x y)

theorem retractionIsomorphismImageEquiv_check (x : V) :
    A.retractionIsomorphismImageEquiv hr hT hone he hf hS (A.check x) =
      (A.retractionIsomorphismImage hr hT hone hf hS).check x := by
  change (A.retractionImage hr hT hone).isomorphismImageEquiv hf hS
    (A.retractionImageEquiv hr hT hone he (A.check x)) = _
  rw [retractionImageEquiv_check]
  exact (A.retractionImage hr hT hone).isomorphismImageEquiv_check hf hS x

theorem retractionIsomorphismImageEquiv_name (τ : ForcingName A.P) :
    A.retractionIsomorphismImageEquiv hr hT hone he hf hS (A.ofName τ) =
      (A.retractionIsomorphismImage hr hT hone hf hS).ofName
        ⟨nameAction (compose n f) τ.val, nameAction_isName (compose_function hr.maps hf.1) τ.property⟩ := by
  change (A.retractionImage hr hT hone).isomorphismImageEquiv hf hS
    (A.retractionImageEquiv hr hT hone he (A.ofName τ)) = _
  rw [retractionImageEquiv_name]
  rw [(A.retractionImage hr hT hone).isomorphismImageEquiv_name hf hS]
  congr 1
  exact Subtype.ext (nameAction_compose hr.maps hf.1 τ.property)

end ForcingContext
end ZFVP


