import ZFVP.ModelTheory.ForcingRetractionModel
import ZFVP.SetTheory.NameActionEquivalentConditions
import ZFVP.SetTheory.MembershipIso

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext
variable (A B : ForcingContext V) {r : V} (hr : IsForcingRetraction A.P A.R B.P B.R r)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)
  (he : ∀ p ∈ B.P, ⟨r ‘ p, p⟩ₖ ∈ B.R)

include he

theorem retractionInclusion_surjective_of_equivalent :
    Function.Surjective (A.retractionInclusion B hr hG) := by
  intro y
  obtain ⟨τ, rfl⟩ := B.ofName_surjective y
  let σ : ForcingName A.P := ⟨nameAction r τ.val, nameAction_isName hr.maps τ.property⟩
  refine ⟨A.ofName σ, ?_⟩
  rw [retractionInclusion_ofName]
  apply (forcingQuotientMk_eq_iff B.P B.R B.G B.order B.generic.1 _ _).mpr
  obtain ⟨p, hp⟩ := B.generic.1.2.1
  refine ⟨p, hp, ?_⟩
  rw [atomicEquality_symm]
  apply nameAction_forced_equal_of_equivalent_conditions B.order
    (mem_function_of_mem_function_of_subset hr.maps hr.inclusion) ?_ τ.property p (B.generic.1.1 p hp)
  intro q hq
  have hqr := function_value_mem hr.maps hq
  exact ⟨he q hq, (hr.below q hq _ hqr).mpr (A.order.2.1 _ hqr)⟩

noncomputable def equivalentRetractionModelEquiv : A.Model ≃ B.Model :=
  Equiv.ofBijective (A.retractionInclusion B hr hG)
    ⟨A.retractionInclusion_injective B hr hG,
      A.retractionInclusion_surjective_of_equivalent B hr hG he⟩

theorem equivalentRetractionModelEquiv_mem_iff (x y : A.Model) :
    A.equivalentRetractionModelEquiv B hr hG he x ∈ A.equivalentRetractionModelEquiv B hr hG he y ↔ x ∈ y :=
  A.retractionInclusion_mem_iff B hr hG x y

theorem equivalentRetractionModelEquiv_check (hone : A.one = B.one) (x : V) :
    A.equivalentRetractionModelEquiv B hr hG he (A.check x) = B.check x :=
  A.retractionInclusion_check B hr hG hone x

theorem equivalentRetractionModelEquiv_name (τ : ForcingName A.P) :
    A.equivalentRetractionModelEquiv B hr hG he (A.ofName τ) =
      B.ofName ⟨τ.val, τ.property.mono hr.inclusion⟩ :=
  A.retractionInclusion_ofName B hr hG τ

noncomputable def equivalentRetractionElementaryMap : ElementaryMap A.Model B.Model :=
  ElementaryMap.ofMembershipIso (A.equivalentRetractionModelEquiv B hr hG he)
    (A.equivalentRetractionModelEquiv_mem_iff B hr hG he)

end ForcingContext
end ZFVP
