import ZFVP.ModelTheory.ForcingSmallDCFailure
import ZFVP.ModelTheory.ForcingSmallInaccessible
import ZFVP.ModelTheory.WoodinRankDependentChoiceAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.eventually_rank_dependentChoice_iff (A : ForcingContext V)
    {δ γ : V} (hδ : IsWoodinSupercompact δ) (hP : A.P ∈ hierarchy δ) (hγ : γ ∈ δ) :
    ∃ η ∈ δ, γ ∈ η ∧ ∀ ξ : A.Model, A.check η ∈ ξ →
      ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ κ : SetDomain (hierarchy ξ), κ.val ∈ A.check γ →
        (InternalDependentChoiceAt κ ↔ InternalDependentChoiceAt κ.val) := by
  let := hδ.1.1
  have hi := A.check_inaccessible_of_small hδ.inaccessible hP
  have hsmall : ∀ κ ∈ A.check γ, ¬InternalDependentChoiceAt κ →
      ∃ B ∈ hierarchy (A.check δ), IsRankFunctionClosed (succ κ) B ∧ hierarchy (succ κ) ∈ B ∧
        κ ∈ B ∧ IsTransitive B ∧ IsFunctionRestrictionClosed B ∧
        IsBoundedDependentChoiceFailure κ B := by
    intro κ hκ hf
    obtain ⟨k, hk, rfl⟩ := (A.mem_check_iff γ κ).mp hκ
    exact A.small_dependentChoice_failure_certificate hδ hP
      (IsOrdinal.toIsTransitive.mem_trans hk hγ) hf
  obtain ⟨η, hη, hγη, hall⟩ := hi.eventually_rank_dependentChoice_iff
    ((A.check_mem_iff _ _).mpr hγ) hsmall
  obtain ⟨b, hb, rfl⟩ := (A.mem_check_iff δ η).mp hη
  exact ⟨b, hb, (A.check_mem_iff _ _).mp hγη, hall⟩

end ZFVP
