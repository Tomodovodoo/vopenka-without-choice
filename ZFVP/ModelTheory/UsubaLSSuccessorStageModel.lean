import ZFVP.ModelTheory.UsubaLSSuccessorRestorationModel
import ZFVP.ModelTheory.UsubaSuccessorStageModel

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace UsubaSuccessorModel
variable {P R one : V} (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
  {H : Set V}
  (hH : IsExternalForcingGeneric
    (twoStepConditions P R (usubaSaturatedPosetName P R) ∅)
    (twoStepOrder P R (usubaSaturatedPosetName P R)
      (reverseInclusionOrderName P R (usubaSaturatedPosetName P R)) ∅) H)

theorem enumeration_congr_of_ls [Countable V]
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (A B : ForcingContext V)
    (hA : A = twoStepFirstContext hR ht (usubaSaturated_iterand hR ht) hH)
    (hB : B = twoStepTotalContext hR ht (usubaSaturated_iterand hR ht) hH)
    (j : MembershipEndExtension A.Model B.Model)
    (hj : ∀ x : V, j (A.check x) = B.check x)
    (hAC : ¬InternalChoice A.Model)
    {X : A.Model} (hX : X ⊆ hierarchy (usubaLeastTarget woodinSeedCardinal)) :
    ∃ γ : B.Model, IsOrdinal γ ∧ γ ⊆ j (woodinSeedCardinal : A.Model) ∧
      InternalDependentChoiceAt γ ∧ ∃ f ∈ (j X) ^ γ, range f = j X := by
  subst A B
  have he (x : (twoStepFirstContext hR ht (usubaSaturated_iterand hR ht) hH).Model) :
      twoStepIntermediateEmbedding hR ht (usubaSaturated_iterand hR ht) hH x = j x := by
    apply (twoStepFirstContext hR ht (usubaSaturated_iterand hR ht) hH).endExtension_ext
    intro a
    rw [twoStepIntermediateEmbedding_check, hj]
  simpa only [he] using enumeration_of_ls hR ht hH hLS hAC hX

theorem dependentChoiceAt_congr_of_ls [Countable V]
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (A B : ForcingContext V)
    (hA : A = twoStepFirstContext hR ht (usubaSaturated_iterand hR ht) hH)
    (hB : B = twoStepTotalContext hR ht (usubaSaturated_iterand hR ht) hH)
    (k : V) [IsOrdinal k]
    (hbelow : ∀ β ∈ A.check k, InternalDependentChoiceAt β) :
    InternalDependentChoiceAt (B.check k) := by
  subst A B
  exact successor_step_dependentChoiceAt_of_ls hR ht hH hLS k hbelow
end UsubaSuccessorModel

namespace UsubaSuccessorStage
local notation "T" => usubaForcingTower (V := V)
variable (k : V) [IsOrdinal k] {H : Set V}
  (hH : IsExternalForcingGeneric ((usubaForcingTower (V := V)).P (succ k))
    ((usubaForcingTower (V := V)).R (succ k)) H)
include hH

theorem dependentChoiceAt_of_ls [Countable V]
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (hbelow : ∀ β ∈ (usubaStageContext k (projected_generic k hH)).check k,
      InternalDependentChoiceAt β) :
    InternalDependentChoiceAt ((usubaStageContext (succ k) hH).check k) :=
  UsubaSuccessorModel.dependentChoiceAt_congr_of_ls ((T).order k inferInstance)
    ((T).top_spec k inferInstance) (twoStep_generic k hH) hLS _ _
    (first_context_eq k hH) (total_context_eq k hH) k hbelow

theorem dependentChoiceAt_of_stageDCBelow_of_ls [Countable V]
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (hbelow : UsubaStageDCBelow k) :
    InternalDependentChoiceAt ((usubaStageContext (succ k) hH).check k) :=
  dependentChoiceAt_of_ls k hH hLS (usubaStageDCBelow_semantics hbelow (projected_generic k hH))

theorem enumeration_of_ls [Countable V]
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (hAC : ¬InternalChoice (usubaStageContext k (projected_generic k hH)).Model)
    {X : (usubaStageContext k (projected_generic k hH)).Model}
    (hX : X ⊆ hierarchy (usubaLeastTarget woodinSeedCardinal)) :
    ∃ γ : (usubaStageContext (succ k) hH).Model,
      IsOrdinal γ ∧ γ ⊆ inclusion k hH woodinSeedCardinal ∧
      InternalDependentChoiceAt γ ∧ ∃ f ∈ (inclusion k hH X) ^ γ, range f = inclusion k hH X := by
  apply UsubaSuccessorModel.enumeration_congr_of_ls ((T).order k inferInstance)
    ((T).top_spec k inferInstance) (twoStep_generic k hH) hLS _ _
    (first_context_eq k hH) (total_context_eq k hH) (inclusion k hH) _ hAC hX
  intro x
  exact (usubaStageContext k (projected_generic k hH)).projectionInclusion_check _ _ rfl x

end UsubaSuccessorStage
end ZFVP
