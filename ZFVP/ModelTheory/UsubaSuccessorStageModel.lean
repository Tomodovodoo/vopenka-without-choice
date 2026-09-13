import ZFVP.ModelTheory.UsubaSuccessorRestorationModel
import ZFVP.ModelTheory.UsubaStageDependentChoice
import ZFVP.ModelTheory.TwoStepIntermediatePreservation

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

theorem enumeration_congr [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
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
  simpa only [he] using enumeration hR ht hH hVP hAC hX

theorem dependentChoiceAt_congr [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (A B : ForcingContext V)
    (hA : A = twoStepFirstContext hR ht (usubaSaturated_iterand hR ht) hH)
    (hB : B = twoStepTotalContext hR ht (usubaSaturated_iterand hR ht) hH)
    (k : V) [IsOrdinal k]
    (hbelow : ∀ β ∈ A.check k, InternalDependentChoiceAt β) :
    InternalDependentChoiceAt (B.check k) := by
  subst A B
  exact successor_step_dependentChoiceAt hR ht hH hVP k hbelow
end UsubaSuccessorModel

namespace UsubaSuccessorStage
local notation "T" => usubaForcingTower (V := V)
variable (k : V) [IsOrdinal k] {H : Set V}
  (hH : IsExternalForcingGeneric ((usubaForcingTower (V := V)).P (succ k))
    ((usubaForcingTower (V := V)).R (succ k)) H)
include hH

theorem twoStep_generic : IsExternalForcingGeneric
    (twoStepConditions ((T).P k) ((T).R k) (usubaSaturatedPosetName ((T).P k) ((T).R k)) ∅)
    (twoStepOrder ((T).P k) ((T).R k) (usubaSaturatedPosetName ((T).P k) ((T).R k))
      (reverseInclusionOrderName ((T).P k) ((T).R k)
        (usubaSaturatedPosetName ((T).P k) ((T).R k))) ∅) H := by
  simpa only [usubaTower_P_succ, usubaTower_R_succ] using hH

theorem projected_generic : IsExternalForcingGeneric ((T).P k) ((T).R k)
    (forcingProjectionGeneric ((T).P k) ((T).R k) ((T).projection k (succ k)) H) :=
  ((T).splitProjection (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k))).projection.generic
    ((T).order k inferInstance) hH

theorem projection_filter :
    forcingProjectionGeneric ((T).P k) ((T).R k) ((T).projection k (succ k)) H =
      forcingProjectionGeneric ((T).P k) ((T).R k)
        (twoStepProjection ((T).P k) ((T).R k)
          (usubaSaturatedPosetName ((T).P k) ((T).R k)) ∅) H := by
  have he (q : V) (hq : q ∈ H) :
      ((T).projection k (succ k)) ‘ q =
        (twoStepProjection ((T).P k) ((T).R k)
          (usubaSaturatedPosetName ((T).P k) ((T).R k)) ∅) ‘ q := by
    rw [usubaTower_projection_first (hH.1.1 q hq),
      twoStepProjection_value ((twoStep_generic k hH).1.1 q hq)]
  apply Set.ext
  intro p
  change (p ∈ (T).P k ∧ ∃ q ∈ H, _) ↔ (p ∈ (T).P k ∧ ∃ q ∈ H, _)
  constructor <;> rintro ⟨hp, q, hq, ho⟩
  · exact ⟨hp, q, hq, (he q hq) ▸ ho⟩
  · exact ⟨hp, q, hq, (he q hq).symm ▸ ho⟩

theorem first_context_eq : usubaStageContext k (projected_generic k hH) =
    twoStepFirstContext ((T).order k inferInstance) ((T).top_spec k inferInstance)
      (usubaSaturated_iterand ((T).order k inferInstance) ((T).top_spec k inferInstance))
      (twoStep_generic k hH) := by
  apply ForcingContext.eq_of_data_eq <;> try rfl
  exact projection_filter k hH

theorem total_context_eq : usubaStageContext (succ k) hH =
    twoStepTotalContext ((T).order k inferInstance) ((T).top_spec k inferInstance)
      (usubaSaturated_iterand ((T).order k inferInstance) ((T).top_spec k inferInstance))
      (twoStep_generic k hH) := by
  apply ForcingContext.eq_of_data_eq
  · exact usubaTower_P_succ k
  · exact usubaTower_R_succ k
  · exact usubaTower_top_succ k
  · rfl

theorem dependentChoiceAt [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (hbelow : ∀ β ∈ (usubaStageContext k (projected_generic k hH)).check k,
      InternalDependentChoiceAt β) :
    InternalDependentChoiceAt ((usubaStageContext (succ k) hH).check k) :=
  UsubaSuccessorModel.dependentChoiceAt_congr ((T).order k inferInstance)
    ((T).top_spec k inferInstance) (twoStep_generic k hH) hVP _ _
    (first_context_eq k hH) (total_context_eq k hH) k hbelow

theorem dependentChoiceAt_of_stageDCBelow [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (hbelow : UsubaStageDCBelow k) :
    InternalDependentChoiceAt ((usubaStageContext (succ k) hH).check k) :=
  dependentChoiceAt k hH hVP (usubaStageDCBelow_semantics hbelow (projected_generic k hH))

noncomputable def inclusion :
    MembershipEndExtension (usubaStageContext k (projected_generic k hH)).Model
      (usubaStageContext (succ k) hH).Model :=
  (usubaStageContext k (projected_generic k hH)).projectionInclusion
    (usubaStageContext (succ k) hH)
    ((T).splitProjection (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k))) rfl

theorem enumeration [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (hAC : ¬InternalChoice (usubaStageContext k (projected_generic k hH)).Model)
    {X : (usubaStageContext k (projected_generic k hH)).Model}
    (hX : X ⊆ hierarchy (usubaLeastTarget woodinSeedCardinal)) :
    ∃ γ : (usubaStageContext (succ k) hH).Model,
      IsOrdinal γ ∧ γ ⊆ inclusion k hH woodinSeedCardinal ∧
      InternalDependentChoiceAt γ ∧ ∃ f ∈ (inclusion k hH X) ^ γ, range f = inclusion k hH X := by
  apply UsubaSuccessorModel.enumeration_congr ((T).order k inferInstance)
    ((T).top_spec k inferInstance) (twoStep_generic k hH) hVP _ _
    (first_context_eq k hH) (total_context_eq k hH) (inclusion k hH) _ hAC hX
  intro x
  exact (usubaStageContext k (projected_generic k hH)).projectionInclusion_check _ _ rfl x

end UsubaSuccessorStage
end ZFVP
