import ZFVP.SetTheory.TwoStepForcing
import ZFVP.SetTheory.DeltaOneAtomicForcing
import ZFVP.SetTheory.BoundedRelationDomain
import ZFVP.SetTheory.BoundedUnion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneTwoStepNameSetFormula : SetTheorySemisentence 3 :=
  “N Q t. ∃ D, !boundedRelationDomainFormula D Q ∧
    ∃ T, !boundedSingletonFormula T t ∧ !boundedUnionFormula N D T”

theorem sigmaOneTwoStepNameSetFormula_sigmaOne : IsSigmaFormula 1 sigmaOneTwoStepNameSetFormula :=
  .exs (.and (.bounded (boundedRelationDomainFormula_bounded.subst _))
    (.exs (.bounded (.and (boundedSingletonFormula_bounded.subst _) (boundedUnionFormula_bounded.subst _)))))

def sigmaOneTwoStepConditionSetFormula : SetTheorySemisentence 5 :=
  “C P R Q t. ∃ N, !sigmaOneTwoStepNameSetFormula N Q t ∧
    (∀ z ∈ C, ∃ p ∈ P, ∃ τ ∈ N, !boundedKpairFormula z p τ) ∧
    (∀ p ∈ P, ∀ τ ∈ N,
      (!boundedPairMemberFormula C p τ ∧ !(sigmaOneAtomicMembershipFormula true) P R τ Q p) ∨
      (¬!boundedPairMemberFormula C p τ ∧ !(sigmaOneAtomicMembershipFormula false) P R τ Q p))”

theorem sigmaOneTwoStepConditionSetFormula_sigmaOne : IsSigmaFormula 1 sigmaOneTwoStepConditionSetFormula := by
  unfold sigmaOneTwoStepConditionSetFormula
  repeat' first
    | exact sigmaOneTwoStepNameSetFormula_sigmaOne.subst _
    | exact (sigmaOneAtomicMembershipFormula_sigmaOne true).subst _
    | exact (sigmaOneAtomicMembershipFormula_sigmaOne false).subst _
    | exact IsLevyFormula.bounded (boundedKpairFormula_bounded.subst _)
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _)
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _).neg
    | apply IsLevyFormula.boundedAll
    | apply IsLevyFormula.boundedExs
    | apply IsLevyFormula.exs
    | apply IsLevyFormula.and
    | apply IsLevyFormula.or

def piOneTwoStepConditionSetFormula : SetTheorySemisentence 5 :=
  “C P R Q t. ∀ D, !sigmaOneTwoStepConditionSetFormula D P R Q t → C = D”

theorem piOneTwoStepConditionSetFormula_piOne : IsPiFormula 1 piOneTwoStepConditionSetFormula :=
  .all (.or (sigmaOneTwoStepConditionSetFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneTwoStepNameSetFormula_defined : ℒₛₑₜ-function₂[V] twoStepNames via sigmaOneTwoStepNameSetFormula :=
  ⟨fun v ↦ by simp [sigmaOneTwoStepNameSetFormula, twoStepNames]⟩

instance sigmaOneTwoStepConditionSetFormula_defined :
    ℒₛₑₜ-function₄[V] twoStepConditions via sigmaOneTwoStepConditionSetFormula := by
  refine ⟨fun v ↦ ?_⟩
  change sigmaOneTwoStepConditionSetFormula.Evalb v ↔
    v 0 = twoStepConditions (v 1) (v 2) (v 3) (v 4)
  simp [sigmaOneTwoStepConditionSetFormula, TruthAnswer]
  constructor
  · rintro ⟨hs, ht⟩
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨p, hp, τ, hτ, rfl⟩ := hs z hz
      exact (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr
        ⟨hp, hτ, (ht p hp τ hτ).resolve_right (fun h ↦ h.1 hz) |>.2⟩
    · intro hz
      obtain ⟨p, hp, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp hz
      exact ((ht p hp τ hτ).resolve_right (fun h ↦ h.2 hm)).1
  · intro h
    rw [h]
    constructor
    · intro z hz
      obtain ⟨p, hp, τ, hτ, he, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hz
      exact ⟨p, hp, τ, hτ, he⟩
    · intro p hp τ hτ
      classical
      by_cases hm : p ∈ atomicMembership (v 1) (v 2) τ (v 3)
      · exact Or.inl ⟨(kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hp, hτ, hm⟩, hm⟩
      · exact Or.inr ⟨fun hc ↦ hm ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp hc).2.2, hm⟩

instance piOneTwoStepConditionSetFormula_defined :
    ℒₛₑₜ-function₄[V] twoStepConditions via piOneTwoStepConditionSetFormula :=
  ⟨fun v ↦ by simp [piOneTwoStepConditionSetFormula]⟩

end ZFVP
