import ZFVP.ModelTheory.SigmaOneMembershipEmbedding
import ZFVP.ModelTheory.SupportStageEmbeddingAction

/-! A bounded formula for the coded membership embedding predicate, with a stage argument.

`IsCodedMembershipEmbedding A B f` is Pi-one through `piOneMembershipEmbeddingFormula` and
Sigma-one through `sigmaOneMembershipEmbeddingFormula`. The Sigma-one form quantifies over a
sequence support `U`, the membership formula family `F` and two complete truth tables `T`, `S`.
Once a set `W` is handed to the formula as a fourth argument and `W` itself is used as the
support, all four quantifiers become bounded by `W`, so the predicate can sit under a bounded
quantifier inside a Pi-one class formula without raising its level.

The side conditions the formula puts on `W` are: `W` is a sequence support (transitive, holds
`ω`, closed under Kuratowski pairs, doubletons, successors and binary unions), `A ∈ W`, `B ∈ W`,
the membership formula family and its identity graph are members of `W`, and complete membership
truth tables for `A` and for `B` are members of `W`.

At `W = hierarchy θ` for an ordinal `θ` with `ω ∈ θ` that is closed under successors these hold:
`hierarchy_isSequenceSupport` gives the support conditions, `identity_mem_hierarchy_limit` moves
the identity graph of the family into the stage, and `membershipModelTruthTable_mem_hierarchy_limit`
puts the canonical truth tables of `A` and `B` there. The one condition that does not follow from
`ω ∈ θ` and successor closure alone is that the formula family is a *member* of the stage: closure
of the stage under the syntax constructors only gives `formulaFamily membershipLanguageCode ∅ ⊆
hierarchy θ`, and an infinite subset of a rank stage need not be an element of it. So the family
membership is carried as a hypothesis `hF`, the same way `ZFVP.ModelTheory.SupportStageEmbeddingAction`
and `ZFVP.SetTheory.WoodinWitnessSupportReflection` carry it.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The coded membership embedding predicate with every quantifier bounded by a fourth argument
`W`, meant to be a rank stage holding `A`, `B` and the membership syntax. -/
def boundedMembershipEmbeddingFormula : SetTheorySemisentence 4 :=
  “A B f W. !boundedNonemptyFormula A ∧ !boundedNonemptyFormula B ∧
    !boundedFunctionFormula f A B ∧ !sequenceSupportFormula W ∧ A ∈ W ∧ B ∈ W ∧
      ∃ F ∈ W, !membershipFamilyWitnessFormula W F ∧
        ∃ O ∈ W, !boundedOmegaFormula O ∧
          ∃ T ∈ W, ∃ S ∈ W, !membershipTruthTableFormula W O F A T ∧
            !membershipTruthTableFormula W O F B S ∧
              !boundedEmbeddingTablesFormula W O F A B f T S”

theorem boundedMembershipEmbeddingFormula_bounded :
    IsBoundedSetFormula boundedMembershipEmbeddingFormula :=
  .and (boundedNonemptyFormula_bounded.subst _)
    (.and (boundedNonemptyFormula_bounded.subst _)
      (.and (boundedFunctionFormula_bounded.subst _)
        (.and (sequenceSupportFormula_bounded.subst _)
          (.and (.rel _ _)
            (.and (.rel _ _)
              (.exs (.bvar 3)
                (.and (membershipFamilyWitnessFormula_bounded.subst _)
                  (.exs (.bvar 4)
                    (.and (boundedOmegaFormula_bounded.subst _)
                      (.exs (.bvar 5)
                        (.exs (.bvar 6)
                          (.and (membershipTruthTableFormula_bounded.subst _)
                            (.and (membershipTruthTableFormula_bounded.subst _)
                              (boundedEmbeddingTablesFormula_bounded.subst _))))))))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The literal reading of `boundedMembershipEmbeddingFormula`. -/
def BoundedMembershipEmbedding (A B f W : V) : Prop :=
  IsNonempty A ∧ IsNonempty B ∧ f ∈ B ^ A ∧ IsSequenceSupport W ∧ A ∈ W ∧ B ∈ W ∧
    (formulaFamily membershipLanguageCode ∅ : V) ∈ W ∧
    SetTheory.identity (formulaFamily membershipLanguageCode ∅ : V) ∈ W ∧
    (∃ T ∈ W, IsMembershipTruthTable A T) ∧ (∃ S ∈ W, IsMembershipTruthTable B S) ∧
      ∀ n φ b, IsMembershipFormulaCode n φ → b ∈ A ^ n →
        (MembershipSatisfies A n φ b ↔ MembershipSatisfies B n φ (compose b f))

private theorem eval_membershipFamilyWitness (W F : V) :
    membershipFamilyWitnessFormula.Evalb ![W, F] ↔
      IsCodingSupport W ∧ F ∈ W ∧ SetTheory.identity F ∈ W ∧
        F = (formulaFamily membershipLanguageCode ∅ : V) := by
  simp [membershipFamilyWitnessFormula, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton]
  intro hU
  let := hU
  intro hQ
  rw [and_iff_right hU.omega_mem]
  apply and_congr_right
  intro hs
  exact eval_membershipFixedPointFormula hQ hs

theorem eval_boundedMembershipEmbeddingFormula_all (A B f W : V) :
    boundedMembershipEmbeddingFormula.Evalb ![A, B, f, W] ↔
      BoundedMembershipEmbedding A B f W := by
  simp [boundedMembershipEmbeddingFormula, BoundedMembershipEmbedding,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    eval_membershipFamilyWitness]
  intro hA hB hf hW hAW hBW hFW
  let := hW
  have hAsub : A ⊆ W := hW.transitive A hAW
  have hBsub : B ⊆ W := hW.transitive B hBW
  constructor
  · rintro ⟨⟨-, -, hiF⟩, -, T, hTW, S, hSW, hT, hS, he⟩
    have hT' := (eval_membershipTruthTableFormula hAsub T).mp hT
    have hS' := (eval_membershipTruthTableFormula hBsub S).mp hS
    exact ⟨hiF, ⟨T, hTW, hT'⟩, ⟨S, hSW, hS'⟩,
      (eval_boundedEmbeddingTablesFormula hAsub hBsub hf hT' hS').mp he⟩
  · rintro ⟨hiF, ⟨T, hTW, hT⟩, ⟨S, hSW, hS⟩, hsat⟩
    exact ⟨⟨hW.toIsCodingSupport, hFW, hiF⟩, hW.omega_mem,
      T, hTW, S, hSW, (eval_membershipTruthTableFormula hAsub T).mpr hT,
      (eval_membershipTruthTableFormula hBsub S).mpr hS,
      (eval_boundedEmbeddingTablesFormula hAsub hBsub hf hT hS).mpr hsat⟩

instance boundedMembershipEmbeddingFormula_defined :
    ℒₛₑₜ-relation₄[V] BoundedMembershipEmbedding via boundedMembershipEmbeddingFormula :=
  ⟨fun (v : Fin 4 → V) ↦ by
    have hv : ![v 0, v 1, v 2, v 3] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
        (fun l ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) l) k) j) i
    change boundedMembershipEmbeddingFormula.Evalb v ↔
      BoundedMembershipEmbedding (v 0) (v 1) (v 2) (v 3)
    rw [← hv]
    exact eval_boundedMembershipEmbeddingFormula_all _ _ _ _⟩

/-- The bounded reading at a successor closed rank stage above `ω` that holds the membership
formula family is exactly the coded embedding predicate. -/
theorem boundedMembershipEmbedding_iff {θ A B f : V} [IsOrdinal θ]
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy θ)
    (hA : A ∈ hierarchy θ) (hB : B ∈ hierarchy θ) (hf : f ∈ hierarchy θ) :
    BoundedMembershipEmbedding A B f (hierarchy θ) ↔ IsCodedMembershipEmbedding A B f := by
  have hωA : (ω : V) ∈ hierarchy θ := ordinal_subset_hierarchy θ _ hω
  rw [codedMembershipEmbedding_iff_valid_satisfaction]
  constructor
  · rintro ⟨hA', hB', hf', -, -, -, -, -, -, -, hsat⟩
    exact ⟨hA', hB', hf', hsat⟩
  · rintro ⟨hA', hB', hf', hsat⟩
    exact ⟨hA', hB', hf', hierarchy_isSequenceSupport hω hsucc, hA, hB, hF,
      identity_mem_hierarchy_limit hsucc hF,
      ⟨membershipModelTruthTable A,
        membershipModelTruthTable_mem_hierarchy_limit hsucc hωA hA hF,
        membershipModelTruthTable_correct A⟩,
      ⟨membershipModelTruthTable B,
        membershipModelTruthTable_mem_hierarchy_limit hsucc hωA hB hF,
        membershipModelTruthTable_correct B⟩, hsat⟩

/-- A transitive set that models ZF holds the membership formula family, so the family
hypothesis of `boundedMembershipEmbedding_iff` is free at a stage that models ZF. -/
theorem formulaFamily_mem_of_transitiveZF (a : V) [IsTransitive a] [Nonempty (SetDomain a)]
    [(SetDomain a)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : (formulaFamily membershipLanguageCode ∅ : V) ∈ a := by
  simpa only [TransitiveZF.membershipFamily_val a] using
    (formulaFamily (membershipLanguageCode : SetDomain a) ∅).property

theorem eval_boundedMembershipEmbeddingFormula {θ A B f : V} [IsOrdinal θ]
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy θ)
    (hA : A ∈ hierarchy θ) (hB : B ∈ hierarchy θ) (hf : f ∈ hierarchy θ) :
    boundedMembershipEmbeddingFormula.Evalb ![A, B, f, hierarchy θ] ↔
      IsCodedMembershipEmbedding A B f :=
  (eval_boundedMembershipEmbeddingFormula_all A B f (hierarchy θ)).trans
    (boundedMembershipEmbedding_iff hω hsucc hF hA hB hf)

/-- The same identification at a stage that models ZF, where the family hypothesis is automatic. -/
theorem eval_boundedMembershipEmbeddingFormula_zf {θ A B f : V} [IsOrdinal θ]
    [Nonempty (SetDomain (hierarchy θ))] [(SetDomain (hierarchy θ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (hA : A ∈ hierarchy θ) (hB : B ∈ hierarchy θ) (hf : f ∈ hierarchy θ) :
    boundedMembershipEmbeddingFormula.Evalb ![A, B, f, hierarchy θ] ↔
      IsCodedMembershipEmbedding A B f :=
  letI := hierarchy_transitive θ
  eval_boundedMembershipEmbeddingFormula hω hsucc
    (formulaFamily_mem_of_transitiveZF (hierarchy θ)) hA hB hf

end ZFVP
