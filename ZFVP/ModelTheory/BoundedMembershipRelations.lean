import ZFVP.SetTheory.BoundedFiniteFunctions
import ZFVP.SetTheory.BoundedNameAction
import ZFVP.ModelTheory.MembershipStructure
import ZFVP.Syntax.BoundedStandardTuples

/-! Bounded descriptions of the two relations in the membership structures. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedBinaryTupleTestFormula (equal : Bool) : SetTheorySemisentence 4 :=
  if equal then
    “A s z o. ∃ x ∈ A, ∃ y ∈ A, !boundedPairMemberFormula s z x ∧
      !boundedPairMemberFormula s o y ∧ x = y”
  else
    “A s z o. ∃ x ∈ A, ∃ y ∈ A, !boundedPairMemberFormula s z x ∧
      !boundedPairMemberFormula s o y ∧ x ∈ y”

def boundedBinaryRelationFormula (equal : Bool) : SetTheorySemisentence 5 :=
  “D X A z o. (∀ s ∈ D, s ∈ X ∧ !(boundedBinaryTupleTestFormula equal) A s z o) ∧
    ∀ s ∈ X, !(boundedBinaryTupleTestFormula equal) A s z o → s ∈ D”

def boundedMembershipRelationsFormula : SetTheorySemisentence 3 :=
  “U R A. ∃ z ∈ U, ∃ o ∈ U, ∃ t ∈ U, ∃ X ∈ U, ∃ E ∈ U, ∃ D ∈ U,
    !(boundedNumeralFormula 0) z ∧ !(boundedNumeralFormula 1) o ∧ !(boundedNumeralFormula 2) t ∧
    !boundedFiniteFunctionSetFormula U X A t ∧
    !(boundedBinaryRelationFormula true) E X A z o ∧
    !(boundedBinaryRelationFormula false) D X A z o ∧
    !(boundedStandardTupleFormula 2) U R E D”

theorem boundedBinaryTupleTestFormula_bounded (equal : Bool) :
    IsBoundedSetFormula (boundedBinaryTupleTestFormula equal) := by
  cases equal <;>
    exact .exs (.bvar 0) (.exs (.bvar 1) (.and (boundedPairMemberFormula_bounded.subst _)
      (.and (boundedPairMemberFormula_bounded.subst _) (.rel _ _))))

theorem boundedBinaryRelationFormula_bounded (equal : Bool) :
    IsBoundedSetFormula (boundedBinaryRelationFormula equal) :=
  .and (.all (.bvar 0) (.and (.rel _ _) ((boundedBinaryTupleTestFormula_bounded equal).subst _)))
    (.all (.bvar 1) (.or ((boundedBinaryTupleTestFormula_bounded equal).subst _).neg (.rel _ _)))

theorem boundedMembershipRelationsFormula_bounded : IsBoundedSetFormula boundedMembershipRelationsFormula := by
  repeat' first
    | exact (boundedNumeralFormula_bounded _).subst _
    | exact boundedFiniteFunctionSetFormula_bounded.subst _
    | exact (boundedBinaryRelationFormula_bounded _).subst _
    | exact (boundedStandardTupleFormula_bounded 2).subst _
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def selectedBinaryRelation (equal : Bool) (A : V) : V :=
  if equal then equalityRelation A else membershipTupleRelation A

theorem eval_boundedBinaryTupleTestFormula (equal : Bool) {A s : V} (hs : s ∈ A ^ (2 : V)) :
    (boundedBinaryTupleTestFormula equal).Evalb ![A, s, (0 : V), (1 : V)] ↔
      if equal then s ‘ (0 : V) = s ‘ (1 : V) else s ‘ (0 : V) ∈ s ‘ (1 : V) := by
  let := IsFunction.of_mem hs
  have hz : s ‘ (0 : V) ∈ A := function_value_mem hs (by simp)
  have ho : s ‘ (1 : V) ∈ A := function_value_mem hs (by simp)
  cases equal <;> simp [boundedBinaryTupleTestFormula, kpair_mem_iff_value,
    domain_eq_of_mem_function hs, hz, ho]

theorem eval_boundedBinaryRelationFormula (equal : Bool) (D A : V) :
    (boundedBinaryRelationFormula equal).Evalb ![D, A ^ (2 : V), A, (0 : V), (1 : V)] ↔
      D = selectedBinaryRelation equal A := by
  have he (s : V) : s ∈ selectedBinaryRelation equal A ↔ s ∈ A ^ (2 : V) ∧
      (boundedBinaryTupleTestFormula equal).Evalb ![A, s, (0 : V), (1 : V)] := by
    cases equal <;> simp only [selectedBinaryRelation, Bool.false_eq_true, ↓reduceIte,
      mem_equalityRelation_iff, mem_membershipTupleRelation_iff]
    · exact and_congr_right (fun hs ↦ (eval_boundedBinaryTupleTestFormula false hs).symm)
    · exact and_congr_right (fun hs ↦ (eval_boundedBinaryTupleTestFormula true hs).symm)
  simp only [boundedBinaryRelationFormula]
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  rw [mem_ext_iff]
  simp only [he]
  constructor
  · rintro ⟨hl, hr⟩ s
    exact ⟨fun hs ↦ hl s hs, fun hs ↦ hr s hs.1 hs.2⟩
  · intro h
    exact ⟨fun s hs ↦ (h s).mp hs, fun s hs hp ↦ (h s).mpr ⟨hs, hp⟩⟩

theorem membershipStructure_relations_standardTuple (A : V) :
    structureRelations (membershipStructureCode A) = standardTuple ![equalityRelation A, membershipTupleRelation A] := by
  let : IsFunction (structureRelations (membershipStructureCode A)) := by
    simp only [membershipStructureCode, structureRelations_code]
    infer_instance
  apply functions_eq_of_domain_values
  · simp [membershipStructureCode, domain_definableGraph]
  · intro i hi
    have hi' : i ∈ (2 : V) := by simpa [membershipStructureCode, domain_definableGraph] using hi
    change i ∈ ((2 : ℕ) : V) at hi'
    rw [mem_natCast_iff] at hi'
    obtain ⟨j, rfl⟩ := hi'
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun t ↦ Fin.elim0 t) j) j
    · exact (membershipStructureCode_equality A).trans
        (value_standardTuple ![equalityRelation A, membershipTupleRelation A] 0).symm
    · exact (membershipStructureCode_membership A).trans
        (value_standardTuple ![equalityRelation A, membershipTupleRelation A] 1).symm

theorem eval_boundedMembershipRelationsFormula {U A : V} [hU : IsSequenceSupport U]
    (hA : A ⊆ U) (R : V) :
    boundedMembershipRelationsFormula.Evalb ![U, R, A] ↔
      R = structureRelations (membershipStructureCode A) ∧ A ^ (2 : V) ∈ U ∧
        equalityRelation A ∈ U ∧ membershipTupleRelation A ∈ U := by
  simp only [boundedMembershipRelationsFormula]
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  have hx := eval_boundedFiniteFunctionSetFormula hA (show (2 : V) ∈ (ω : V) by simp)
  simp only [hx]
  have hz : (0 : V) ∈ U := IsCodingSupport.numeral_mem 0
  have ho : (1 : V) ∈ U := IsCodingSupport.numeral_mem 1
  have ht : (2 : V) ∈ U := IsCodingSupport.numeral_mem 2
  simp only [hz, ho, ht, true_and]
  constructor
  · rintro ⟨X, hX, E, hE, D, hD, rfl, he, hd, hr⟩
    have heq : E = equalityRelation A := (eval_boundedBinaryRelationFormula true E A).mp he
    have hdq : D = membershipTupleRelation A := (eval_boundedBinaryRelationFormula false D A).mp hd
    subst E D
    exact ⟨((eval_boundedStandardTupleFormula U R ![equalityRelation A, membershipTupleRelation A]).mp hr).1.trans
      (membershipStructure_relations_standardTuple A).symm, hX, hE, hD⟩
  · rintro ⟨hr, hX, hE, hD⟩
    refine ⟨_, hX, _, hE, _, hD, rfl, (eval_boundedBinaryRelationFormula true _ A).mpr rfl,
      (eval_boundedBinaryRelationFormula false _ A).mpr rfl, ?_⟩
    exact (eval_boundedStandardTupleFormula U R ![equalityRelation A, membershipTupleRelation A]).mpr
      ⟨hr.trans (membershipStructure_relations_standardTuple A), by simpa using And.intro hE hD⟩

end ZFVP
