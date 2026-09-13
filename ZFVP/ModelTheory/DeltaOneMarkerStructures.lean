import ZFVP.ModelTheory.BoundedMarkerFunctions

/-! Sigma-one and Pi-one graphs for the concrete marker structures. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedMarkerStructureFormula : SetTheorySemisentence 5 :=
  “U M B A a. ∃ I ∈ U, ∃ X ∈ U, ∃ F ∈ U, ∃ R ∈ U, ∃ D ∈ U, ∃ z ∈ U,
    !boundedEmptyFormula z ∧ !boundedSuccFormula I B ∧ !boundedFiniteFunctionSetFormula U X A z ∧
    !boundedMarkerFunctionsFormula U F I X B a ∧ !boundedMembershipRelationsFormula U R A ∧
    !boundedKpairFormula D F R ∧ !boundedKpairFormula M A D”

def sigmaOneMarkerStructureFormula : SetTheorySemisentence 4 :=
  “M B A a. ∃ U, !sequenceSupportFormula U ∧ A ∈ U ∧ B ∈ U ∧ a ∈ U ∧
    !boundedMarkerStructureFormula U M B A a”

def sigmaOneNonMarkerStructureFormula : SetTheorySemisentence 4 :=
  “M B A a. ∃ N, !sigmaOneMarkerStructureFormula N B A a ∧ N ≠ M”

def piOneMarkerStructureFormula : SetTheorySemisentence 4 := ∼sigmaOneNonMarkerStructureFormula

theorem boundedMarkerStructureFormula_bounded : IsBoundedSetFormula boundedMarkerStructureFormula := by
  repeat' first
    | exact boundedEmptyFormula_bounded.subst _
    | exact boundedSuccFormula_bounded.subst _
    | exact boundedFiniteFunctionSetFormula_bounded.subst _
    | exact boundedMarkerFunctionsFormula_bounded.subst _
    | exact boundedMembershipRelationsFormula_bounded.subst _
    | exact boundedKpairFormula_bounded.subst _
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and

theorem sigmaOneMarkerStructureFormula_sigmaOne : IsSigmaFormula 1 sigmaOneMarkerStructureFormula :=
  .exs (.and (.bounded (sequenceSupportFormula_bounded.subst _))
    (.and (.bounded (.rel _ _)) (.and (.bounded (.rel _ _)) (.and (.bounded (.rel _ _))
      (.bounded (boundedMarkerStructureFormula_bounded.subst _))))))

theorem sigmaOneNonMarkerStructureFormula_sigmaOne : IsSigmaFormula 1 sigmaOneNonMarkerStructureFormula :=
  .exs (.and (sigmaOneMarkerStructureFormula_sigmaOne.subst _) (.bounded (.nrel _ _)))

theorem piOneMarkerStructureFormula_piOne : IsPiFormula 1 piOneMarkerStructureFormula :=
  sigmaOneNonMarkerStructureFormula_sigmaOne.neg

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedMarkerStructureFormula (U M B A a : V) :
    boundedMarkerStructureFormula.Evalb ![U, M, B, A, a] ↔
      ∃ I ∈ U, ∃ X ∈ U, ∃ F ∈ U, ∃ R ∈ U, ∃ D ∈ U,
        (∅ : V) ∈ U ∧ I = succ B ∧ boundedFiniteFunctionSetFormula.Evalb ![U, X, A, ∅] ∧
        boundedMarkerFunctionsFormula.Evalb ![U, F, I, X, B, a] ∧
        boundedMembershipRelationsFormula.Evalb ![U, R, A] ∧ D = ⟨F, R⟩ₖ ∧ M = ⟨A, D⟩ₖ := by
  simp [boundedMarkerStructureFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def]

theorem boundedMarkerStructureFormula_sound {U M B A a : V} [hU : IsSequenceSupport U]
    (hA : A ⊆ U) (h : boundedMarkerStructureFormula.Evalb ![U, M, B, A, a]) :
    M = markerStructure B A a := by
  obtain ⟨I, _, X, _, F, _, R, _, D, _, _, rfl, hX, hF, hR, rfl, rfl⟩ :=
    (eval_boundedMarkerStructureFormula U M B A a).mp h
  have heX : X = A ^ (0 : V) :=
    (eval_boundedFiniteFunctionSetFormula hA (show (∅ : V) ∈ (ω : V) from empty_mem_ω) X).mp hX
  subst X
  have heF := ((eval_boundedMarkerFunctionsFormula U F B A a).mp hF).1
  have heR := ((eval_boundedMembershipRelationsFormula hA R).mp hR).1
  simp only [heF, heR, markerStructure, namedMembershipStructureCode, structureCode]

theorem boundedMarkerStructureFormula_complete {U B A a : V} [hU : IsSequenceSupport U]
    (hB : B ∈ U) (hA : A ∈ U) (hX : A ^ (0 : V) ∈ U)
    (hF : namedMembershipFunctions (succ B) A (markerNames B a) ∈ U)
    (hR : structureRelations (membershipStructureCode A) ∈ U)
    (hX₂ : A ^ (2 : V) ∈ U) (hE : equalityRelation A ∈ U) (hD : membershipTupleRelation A ∈ U) :
    boundedMarkerStructureFormula.Evalb ![U, markerStructure B A a, B, A, a] := by
  have hAU : A ⊆ U := hU.transitive A hA
  apply (eval_boundedMarkerStructureFormula _ _ _ _ _).mpr
  refine ⟨succ B, hU.succ_closed _ hB, _, hX, _, hF, _, hR, _, hU.kpair_closed _ hF _ hR,
    IsCodingSupport.empty_mem, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · exact (eval_boundedFiniteFunctionSetFormula hAU (show (∅ : V) ∈ (ω : V) from empty_mem_ω) _).mpr rfl
  · exact (eval_boundedMarkerFunctionsFormula U _ B A a).mpr ⟨rfl, markerFunctions_values_mem_of_mem hF⟩
  · exact (eval_boundedMembershipRelationsFormula hAU _).mpr ⟨rfl, hX₂, hE, hD⟩

theorem eval_sigmaOneMarkerStructureFormula (M B A a : V) :
    sigmaOneMarkerStructureFormula.Evalb ![M, B, A, a] ↔ M = markerStructure B A a := by
  simp only [sigmaOneMarkerStructureFormula]
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  constructor
  · rintro ⟨U, hU, hA, _, _, h⟩
    let := hU
    exact boundedMarkerStructureFormula_sound (hU.transitive A hA) h
  · rintro rfl
    obtain ⟨U, hU, hv⟩ := sequenceSupport_containing_parameters
      ![B, A, a, A ^ (0 : V), namedMembershipFunctions (succ B) A (markerNames B a),
        structureRelations (membershipStructureCode A), A ^ (2 : V), equalityRelation A, membershipTupleRelation A]
    let := hU
    exact ⟨U, hU, hv 1, hv 0, hv 2,
      boundedMarkerStructureFormula_complete (hv 0) (hv 1) (hv 3) (hv 4) (hv 5) (hv 6) (hv 7) (hv 8)⟩

theorem eval_sigmaOneNonMarkerStructureFormula (M B A a : V) :
    sigmaOneNonMarkerStructureFormula.Evalb ![M, B, A, a] ↔ M ≠ markerStructure B A a := by
  simp [sigmaOneNonMarkerStructureFormula, eval_sigmaOneMarkerStructureFormula, eq_comm]

theorem eval_piOneMarkerStructureFormula (M B A a : V) :
    piOneMarkerStructureFormula.Evalb ![M, B, A, a] ↔ M = markerStructure B A a := by
  simp [piOneMarkerStructureFormula, eval_sigmaOneNonMarkerStructureFormula]

end ZFVP
