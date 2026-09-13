import ZFVP.ModelTheory.BoundedIndexedMarkers

/-! Delta-one definitions for membership structures with an indexed family of constants. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedIndexedMarkerStructureFormula : SetTheorySemisentence 6 :=
  “U M B n A c. ∃ I ∈ U, ∃ X ∈ U, ∃ F ∈ U, ∃ R ∈ U, ∃ D ∈ U, ∃ z ∈ U,
    !boundedEmptyFormula z ∧ !boundedMarkerIndexSetFormula I B n ∧ !boundedFiniteFunctionSetFormula U X A z ∧
    !boundedIndexedMarkerFunctionsFormula U F I X B n c A ∧ !boundedMembershipRelationsFormula U R A ∧
    !boundedKpairFormula D F R ∧ !boundedKpairFormula M A D”

def sigmaOneIndexedMarkerStructureFormula : SetTheorySemisentence 5 :=
  “M B n A c. B ⊆ A ∧ !boundedFunctionFormula c n A ∧ ∃ U,
    !sequenceSupportFormula U ∧ A ∈ U ∧ B ∈ U ∧ n ∈ U ∧ c ∈ U ∧
    !boundedIndexedMarkerStructureFormula U M B n A c”

def sigmaOneOtherIndexedMarkerStructureFormula : SetTheorySemisentence 5 :=
  “M B n A c. ∃ N, !sigmaOneIndexedMarkerStructureFormula N B n A c ∧ N ≠ M”

def piOneIndexedMarkerStructureFormula : SetTheorySemisentence 5 :=
  “M B n A c. B ⊆ A ∧ !boundedFunctionFormula c n A ∧ ¬!sigmaOneOtherIndexedMarkerStructureFormula M B n A c”

theorem boundedIndexedMarkerStructureFormula_bounded : IsBoundedSetFormula boundedIndexedMarkerStructureFormula := by
  repeat' first
    | exact boundedEmptyFormula_bounded.subst _
    | exact boundedMarkerIndexSetFormula_bounded.subst _
    | exact boundedFiniteFunctionSetFormula_bounded.subst _
    | exact boundedIndexedMarkerFunctionsFormula_bounded.subst _
    | exact boundedMembershipRelationsFormula_bounded.subst _
    | exact boundedKpairFormula_bounded.subst _
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and

theorem sigmaOneIndexedMarkerStructureFormula_sigmaOne : IsSigmaFormula 1 sigmaOneIndexedMarkerStructureFormula := by
  repeat' first
    | exact IsLevyFormula.bounded (isSubsetOf_bounded.subst _)
    | exact IsLevyFormula.bounded (boundedFunctionFormula_bounded.subst _)
    | exact IsLevyFormula.bounded (sequenceSupportFormula_bounded.subst _)
    | exact IsLevyFormula.bounded (boundedIndexedMarkerStructureFormula_bounded.subst _)
    | apply IsLevyFormula.and
    | apply IsLevyFormula.exs
    | exact .bounded (.rel _ _)

theorem sigmaOneOtherIndexedMarkerStructureFormula_sigmaOne : IsSigmaFormula 1 sigmaOneOtherIndexedMarkerStructureFormula :=
  .exs (.and (sigmaOneIndexedMarkerStructureFormula_sigmaOne.subst _) (.bounded (.nrel _ _)))

theorem piOneIndexedMarkerStructureFormula_piOne : IsPiFormula 1 piOneIndexedMarkerStructureFormula :=
  .and (.bounded (isSubsetOf_bounded.subst _)) (.and (.bounded (boundedFunctionFormula_bounded.subst _))
    (sigmaOneOtherIndexedMarkerStructureFormula_sigmaOne.subst _).neg)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedIndexedMarkerStructureFormula (U M B n A c : V) :
    boundedIndexedMarkerStructureFormula.Evalb ![U, M, B, n, A, c] ↔
      ∃ I ∈ U, ∃ X ∈ U, ∃ F ∈ U, ∃ R ∈ U, ∃ D ∈ U,
        (∅ : V) ∈ U ∧ I = markerIndexSet B n ∧ boundedFiniteFunctionSetFormula.Evalb ![U, X, A, ∅] ∧
        boundedIndexedMarkerFunctionsFormula.Evalb ![U, F, I, X, B, n, c, A] ∧
        boundedMembershipRelationsFormula.Evalb ![U, R, A] ∧ D = ⟨F, R⟩ₖ ∧ M = ⟨A, D⟩ₖ := by
  simp [boundedIndexedMarkerStructureFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, eval_boundedMarkerIndexSetFormula]

theorem boundedIndexedMarkerStructureFormula_sound {U M B n A c : V} [hU : IsSequenceSupport U]
    (hA : A ⊆ U) (hBA : B ⊆ A) (hc : c ∈ A ^ n)
    (h : boundedIndexedMarkerStructureFormula.Evalb ![U, M, B, n, A, c]) :
    M = indexedMarkerStructure B n A c := by
  obtain ⟨I, _, X, _, F, _, R, _, D, _, _, rfl, hX, hF, hR, rfl, rfl⟩ :=
    (eval_boundedIndexedMarkerStructureFormula U M B n A c).mp h
  have heX : X = A ^ (0 : V) :=
    (eval_boundedFiniteFunctionSetFormula hA (show (∅ : V) ∈ (ω : V) from empty_mem_ω) X).mp hX
  subst X
  have heF := ((eval_boundedIndexedMarkerFunctionsFormula hBA hc U F).mp hF).1
  have heR := ((eval_boundedMembershipRelationsFormula hA R).mp hR).1
  simp only [heF, heR, indexedMarkerStructure, namedMembershipStructureCode, structureCode]

theorem boundedIndexedMarkerStructureFormula_complete {U B n A c : V} [hU : IsSequenceSupport U]
    (hBA : B ⊆ A) (hc : c ∈ A ^ n) (hI : markerIndexSet B n ∈ U) (hA : A ∈ U) (hX : A ^ (0 : V) ∈ U)
    (hF : namedMembershipFunctions (markerIndexSet B n) A (indexedMarkerNames B n c) ∈ U)
    (hR : structureRelations (membershipStructureCode A) ∈ U)
    (hX₂ : A ^ (2 : V) ∈ U) (hE : equalityRelation A ∈ U) (hD : membershipTupleRelation A ∈ U) :
    boundedIndexedMarkerStructureFormula.Evalb ![U, indexedMarkerStructure B n A c, B, n, A, c] := by
  have hAU : A ⊆ U := hU.transitive A hA
  apply (eval_boundedIndexedMarkerStructureFormula _ _ _ _ _ _).mpr
  refine ⟨_, hI, _, hX, _, hF, _, hR, _, hU.kpair_closed _ hF _ hR,
    IsCodingSupport.empty_mem, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · exact (eval_boundedFiniteFunctionSetFormula hAU (show (∅ : V) ∈ (ω : V) from empty_mem_ω) _).mpr rfl
  · exact (eval_boundedIndexedMarkerFunctionsFormula hBA hc U _).mpr
      ⟨rfl, indexedMarkerFunctions_values_mem_of_mem hF⟩
  · exact (eval_boundedMembershipRelationsFormula hAU _).mpr ⟨rfl, hX₂, hE, hD⟩

theorem eval_sigmaOneIndexedMarkerStructureFormula (M B n A c : V) :
    sigmaOneIndexedMarkerStructureFormula.Evalb ![M, B, n, A, c] ↔
      B ⊆ A ∧ c ∈ A ^ n ∧ M = indexedMarkerStructure B n A c := by
  simp only [sigmaOneIndexedMarkerStructureFormula]
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  intro hBA hc
  constructor
  · rintro ⟨U, hU, hA, _, _, _, h⟩
    let := hU
    exact boundedIndexedMarkerStructureFormula_sound (hU.transitive A hA) hBA hc h
  · rintro rfl
    obtain ⟨U, hU, hv⟩ := sequenceSupport_containing_parameters
      ![B, n, A, c, markerIndexSet B n, A ^ (0 : V),
        namedMembershipFunctions (markerIndexSet B n) A (indexedMarkerNames B n c),
        structureRelations (membershipStructureCode A), A ^ (2 : V), equalityRelation A, membershipTupleRelation A]
    let := hU
    exact ⟨U, hU, hv 2, hv 0, hv 1, hv 3,
      boundedIndexedMarkerStructureFormula_complete hBA hc (hv 4) (hv 2) (hv 5) (hv 6) (hv 7) (hv 8) (hv 9) (hv 10)⟩

theorem eval_sigmaOneOtherIndexedMarkerStructureFormula (M B n A c : V) :
    sigmaOneOtherIndexedMarkerStructureFormula.Evalb ![M, B, n, A, c] ↔
      B ⊆ A ∧ c ∈ A ^ n ∧ M ≠ indexedMarkerStructure B n A c := by
  simp [sigmaOneOtherIndexedMarkerStructureFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
    eval_sigmaOneIndexedMarkerStructureFormula, eq_comm, and_assoc]

theorem eval_piOneIndexedMarkerStructureFormula (M B n A c : V) :
    piOneIndexedMarkerStructureFormula.Evalb ![M, B, n, A, c] ↔
      B ⊆ A ∧ c ∈ A ^ n ∧ M = indexedMarkerStructure B n A c := by
  simp [piOneIndexedMarkerStructureFormula,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
    eval_sigmaOneOtherIndexedMarkerStructureFormula]
  tauto

end ZFVP
