import ZFVP.ModelTheory.BoundedMembershipRelations
import ZFVP.ModelTheory.MarkerMembership

/-! Bounded checks for the constant symbols of a one-marker structure. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedMarkerFunctionValueFormula : SetTheorySemisentence 5 :=
  “g X B a i. (i = B ∧ !boundedConstantGraphFormula g X a) ∨
    (i ≠ B ∧ !boundedConstantGraphFormula g X i)”

def boundedMarkerFunctionsFormula : SetTheorySemisentence 6 :=
  “U F I X B a. (∀ p ∈ F, ∃ i ∈ I, ∃ g ∈ U,
    !boundedKpairFormula p i g ∧ !boundedMarkerFunctionValueFormula g X B a i) ∧
    ∀ i ∈ I, ∃ g ∈ U, !boundedPairMemberFormula F i g ∧ !boundedMarkerFunctionValueFormula g X B a i”

theorem boundedMarkerFunctionValueFormula_bounded : IsBoundedSetFormula boundedMarkerFunctionValueFormula :=
  .or (.and (.rel _ _) (boundedConstantGraphFormula_bounded.subst _))
    (.and (.nrel _ _) (boundedConstantGraphFormula_bounded.subst _))

theorem boundedMarkerFunctionsFormula_bounded : IsBoundedSetFormula boundedMarkerFunctionsFormula :=
  .and (.all (.bvar 1) (.exs (.bvar 3) (.exs (.bvar 2)
    (.and (boundedKpairFormula_bounded.subst _) (boundedMarkerFunctionValueFormula_bounded.subst _)))))
    (.all (.bvar 2) (.exs (.bvar 1)
      (.and (boundedPairMemberFormula_bounded.subst _) (boundedMarkerFunctionValueFormula_bounded.subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem eval_boundedMarkerFunctionValueFormula (g X B a i : V) :
    boundedMarkerFunctionValueFormula.Evalb ![g, X, B, a, i] ↔
      g = constantGraph X (markerValue B a i) := by
  simp [boundedMarkerFunctionValueFormula, markerValue]
  split_ifs <;> simp_all

theorem namedMembershipFunctions_marker (B A a : V) :
    namedMembershipFunctions (succ B) A (markerNames B a) =
      definableGraph (succ B) (fun i ↦ constantGraph (A ^ (0 : V)) (markerValue B a i)) (by definability) := by
  apply mem_ext
  intro p
  simp only [namedMembershipFunctions, mem_definableGraph_iff]
  apply exists_congr
  intro i
  apply and_congr_right
  intro hi
  rw [markerNames, value_definableGraph _ _ _ hi]

theorem eval_boundedMarkerFunctionsFormula (U F B A a : V) :
    boundedMarkerFunctionsFormula.Evalb ![U, F, succ B, A ^ (0 : V), B, a] ↔
      F = namedMembershipFunctions (succ B) A (markerNames B a) ∧
        ∀ i ∈ succ B, constantGraph (A ^ (0 : V)) (markerValue B a i) ∈ U := by
  simp only [boundedMarkerFunctionsFormula]
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  rw [namedMembershipFunctions_marker, mem_ext_iff]
  simp only [mem_definableGraph_iff]
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨?_, fun i hi ↦ (hr i hi).1⟩
    intro p
    constructor
    · intro hp
      obtain ⟨i, hi, _, he⟩ := hl p hp
      exact ⟨i, hi, he⟩
    · rintro ⟨i, hi, rfl⟩
      exact (hr i hi).2
  · rintro ⟨he, hg⟩
    refine ⟨?_, fun i hi ↦ ⟨hg i hi, (he _).mpr ⟨i, hi, rfl⟩⟩⟩
    intro p hp
    obtain ⟨i, hi, he⟩ := (he p).mp hp
    exact ⟨i, hi, hg i hi, he⟩

theorem markerFunctions_values_mem_of_mem {U B A a : V} [hU : IsTransitive U]
    (hF : namedMembershipFunctions (succ B) A (markerNames B a) ∈ U) :
    ∀ i ∈ succ B, constantGraph (A ^ (0 : V)) (markerValue B a i) ∈ U := by
  intro i hi
  rw [namedMembershipFunctions_marker] at hF
  have hp := hU.mem_trans ((mem_definableGraph_iff _ _ _ _).mpr ⟨i, hi, rfl⟩) hF
  exact (kpair_components_mem_transitive hp).2

end ZFVP
