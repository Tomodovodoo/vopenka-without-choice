import ZFVP.Syntax.PartialTruthAtoms
import ZFVP.Syntax.LevyCodeSubstitution
import ZFVP.Syntax.FormulaSubstitutionSemantics

/-! Capture-avoiding substitution commutes with every positive internal partial-truth predicate. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def membershipSubstitutedAssignment (s b : V) : V :=
  compose (stateBound s) (termEvaluation membershipLanguageCode ∅ (stateTarget s) ∅ b ∅)

instance membershipSubstitutedAssignment_definable : ℒₛₑₜ-function₂[V] membershipSubstitutedAssignment := by
  unfold membershipSubstitutedAssignment
  apply Language.DefinableFunction₂.comp
  · definability
  · exact Language.DefinableFunction.substitution
      (f := ![fun _ ↦ membershipLanguageCode, fun _ ↦ ∅,
        fun v : Fin 2 → V ↦ stateTarget (v 0), fun _ ↦ ∅, fun v ↦ v 1, fun _ ↦ ∅])
      termEvaluation_definable (by simp [Fin.forall_fin_iff_zero_and_forall_succ]; all_goals definability)

theorem membershipSubstitutedAssignment_eq {s : V} (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s)
    (b A : V) : membershipSubstitutedAssignment s b =
      compose (stateBound s) (termEvaluation membershipLanguageCode ∅ (stateTarget s) (membershipStructureCode A) b ∅) := by
  unfold membershipSubstitutedAssignment
  rw [membershipTermEvaluation_eq hs.2.1 (∅ : V) (membershipStructureCode A) b ∅ ∅]

theorem membershipSubstitutedAssignment_mem {s A b : V}
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s) (hA : IsNonempty A)
    (hb : b ∈ A ^ stateTarget s) : membershipSubstitutedAssignment s b ∈ A ^ stateSource s := by
  rw [membershipSubstitutedAssignment_eq hs b A]
  have hT := termEvaluation_mem_function (e := (∅ : V)) (membershipStructureCode_valid hA) hs.2.1 ∅
    (by simpa using hb) (mem_function.intro (by simp) (by simp))
  simpa only [membershipStructureCode_domain] using compose_function hs.2.2.1 hT

theorem membershipSatisfies_substitute {s A φ b : V}
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s) (hA : IsNonempty A)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (stateSource s)) (hb : b ∈ A ^ stateTarget s) :
    MembershipSatisfies A (stateTarget s) (substituteFormula membershipLanguageCode ∅ ∅ s φ) b ↔
      MembershipSatisfies A (stateSource s) φ (membershipSubstitutedAssignment s b) := by
  have hT := termEvaluation_mem_function (e := (∅ : V)) (membershipStructureCode_valid hA) hs.2.1 ∅
    (by simpa using hb) (mem_function.intro (by simp) (by simp))
  have hE : compose (stateFree s)
      (termEvaluation membershipLanguageCode ∅ (stateTarget s) (membershipStructureCode A) b ∅) = ∅ := by
    apply subset_empty_iff_eq_empty.mp
    simpa using subset_prod_of_mem_function (compose_function hs.2.2.2 hT)
  have he := satisfies_substituteFormula (e := (∅ : V)) (membershipStructureCode_valid hA) hs
    (mem_function.intro (by simp) (by simp)) hφ (by simpa using hb)
  rw [hE, ← membershipSubstitutedAssignment_eq hs b A] at he
  exact he

theorem domainTruth_substitute {p : LevyPolarity} {k : ℕ} {s φ b : V}
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s)
    (hφ : IsLevyFormulaCode p (k + 1) (stateSource s) φ)
    (hb : IsFunction b ∧ domain b = stateTarget s) :
    DomainTruth p k (stateTarget s) (substituteFormula membershipLanguageCode ∅ ∅ s φ) b ↔
      DomainTruth p k (stateSource s) φ (membershipSubstitutedAssignment s b) := by
  obtain ⟨A, hA, hbA⟩ := correctDomain_assignment (k + 1) hb
  rw [hA.truth_iff (substituteFormula_levy hs hφ) hbA,
    hA.truth_iff hφ (membershipSubstitutedAssignment_mem hs hA.nonempty hbA)]
  exact membershipSatisfies_substitute hs hA.nonempty hφ.valid hbA

theorem boundedTruth_substitute {s φ b : V}
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s)
    (hφ : IsBoundedFormulaCode (stateSource s) φ)
    (hb : IsFunction b ∧ domain b = stateTarget s) :
    BoundedTruth (stateTarget s) (substituteFormula membershipLanguageCode ∅ ∅ s φ) b ↔
      BoundedTruth (stateSource s) φ (membershipSubstitutedAssignment s b) := by
  obtain ⟨A, hA, hbA⟩ := correctDomain_assignment 0 hb
  let := hA.support
  rw [boundedTruth_iff_membershipSatisfies (substituteFormula_bounded hs hφ) hA.nonempty hbA,
    boundedTruth_iff_membershipSatisfies hφ hA.nonempty (membershipSubstitutedAssignment_mem hs hA.nonempty hbA)]
  exact membershipSatisfies_substitute hs hA.nonempty hφ.valid hbA

end ZFVP
