import ZFVP.Syntax.BoundedInternalForcingTable
import ZFVP.Syntax.InternalForcingTableUniqueness
import ZFVP.SetTheory.BoundedAtomicTruth
import ZFVP.SetTheory.BoundedSequenceSupport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneInternalNonforcingFormula : SetTheorySemisentence 7 :=
  “P R D n φ b p. ∃ U, !sequenceSupportFormula U ∧ P ∈ U ∧ D ∈ U ∧
    ∃ O, !boundedOmegaFormula O ∧ ∃ F, !sigmaOneMembershipFamilyFormula F ∧
    ∃ H, !boundedAtomicTruthTableFormula U P R H ∧
    ∃ T, !boundedInternalForcingTableFormula U O F P R D H T ∧
      ¬ !(CodeExpression.kpair (.var 0) (.var 1)).forcingLookupFormula U T b p n φ”

theorem sigmaOneInternalNonforcingFormula_sigmaOne : IsSigmaFormula 1 sigmaOneInternalNonforcingFormula := by
  unfold sigmaOneInternalNonforcingFormula
  refine .exs (.and (.bounded (sequenceSupportFormula_bounded.subst _))
    (.and (.bounded (.rel _ _)) (.and (.bounded (.rel _ _))
      (.exs (.and (.bounded (boundedOmegaFormula_bounded.subst _))
        (.exs (.and (sigmaOneMembershipFamilyFormula_sigmaOne.subst _)
          (.exs (.and (.bounded (boundedAtomicTruthTableFormula_bounded.subst _))
            (.exs (.and (.bounded (boundedInternalForcingTableFormula_bounded.subst _))
              (.bounded (((CodeExpression.kpair (.var 0) (.var 1)).forcingLookupFormula_bounded.subst _).neg)))))))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneInternalNonforcingFormula {P R D n φ b p : V}
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ D ^ n) (hp : p ∈ P) :
    sigmaOneInternalNonforcingFormula.Evalb ![P, R, D, n, φ, b, p] ↔ ¬ InternalForces P R D n φ b p := by
  have hm : sigmaOneInternalNonforcingFormula.Evalb ![P, R, D, n, φ, b, p] ↔
      ∃ U : V, IsSequenceSupport U ∧ P ∈ U ∧ D ∈ U ∧
        ∃ H : V, boundedAtomicTruthTableFormula.Evalb ![U, P, R, H] ∧
          ∃ T : V, boundedInternalForcingTableFormula.Evalb ![U, ω, formulaFamily membershipLanguageCode ∅, P, R, D, H, T] ∧
            ¬ (CodeExpression.kpair (.var 0) (.var 1)).forcingLookupFormula.Evalb ![U, T, b, p, n, φ] := by
    simp [sigmaOneInternalNonforcingFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [hm]
  have hlocal (U : V) (hU : IsSequenceSupport U) (hP : P ∈ U) (hD : D ∈ U) :
      (∃ H : V, boundedAtomicTruthTableFormula.Evalb ![U, P, R, H] ∧
        ∃ T : V, boundedInternalForcingTableFormula.Evalb ![U, ω, formulaFamily membershipLanguageCode ∅, P, R, D, H, T] ∧
          ¬ (CodeExpression.kpair (.var 0) (.var 1)).forcingLookupFormula.Evalb ![U, T, b, p, n, φ]) ↔
      ¬ InternalForces P R D n φ b p := by
    let := hU
    have hPs : P ⊆ U := hU.toIsTransitive.transitive P hP
    have hDs : D ⊆ U := hU.toIsTransitive.transitive D hD
    have hbu := function_mem_sequenceSupport hDs hφ.context hb
    have hnu : n ∈ U := IsCodingSupport.natural_mem hφ.context
    have hφu : φ ∈ U := membershipFormulaCode_formula_mem_support hφ
    constructor
    · rintro ⟨H, hH, T, hT, ht⟩
      have hH := (eval_boundedAtomicTruthTableFormula P R H).mp hH
      have hT : IsInternalForcingTruthTable P R D T := (eval_boundedInternalForcingTableFormula hPs hDs hH T).mp hT
      have hl := (not_congr (CodeExpression.eval_forcingLookupFormula_two (.kpair (.var 0) (.var 1)) T hbu (hPs p hp) hnu hφu)).mp ht
      exact (not_congr (hT.lookup hφ hb hp)).mp hl
    · intro ht
      obtain ⟨H, hH⟩ := atomicTruthTable_exists P R U (transitive_subnameClosed hU.toIsTransitive)
      refine ⟨H, (eval_boundedAtomicTruthTableFormula P R H).mpr hH, internalForcingTruthTable P R D,
        (eval_boundedInternalForcingTableFormula hPs hDs hH _).mpr (internalForcingTruthTable_correct P R D), ?_⟩
      apply (not_congr (CodeExpression.eval_forcingLookupFormula_two (.kpair (.var 0) (.var 1)) _ hbu (hPs p hp) hnu hφu)).mpr
      exact (not_congr (internalForcingTruthTable_lookup hφ hb hp)).mpr ht
  constructor
  · rintro ⟨U, hU, hP, hD, hh⟩
    exact (hlocal U hU hP hD).mp hh
  · intro ht
    obtain ⟨U, hU, hpair⟩ := sequenceSupport_containing ⟨P, D⟩ₖ
    let := hU
    obtain ⟨hP, hD⟩ := kpair_components_mem_transitive hpair
    exact ⟨U, hU, hP, hD, (hlocal U hU hP hD).mpr ht⟩

end ZFVP

