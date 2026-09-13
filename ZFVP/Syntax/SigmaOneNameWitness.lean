import ZFVP.Syntax.SigmaOneInternalForcing
import ZFVP.SetTheory.ForcingNameFamily
import ZFVP.SetTheory.DeltaOneBoundedTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneNameWitnessMatrix : SetTheorySemisentence 7 :=
  “D P R n φ b p. !boundedNameFamilyFormula P D ∧ !boundedNonemptyFormula D ∧
    !boundedFunctionFormula b n D ∧ ∃ τ ∈ D, ∃ O, !boundedOmegaFormula O ∧
      ∃ c, !boundedAssignmentPrependFormula D O c n b τ ∧ ∃ m, !boundedSuccFormula m n ∧
        !sigmaOneInternalForcingFormula P R D m φ c p”

theorem sigmaOneNameWitnessMatrix_sigmaOne : IsSigmaFormula 1 sigmaOneNameWitnessMatrix := by
  unfold sigmaOneNameWitnessMatrix
  exact .and (.bounded (boundedNameFamilyFormula_bounded.subst _))
    (.and (.bounded (boundedNonemptyFormula_bounded.subst _))
      (.and (.bounded (boundedFunctionFormula_bounded.subst _))
        (.boundedExs (.bvar 0) (.exs (.and (.bounded (boundedOmegaFormula_bounded.subst _))
          (.exs (.and (.bounded (boundedAssignmentPrependFormula_bounded.subst _))
            (.exs (.and (.bounded (boundedSuccFormula_bounded.subst _))
              (sigmaOneInternalForcingFormula_sigmaOne.subst _))))))))))

def sigmaOneNameWitnessFormula : SetTheorySemisentence 6 := .exs sigmaOneNameWitnessMatrix

theorem sigmaOneNameWitnessFormula_sigmaOne : IsSigmaFormula 1 sigmaOneNameWitnessFormula :=
  .exs sigmaOneNameWitnessMatrix_sigmaOne

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneNameWitnessMatrix {D P R n φ b p : V} (hn : n ∈ (ω : V))
    (hφ : IsMembershipFormulaCode (succ n) φ) (hp : p ∈ P) :
    sigmaOneNameWitnessMatrix.Evalb ![D, P, R, n, φ, b, p] ↔
      IsForcingNameFamily P D ∧ IsNonempty D ∧ b ∈ D ^ n ∧
        ∃ τ ∈ D, InternalForces P R D (succ n) φ (assignmentPrepend n b τ) p := by
  simp only [sigmaOneNameWitnessMatrix]
  simp [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  intro _ _ hb
  apply exists_congr
  intro τ
  apply and_congr_right
  intro hτ
  change (∃ c : V, boundedAssignmentPrependFormula.Evalb ![D, ω, c, n, b, τ] ∧
    sigmaOneInternalForcingFormula.Evalb ![P, R, D, succ n, φ, c, p]) ↔ _
  simp only [eval_boundedAssignmentPrependFormula hn hb hτ]
  simp only [exists_eq_left]
  exact eval_sigmaOneInternalForcingFormula hφ (assignmentPrepend_mem_function hn hb hτ) hp

theorem eval_sigmaOneNameWitnessFormula {P R n φ b p : V} (hn : n ∈ (ω : V))
    (hφ : IsMembershipFormulaCode (succ n) φ) (hp : p ∈ P) :
    sigmaOneNameWitnessFormula.Evalb ![P, R, n, φ, b, p] ↔
      ∃ D : V, IsForcingNameFamily P D ∧ IsNonempty D ∧ b ∈ D ^ n ∧
        ∃ τ ∈ D, InternalForces P R D (succ n) φ (assignmentPrepend n b τ) p := by
  change (∃ D : V, sigmaOneNameWitnessMatrix.Evalb ![D, P, R, n, φ, b, p]) ↔ _
  exact exists_congr (fun _ ↦ eval_sigmaOneNameWitnessMatrix hn hφ hp)

end ZFVP
