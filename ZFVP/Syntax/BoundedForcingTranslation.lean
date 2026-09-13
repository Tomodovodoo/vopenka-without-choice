import ZFVP.Syntax.BoundedFormulaTree
import ZFVP.Syntax.BoundedForcingSteps

/-! A computable Sigma_1 translation for each answer to bounded forcing. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def BoundedFormulaTree.forcingSigma : {n : ℕ} → BoundedFormulaTree n → Bool → SetTheorySemisentence (n + 4)
  | _, .verum, true => .rel Language.Set.Rel.mem ![.bvar 3, .bvar 1]
  | _, .verum, false => .nrel Language.Set.Rel.mem ![.bvar 3, .bvar 1]
  | _, .falsum, true => .falsum
  | _, .falsum, false => .verum
  | _, .rel r ts, answer => forcingAtomicSigmaStep r ts answer
  | _, .nrel r ts, answer => forcingNegationSigmaStep (forcingAtomicSigmaStep r ts (!answer)) answer
  | _, .and φ ψ, answer => forcingAndSigmaStep (φ.forcingSigma answer) (ψ.forcingSigma answer) answer
  | _, .or φ ψ, answer => forcingOrSigmaStep (φ.forcingSigma answer) (ψ.forcingSigma answer) answer
  | _, .all t φ, answer => forcingAllSigmaStep t (φ.forcingSigma answer) answer
  | _, .exs t φ, answer => forcingExsSigmaStep t (φ.forcingSigma answer) answer

theorem BoundedFormulaTree.forcingSigma_sigmaOne {n : ℕ} (φ : BoundedFormulaTree n) (answer : Bool) :
    IsSigmaFormula 1 (φ.forcingSigma answer) := by
  induction φ generalizing answer with
  | verum => cases answer <;> exact .bounded (by constructor)
  | falsum => cases answer <;> exact .bounded (by constructor)
  | rel r ts => exact forcingAtomicSigmaStep_sigmaOne r ts answer
  | nrel r ts => exact forcingNegationSigmaStep_sigmaOne (forcingAtomicSigmaStep_sigmaOne r ts (!answer)) answer
  | and φ ψ ihφ ihψ => exact forcingAndSigmaStep_sigmaOne (ihφ answer) (ihψ answer) answer
  | or φ ψ ihφ ihψ => exact forcingOrSigmaStep_sigmaOne (ihφ answer) (ihψ answer) answer
  | all t φ ih => exact forcingAllSigmaStep_sigmaOne t (ih answer) answer
  | exs t φ ih => exact forcingExsSigmaStep_sigmaOne t (ih answer) answer

end ZFVP
