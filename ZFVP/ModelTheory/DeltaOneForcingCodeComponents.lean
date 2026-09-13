import ZFVP.SetTheory.DeltaOnePairProjections
import ZFVP.SetTheory.DeltaOneUnaryComposition
import ZFVP.SetTheory.ForcingIterationCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaPairPathFormula (first : Bool) : ℕ → SetTheorySemisentence 2
  | 0 => if first then sigmaOnePairFirstFormula else sigmaOnePairSecondFormula
  | n + 1 => sigmaUnaryComposition (sigmaPairPathFormula first n) sigmaOnePairSecondFormula

def piPairPathFormula (first : Bool) : ℕ → SetTheorySemisentence 2
  | 0 => if first then piOnePairFirstFormula else piOnePairSecondFormula
  | n + 1 => piUnaryComposition (piPairPathFormula first n) sigmaOnePairSecondFormula

theorem sigmaPairPathFormula_sigmaOne (first : Bool) (n : ℕ) :
    IsSigmaFormula 1 (sigmaPairPathFormula first n) := by
  induction n with
  | zero => cases first <;> first | exact sigmaOnePairSecondFormula_sigmaOne | exact sigmaOnePairFirstFormula_sigmaOne
  | succ n ih => exact sigmaUnaryComposition_sigmaOne ih sigmaOnePairSecondFormula_sigmaOne

theorem piPairPathFormula_piOne (first : Bool) (n : ℕ) :
    IsPiFormula 1 (piPairPathFormula first n) := by
  induction n with
  | zero => cases first <;> first | exact piOnePairSecondFormula_piOne | exact piOnePairFirstFormula_piOne
  | succ n ih => exact piUnaryComposition_piOne ih sigmaOnePairSecondFormula_sigmaOne

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def pairPathValue (first : Bool) : ℕ → V → V
  | 0, x => if first then kpair.π₁ x else kpair.π₂ x
  | n + 1, x => pairPathValue first n (kpair.π₂ x)

instance sigmaPairPathFormula_defined (first : Bool) (n : ℕ) :
    ℒₛₑₜ-function₁[V] (pairPathValue first n) via sigmaPairPathFormula first n := by
  induction n with
  | zero => cases first <;> dsimp [pairPathValue, sigmaPairPathFormula] <;> infer_instance
  | succ n ih =>
    let := ih
    exact sigmaUnaryComposition_defined (pairPathValue first n) kpair.π₂
      (sigmaPairPathFormula first n) sigmaOnePairSecondFormula

instance piPairPathFormula_defined (first : Bool) (n : ℕ) :
    ℒₛₑₜ-function₁[V] (pairPathValue first n) via piPairPathFormula first n := by
  induction n with
  | zero => cases first <;> dsimp [pairPathValue, piPairPathFormula] <;> infer_instance
  | succ n ih =>
    let := ih
    exact piUnaryComposition_defined (pairPathValue first n) kpair.π₂
      (piPairPathFormula first n) sigmaOnePairSecondFormula

def sigmaOneForcingCodePFormula : SetTheorySemisentence 2 := sigmaPairPathFormula true 0

theorem sigmaOneForcingCodePFormula_sigmaOne : IsSigmaFormula 1 sigmaOneForcingCodePFormula :=
  sigmaPairPathFormula_sigmaOne true 0

instance sigmaOneForcingCodePFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeP via sigmaOneForcingCodePFormula := by
  exact sigmaPairPathFormula_defined true 0

def piOneForcingCodePFormula : SetTheorySemisentence 2 := piPairPathFormula true 0

theorem piOneForcingCodePFormula_piOne : IsPiFormula 1 piOneForcingCodePFormula :=
  piPairPathFormula_piOne true 0

instance piOneForcingCodePFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeP via piOneForcingCodePFormula := by
  exact piPairPathFormula_defined true 0

def sigmaOneForcingCodeRFormula : SetTheorySemisentence 2 := sigmaPairPathFormula true 1

theorem sigmaOneForcingCodeRFormula_sigmaOne : IsSigmaFormula 1 sigmaOneForcingCodeRFormula :=
  sigmaPairPathFormula_sigmaOne true 1

instance sigmaOneForcingCodeRFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeR via sigmaOneForcingCodeRFormula := by
  exact sigmaPairPathFormula_defined true 1

def piOneForcingCodeRFormula : SetTheorySemisentence 2 := piPairPathFormula true 1

theorem piOneForcingCodeRFormula_piOne : IsPiFormula 1 piOneForcingCodeRFormula :=
  piPairPathFormula_piOne true 1

instance piOneForcingCodeRFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeR via piOneForcingCodeRFormula := by
  exact piPairPathFormula_defined true 1

def sigmaOneForcingCodeπFormula : SetTheorySemisentence 2 := sigmaPairPathFormula true 2

theorem sigmaOneForcingCodeπFormula_sigmaOne : IsSigmaFormula 1 sigmaOneForcingCodeπFormula :=
  sigmaPairPathFormula_sigmaOne true 2

instance sigmaOneForcingCodeπFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeπ via sigmaOneForcingCodeπFormula := by
  exact sigmaPairPathFormula_defined true 2

def piOneForcingCodeπFormula : SetTheorySemisentence 2 := piPairPathFormula true 2

theorem piOneForcingCodeπFormula_piOne : IsPiFormula 1 piOneForcingCodeπFormula :=
  piPairPathFormula_piOne true 2

instance piOneForcingCodeπFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeπ via piOneForcingCodeπFormula := by
  exact piPairPathFormula_defined true 2

def sigmaOneForcingCodeEFormula : SetTheorySemisentence 2 := sigmaPairPathFormula true 3

theorem sigmaOneForcingCodeEFormula_sigmaOne : IsSigmaFormula 1 sigmaOneForcingCodeEFormula :=
  sigmaPairPathFormula_sigmaOne true 3

instance sigmaOneForcingCodeEFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeE via sigmaOneForcingCodeEFormula := by
  exact sigmaPairPathFormula_defined true 3

def piOneForcingCodeEFormula : SetTheorySemisentence 2 := piPairPathFormula true 3

theorem piOneForcingCodeEFormula_piOne : IsPiFormula 1 piOneForcingCodeEFormula :=
  piPairPathFormula_piOne true 3

instance piOneForcingCodeEFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeE via piOneForcingCodeEFormula := by
  exact piPairPathFormula_defined true 3

def sigmaOneForcingCodeLFormula : SetTheorySemisentence 2 := sigmaPairPathFormula true 4

theorem sigmaOneForcingCodeLFormula_sigmaOne : IsSigmaFormula 1 sigmaOneForcingCodeLFormula :=
  sigmaPairPathFormula_sigmaOne true 4

instance sigmaOneForcingCodeLFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeL via sigmaOneForcingCodeLFormula := by
  exact sigmaPairPathFormula_defined true 4

def piOneForcingCodeLFormula : SetTheorySemisentence 2 := piPairPathFormula true 4

theorem piOneForcingCodeLFormula_piOne : IsPiFormula 1 piOneForcingCodeLFormula :=
  piPairPathFormula_piOne true 4

instance piOneForcingCodeLFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeL via piOneForcingCodeLFormula := by
  exact piPairPathFormula_defined true 4

def sigmaOneForcingCodetFormula : SetTheorySemisentence 2 := sigmaPairPathFormula false 4

theorem sigmaOneForcingCodetFormula_sigmaOne : IsSigmaFormula 1 sigmaOneForcingCodetFormula :=
  sigmaPairPathFormula_sigmaOne false 4

instance sigmaOneForcingCodetFormula_defined : ℒₛₑₜ-function₁[V] forcingCodet via sigmaOneForcingCodetFormula := by
  exact sigmaPairPathFormula_defined false 4

def piOneForcingCodetFormula : SetTheorySemisentence 2 := piPairPathFormula false 4

theorem piOneForcingCodetFormula_piOne : IsPiFormula 1 piOneForcingCodetFormula :=
  piPairPathFormula_piOne false 4

instance piOneForcingCodetFormula_defined : ℒₛₑₜ-function₁[V] forcingCodet via piOneForcingCodetFormula := by
  exact piPairPathFormula_defined false 4

end ZFVP
