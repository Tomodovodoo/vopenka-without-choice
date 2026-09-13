import ZFVP.ModelTheory.DeltaOneThreadCode
import ZFVP.ModelTheory.DeltaOneForcingCodeUniverse
import ZFVP.SetTheory.PiOneForcingDirectLimit

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaTwoForcingDirectCodeFormula : SetTheorySemisentence 3 :=
  “G θ s. ∃ P, !sigmaOneForcingCodePFormula P s ∧
    ∃ π, !sigmaOneForcingCodeπFormula π s ∧
    ∃ E, !sigmaOneForcingCodeEFormula E s ∧
    ∃ U, !sigmaOneForcingCodeUniverseFormula U s ∧
    ∃ C, !piOneDirectLimitGraphFormula C θ P π E U ∧
    !sigmaOneThreadCodeFormula G θ s C”

theorem sigmaTwoForcingDirectCodeFormula_sigmaTwo : IsSigmaFormula 2 sigmaTwoForcingDirectCodeFormula :=
  (.exs (.and (.raise (sigmaOneForcingCodePFormula_sigmaOne.subst _))
    (.exs (.and (.raise (sigmaOneForcingCodeπFormula_sigmaOne.subst _))
    (.exs (.and (.raise (sigmaOneForcingCodeEFormula_sigmaOne.subst _))
    (.exs (.and (.raise (sigmaOneForcingCodeUniverseFormula_sigmaOne.subst _))
    (.exs (.and (.raise (piOneDirectLimitGraphFormula_piOne.subst _))
    (.raise (sigmaOneThreadCodeFormula_sigmaOne.subst _))))))))))))

def piTwoForcingDirectCodeFormula : SetTheorySemisentence 3 :=
  “G θ s. ∀ P, !sigmaOneForcingCodePFormula P s →
    ∀ π, !sigmaOneForcingCodeπFormula π s →
    ∀ E, !sigmaOneForcingCodeEFormula E s →
    ∀ U, !sigmaOneForcingCodeUniverseFormula U s →
    ∀ C, !piOneDirectLimitGraphFormula C θ P π E U →
    !piOneThreadCodeFormula G θ s C”

theorem piTwoForcingDirectCodeFormula_piTwo : IsPiFormula 2 piTwoForcingDirectCodeFormula :=
  (.all (.or (.raise (sigmaOneForcingCodePFormula_sigmaOne.subst _).neg)
    (.all (.or (.raise (sigmaOneForcingCodeπFormula_sigmaOne.subst _).neg)
    (.all (.or (.raise (sigmaOneForcingCodeEFormula_sigmaOne.subst _).neg)
    (.all (.or (.raise (sigmaOneForcingCodeUniverseFormula_sigmaOne.subst _).neg)
    (.all (.or (.raise (piOneDirectLimitGraphFormula_piOne.subst _).neg)
    (.raise (piOneThreadCodeFormula_piOne.subst _))))))))))))

def sigmaTwoForcingInverseCodeFormula : SetTheorySemisentence 3 :=
  “G θ s. ∃ P, !sigmaOneForcingCodePFormula P s ∧
    ∃ π, !sigmaOneForcingCodeπFormula π s ∧
    ∃ U, !sigmaOneForcingCodeUniverseFormula U s ∧
    ∃ C, !piOneInverseLimitGraphFormula C θ P π U ∧
    !sigmaOneThreadCodeFormula G θ s C”

theorem sigmaTwoForcingInverseCodeFormula_sigmaTwo : IsSigmaFormula 2 sigmaTwoForcingInverseCodeFormula :=
  (.exs (.and (.raise (sigmaOneForcingCodePFormula_sigmaOne.subst _))
    (.exs (.and (.raise (sigmaOneForcingCodeπFormula_sigmaOne.subst _))
    (.exs (.and (.raise (sigmaOneForcingCodeUniverseFormula_sigmaOne.subst _))
    (.exs (.and (.raise (piOneInverseLimitGraphFormula_piOne.subst _))
    (.raise (sigmaOneThreadCodeFormula_sigmaOne.subst _))))))))))

def piTwoForcingInverseCodeFormula : SetTheorySemisentence 3 :=
  “G θ s. ∀ P, !sigmaOneForcingCodePFormula P s →
    ∀ π, !sigmaOneForcingCodeπFormula π s →
    ∀ U, !sigmaOneForcingCodeUniverseFormula U s →
    ∀ C, !piOneInverseLimitGraphFormula C θ P π U →
    !piOneThreadCodeFormula G θ s C”

theorem piTwoForcingInverseCodeFormula_piTwo : IsPiFormula 2 piTwoForcingInverseCodeFormula :=
  (.all (.or (.raise (sigmaOneForcingCodePFormula_sigmaOne.subst _).neg)
    (.all (.or (.raise (sigmaOneForcingCodeπFormula_sigmaOne.subst _).neg)
    (.all (.or (.raise (sigmaOneForcingCodeUniverseFormula_sigmaOne.subst _).neg)
    (.all (.or (.raise (piOneInverseLimitGraphFormula_piOne.subst _).neg)
    (.raise (piOneThreadCodeFormula_piOne.subst _))))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaTwoForcingDirectCodeFormula_defined : ℒₛₑₜ-function₂[V] forcingDirectCode via sigmaTwoForcingDirectCodeFormula :=
  ⟨fun v ↦ by simp [sigmaTwoForcingDirectCodeFormula, forcingDirectCode]⟩

instance piTwoForcingDirectCodeFormula_defined : ℒₛₑₜ-function₂[V] forcingDirectCode via piTwoForcingDirectCodeFormula :=
  ⟨fun v ↦ by simp [piTwoForcingDirectCodeFormula, forcingDirectCode]⟩

instance sigmaTwoForcingInverseCodeFormula_defined : ℒₛₑₜ-function₂[V] forcingInverseCode via sigmaTwoForcingInverseCodeFormula :=
  ⟨fun v ↦ by simp [sigmaTwoForcingInverseCodeFormula, forcingInverseCode]⟩

instance piTwoForcingInverseCodeFormula_defined : ℒₛₑₜ-function₂[V] forcingInverseCode via piTwoForcingInverseCodeFormula :=
  ⟨fun v ↦ by simp [piTwoForcingInverseCodeFormula, forcingInverseCode]⟩

end ZFVP
