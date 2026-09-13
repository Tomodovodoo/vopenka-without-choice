import ZFVP.ModelTheory.DeltaOneForcingCodeComponents
import ZFVP.ModelTheory.BoundedForcingCode
import ZFVP.SetTheory.DeltaOneMatrixNext
import ZFVP.SetTheory.DeltaOneIdentityLift

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneForcingCodeNextFormula : SetTheorySemisentence 9 :=
  “z θ s Q T ρ F M u. ∃ P, ∃ R, ∃ π, ∃ E, ∃ L, ∃ t, ∃ I, ∃ D, ∃ P1, ∃ R1, ∃ π1, ∃ E1, ∃ L1, ∃ t1,
    !sigmaOneForcingCodePFormula P s ∧
    !sigmaOneForcingCodeRFormula R s ∧
    !sigmaOneForcingCodeπFormula π s ∧
    !sigmaOneForcingCodeEFormula E s ∧
    !sigmaOneForcingCodeLFormula L s ∧
    !sigmaOneForcingCodetFormula t s ∧
    !boundedIdentityFormula I Q ∧
    !sigmaOneIdentityLiftFormula D Q ∧
    !sigmaOneFamilyNextFormula P1 θ P Q ∧
    !sigmaOneFamilyNextFormula R1 θ R T ∧
    !sigmaOneMatrixNextFormula π1 θ π ρ I ∧
    !sigmaOneMatrixNextFormula E1 θ E F I ∧
    !sigmaOneMatrixNextFormula L1 θ L M D ∧
    !sigmaOneFamilyNextFormula t1 θ t u ∧
    !boundedForcingCodeFormula z P1 R1 π1 E1 L1 t1”

theorem sigmaOneForcingCodeNextFormula_sigmaOne : IsSigmaFormula 1 sigmaOneForcingCodeNextFormula :=
  (.exs (.exs (.exs (.exs (.exs (.exs (.exs (.exs (.exs (.exs (.exs (.exs (.exs (.exs
    (.and (sigmaOneForcingCodePFormula_sigmaOne.subst _)
    (.and (sigmaOneForcingCodeRFormula_sigmaOne.subst _)
    (.and (sigmaOneForcingCodeπFormula_sigmaOne.subst _)
    (.and (sigmaOneForcingCodeEFormula_sigmaOne.subst _)
    (.and (sigmaOneForcingCodeLFormula_sigmaOne.subst _)
    (.and (sigmaOneForcingCodetFormula_sigmaOne.subst _)
    (.and (.bounded (boundedIdentityFormula_bounded.subst _))
    (.and (sigmaOneIdentityLiftFormula_sigmaOne.subst _)
    (.and (sigmaOneFamilyNextFormula_sigmaOne.subst _)
    (.and (sigmaOneFamilyNextFormula_sigmaOne.subst _)
    (.and (sigmaOneMatrixNextFormula_sigmaOne.subst _)
    (.and (sigmaOneMatrixNextFormula_sigmaOne.subst _)
    (.and (sigmaOneMatrixNextFormula_sigmaOne.subst _)
    (.and (sigmaOneFamilyNextFormula_sigmaOne.subst _) (.bounded (boundedForcingCodeFormula_bounded.subst _))))))))))))))))))))))))))))))

def piOneForcingCodeNextFormula : SetTheorySemisentence 9 :=
  “z θ s Q T ρ F M u. ∀ P, ∀ R, ∀ π, ∀ E, ∀ L, ∀ t, ∀ I, ∀ D, ∀ P1, ∀ R1, ∀ π1, ∀ E1, ∀ L1, ∀ t1,
    !sigmaOneForcingCodePFormula P s →
    !sigmaOneForcingCodeRFormula R s →
    !sigmaOneForcingCodeπFormula π s →
    !sigmaOneForcingCodeEFormula E s →
    !sigmaOneForcingCodeLFormula L s →
    !sigmaOneForcingCodetFormula t s →
    !boundedIdentityFormula I Q →
    !sigmaOneIdentityLiftFormula D Q →
    !sigmaOneFamilyNextFormula P1 θ P Q →
    !sigmaOneFamilyNextFormula R1 θ R T →
    !sigmaOneMatrixNextFormula π1 θ π ρ I →
    !sigmaOneMatrixNextFormula E1 θ E F I →
    !sigmaOneMatrixNextFormula L1 θ L M D →
    !sigmaOneFamilyNextFormula t1 θ t u →
    !boundedForcingCodeFormula z P1 R1 π1 E1 L1 t1”

theorem piOneForcingCodeNextFormula_piOne : IsPiFormula 1 piOneForcingCodeNextFormula :=
  (.all (.all (.all (.all (.all (.all (.all (.all (.all (.all (.all (.all (.all (.all
    (.or (sigmaOneForcingCodePFormula_sigmaOne.subst _).neg
    (.or (sigmaOneForcingCodeRFormula_sigmaOne.subst _).neg
    (.or (sigmaOneForcingCodeπFormula_sigmaOne.subst _).neg
    (.or (sigmaOneForcingCodeEFormula_sigmaOne.subst _).neg
    (.or (sigmaOneForcingCodeLFormula_sigmaOne.subst _).neg
    (.or (sigmaOneForcingCodetFormula_sigmaOne.subst _).neg
    (.or (IsLevyFormula.bounded (p := .sigma) (k := 1) (boundedIdentityFormula_bounded.subst _)).neg
    (.or (sigmaOneIdentityLiftFormula_sigmaOne.subst _).neg
    (.or (sigmaOneFamilyNextFormula_sigmaOne.subst _).neg
    (.or (sigmaOneFamilyNextFormula_sigmaOne.subst _).neg
    (.or (sigmaOneMatrixNextFormula_sigmaOne.subst _).neg
    (.or (sigmaOneMatrixNextFormula_sigmaOne.subst _).neg
    (.or (sigmaOneMatrixNextFormula_sigmaOne.subst _).neg
    (.or (sigmaOneFamilyNextFormula_sigmaOne.subst _).neg (.bounded (boundedForcingCodeFormula_bounded.subst _))))))))))))))))))))))))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneForcingCodeNextFormula_defined : Defined
    (fun v : Fin 9 → V ↦ v 0 = forcingIterationCodeNext (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8))
    sigmaOneForcingCodeNextFormula :=
  ⟨fun v ↦ by simp [sigmaOneForcingCodeNextFormula, forcingIterationCodeNext]⟩

instance piOneForcingCodeNextFormula_defined : Defined
    (fun v : Fin 9 → V ↦ v 0 = forcingIterationCodeNext (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8))
    piOneForcingCodeNextFormula :=
  ⟨fun v ↦ by
    simp [piOneForcingCodeNextFormula, forcingIterationCodeNext]
    constructor
    · intro h
      exact h _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · rintro h P R π E L t I D P1 R1 π1 E1 L1 t1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      exact h⟩

end ZFVP
