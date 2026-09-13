import ZFVP.ModelTheory.DeltaOneHistoryTables
import ZFVP.ModelTheory.DeltaOneForcingCodeComponents
import ZFVP.ModelTheory.BoundedForcingCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneForcingCodeUnionFormula : SetTheorySemisentence 3 :=
  “G θ H. ∃ P, !(sigmaOneHistoryTableFormula sigmaOneForcingCodePFormula) P θ H ∧
    ∃ R, !(sigmaOneHistoryTableFormula sigmaOneForcingCodeRFormula) R θ H ∧
    ∃ π, !(sigmaOneHistoryTableFormula sigmaOneForcingCodeπFormula) π θ H ∧
    ∃ E, !(sigmaOneHistoryTableFormula sigmaOneForcingCodeEFormula) E θ H ∧
    ∃ L, !(sigmaOneHistoryTableFormula sigmaOneForcingCodeLFormula) L θ H ∧
    ∃ t, !(sigmaOneHistoryTableFormula sigmaOneForcingCodetFormula) t θ H ∧
    !boundedForcingCodeFormula G P R π E L t”

theorem sigmaOneForcingCodeUnionFormula_sigmaOne : IsSigmaFormula 1 sigmaOneForcingCodeUnionFormula :=
  (.exs (.and ((sigmaOneHistoryTableFormula_sigmaOne sigmaOneForcingCodePFormula_sigmaOne).subst _)
    (.exs (.and ((sigmaOneHistoryTableFormula_sigmaOne sigmaOneForcingCodeRFormula_sigmaOne).subst _)
    (.exs (.and ((sigmaOneHistoryTableFormula_sigmaOne sigmaOneForcingCodeπFormula_sigmaOne).subst _)
    (.exs (.and ((sigmaOneHistoryTableFormula_sigmaOne sigmaOneForcingCodeEFormula_sigmaOne).subst _)
    (.exs (.and ((sigmaOneHistoryTableFormula_sigmaOne sigmaOneForcingCodeLFormula_sigmaOne).subst _)
    (.exs (.and ((sigmaOneHistoryTableFormula_sigmaOne sigmaOneForcingCodetFormula_sigmaOne).subst _)
    (.bounded (boundedForcingCodeFormula_bounded.subst _))))))))))))))

def piOneForcingCodeUnionFormula : SetTheorySemisentence 3 :=
  “G θ H. ∀ P, !(sigmaOneHistoryTableFormula sigmaOneForcingCodePFormula) P θ H →
    ∀ R, !(sigmaOneHistoryTableFormula sigmaOneForcingCodeRFormula) R θ H →
    ∀ π, !(sigmaOneHistoryTableFormula sigmaOneForcingCodeπFormula) π θ H →
    ∀ E, !(sigmaOneHistoryTableFormula sigmaOneForcingCodeEFormula) E θ H →
    ∀ L, !(sigmaOneHistoryTableFormula sigmaOneForcingCodeLFormula) L θ H →
    ∀ t, !(sigmaOneHistoryTableFormula sigmaOneForcingCodetFormula) t θ H →
    !boundedForcingCodeFormula G P R π E L t”

theorem piOneForcingCodeUnionFormula_piOne : IsPiFormula 1 piOneForcingCodeUnionFormula :=
  (.all (.or ((sigmaOneHistoryTableFormula_sigmaOne sigmaOneForcingCodePFormula_sigmaOne).subst _).neg
    (.all (.or ((sigmaOneHistoryTableFormula_sigmaOne sigmaOneForcingCodeRFormula_sigmaOne).subst _).neg
    (.all (.or ((sigmaOneHistoryTableFormula_sigmaOne sigmaOneForcingCodeπFormula_sigmaOne).subst _).neg
    (.all (.or ((sigmaOneHistoryTableFormula_sigmaOne sigmaOneForcingCodeEFormula_sigmaOne).subst _).neg
    (.all (.or ((sigmaOneHistoryTableFormula_sigmaOne sigmaOneForcingCodeLFormula_sigmaOne).subst _).neg
    (.all (.or ((sigmaOneHistoryTableFormula_sigmaOne sigmaOneForcingCodetFormula_sigmaOne).subst _).neg
    (.bounded (boundedForcingCodeFormula_bounded.subst _))))))))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneForcingCodeUnionFormula_defined : ℒₛₑₜ-function₂[V] forcingIterationCodeUnion via sigmaOneForcingCodeUnionFormula :=
  ⟨fun v ↦ by simp [sigmaOneForcingCodeUnionFormula, forcingIterationCodeUnion]⟩

instance piOneForcingCodeUnionFormula_defined : ℒₛₑₜ-function₂[V] forcingIterationCodeUnion via piOneForcingCodeUnionFormula :=
  ⟨fun v ↦ by simp [piOneForcingCodeUnionFormula, forcingIterationCodeUnion]⟩

end ZFVP
