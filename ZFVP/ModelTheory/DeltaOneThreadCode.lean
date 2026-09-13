import ZFVP.ModelTheory.DeltaOneForcingCodeNext
import ZFVP.ModelTheory.ForcingLimitCode
import ZFVP.SetTheory.BoundedLimitProjectionColumns
import ZFVP.SetTheory.DeltaOneLimitSectionColumns
import ZFVP.SetTheory.DeltaOneLimitLiftColumns
import ZFVP.SetTheory.DeltaOneThreadOrder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneThreadCodeFormula : SetTheorySemisentence 4 :=
  “G θ s C. ∃ P, !sigmaOneForcingCodePFormula P s ∧
    ∃ R, !sigmaOneForcingCodeRFormula R s ∧
    ∃ π, !sigmaOneForcingCodeπFormula π s ∧
    ∃ E, !sigmaOneForcingCodeEFormula E s ∧
    ∃ L, !sigmaOneForcingCodeLFormula L s ∧
    ∃ t, !sigmaOneForcingCodetFormula t s ∧
    ∃ T, !sigmaOneThreadOrderGraphFormula T θ R C ∧
    ∃ ρ, !boundedLimitProjectionColumnFormula ρ θ C ∧
    ∃ F, !sigmaOneLimitSectionColumnFormula F θ P π E ∧
    ∃ M, !sigmaOneLimitLiftColumnFormula M C θ P π L ∧
    ∃ o, !boundedEmptyFormula o ∧
    ∃ a, !boundedValueFormula a t o ∧
    ∃ u, !sigmaOneSectionThreadFormula u θ π E o a ∧
    !sigmaOneForcingCodeNextFormula G θ s C T ρ F M u”

theorem sigmaOneThreadCodeFormula_sigmaOne : IsSigmaFormula 1 sigmaOneThreadCodeFormula :=
  (.exs (.and (sigmaOneForcingCodePFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneForcingCodeRFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneForcingCodeπFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneForcingCodeEFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneForcingCodeLFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneForcingCodetFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneThreadOrderGraphFormula_sigmaOne.subst _)
    (.exs (.and (.bounded (boundedLimitProjectionColumnFormula_bounded.subst _))
    (.exs (.and (sigmaOneLimitSectionColumnFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneLimitLiftColumnFormula_sigmaOne.subst _)
    (.exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (sigmaOneSectionThreadFormula_sigmaOne.subst _)
    (sigmaOneForcingCodeNextFormula_sigmaOne.subst _)))))))))))))))))))))))))))

def piOneThreadCodeFormula : SetTheorySemisentence 4 :=
  “G θ s C. ∀ P, !sigmaOneForcingCodePFormula P s →
    ∀ R, !sigmaOneForcingCodeRFormula R s →
    ∀ π, !sigmaOneForcingCodeπFormula π s →
    ∀ E, !sigmaOneForcingCodeEFormula E s →
    ∀ L, !sigmaOneForcingCodeLFormula L s →
    ∀ t, !sigmaOneForcingCodetFormula t s →
    ∀ T, !sigmaOneThreadOrderGraphFormula T θ R C →
    ∀ ρ, !boundedLimitProjectionColumnFormula ρ θ C →
    ∀ F, !sigmaOneLimitSectionColumnFormula F θ P π E →
    ∀ M, !sigmaOneLimitLiftColumnFormula M C θ P π L →
    ∀ o, !boundedEmptyFormula o →
    ∀ a, !boundedValueFormula a t o →
    ∀ u, !sigmaOneSectionThreadFormula u θ π E o a →
    !piOneForcingCodeNextFormula G θ s C T ρ F M u”

theorem piOneThreadCodeFormula_piOne : IsPiFormula 1 piOneThreadCodeFormula :=
  (.all (.or (sigmaOneForcingCodePFormula_sigmaOne.subst _).neg
    (.all (.or (sigmaOneForcingCodeRFormula_sigmaOne.subst _).neg
    (.all (.or (sigmaOneForcingCodeπFormula_sigmaOne.subst _).neg
    (.all (.or (sigmaOneForcingCodeEFormula_sigmaOne.subst _).neg
    (.all (.or (sigmaOneForcingCodeLFormula_sigmaOne.subst _).neg
    (.all (.or (sigmaOneForcingCodetFormula_sigmaOne.subst _).neg
    (.all (.or (sigmaOneThreadOrderGraphFormula_sigmaOne.subst _).neg
    (.all (.or (.bounded (boundedLimitProjectionColumnFormula_bounded.subst _).neg)
    (.all (.or (sigmaOneLimitSectionColumnFormula_sigmaOne.subst _).neg
    (.all (.or (sigmaOneLimitLiftColumnFormula_sigmaOne.subst _).neg
    (.all (.or (.bounded (boundedEmptyFormula_bounded.subst _).neg)
    (.all (.or (.bounded (boundedValueFormula_bounded.subst _).neg)
    (.all (.or (sigmaOneSectionThreadFormula_sigmaOne.subst _).neg
    (piOneForcingCodeNextFormula_piOne.subst _)))))))))))))))))))))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneThreadCodeFormula_defined : ℒₛₑₜ-function₃[V] forcingThreadCode via sigmaOneThreadCodeFormula :=
  ⟨fun v ↦ by simp [sigmaOneThreadCodeFormula, forcingThreadCode]⟩

instance piOneThreadCodeFormula_defined : ℒₛₑₜ-function₃[V] forcingThreadCode via piOneThreadCodeFormula :=
  ⟨fun v ↦ by simp [piOneThreadCodeFormula, forcingThreadCode]⟩

end ZFVP
