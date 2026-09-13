import ZFVP.ModelTheory.DeltaTwoForcingLimitCodes
import ZFVP.ModelTheory.WoodinInverseUniform
import ZFVP.SetTheory.BoundedSetUnionInter
import ZFVP.SetTheory.BoundedRelationRange

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def sigmaTwoInverseCodePosetFormula : SetTheorySemisentence 3 :=
  “G θ s. ∃ P, !sigmaOneForcingCodePFormula P s ∧
    ∃ π, !sigmaOneForcingCodeπFormula π s ∧
    ∃ U, !sigmaOneForcingCodeUniverseFormula U s ∧
    !piOneInverseLimitGraphFormula G θ P π U”

theorem sigmaTwoInverseCodePosetFormula_sigmaTwo : IsSigmaFormula 2 sigmaTwoInverseCodePosetFormula :=
  .exs (.and (.raise (sigmaOneForcingCodePFormula_sigmaOne.subst _))
    (.exs (.and (.raise (sigmaOneForcingCodeπFormula_sigmaOne.subst _))
    (.exs (.and (.raise (sigmaOneForcingCodeUniverseFormula_sigmaOne.subst _))
    (.raise (piOneInverseLimitGraphFormula_piOne.subst _)))))))

instance sigmaTwoInverseCodePosetFormula_defined : ℒₛₑₜ-function₂[V] forcingInverseCodePoset via sigmaTwoInverseCodePosetFormula :=
  ⟨fun v ↦ by simp [sigmaTwoInverseCodePosetFormula, forcingInverseCodePoset]⟩

def piTwoInverseCodePosetFormula : SetTheorySemisentence 3 :=
  “G θ s. ∀ W, !sigmaTwoInverseCodePosetFormula W θ s → G = W”

theorem piTwoInverseCodePosetFormula_piTwo : IsPiFormula 2 piTwoInverseCodePosetFormula :=
  .all (.or (sigmaTwoInverseCodePosetFormula_sigmaTwo.subst _).neg (.bounded (.rel _ _)))

instance piTwoInverseCodePosetFormula_defined : ℒₛₑₜ-function₂[V] forcingInverseCodePoset via piTwoInverseCodePosetFormula :=
  ⟨fun v ↦ by simp [piTwoInverseCodePosetFormula]⟩

def sigmaTwoInverseCodeOrderFormula : SetTheorySemisentence 3 :=
  “G θ s. ∃ R, !sigmaOneForcingCodeRFormula R s ∧
    ∃ P, !sigmaTwoInverseCodePosetFormula P θ s ∧
    !sigmaOneThreadOrderGraphFormula G θ R P”

theorem sigmaTwoInverseCodeOrderFormula_sigmaTwo : IsSigmaFormula 2 sigmaTwoInverseCodeOrderFormula :=
  .exs (.and (.raise (sigmaOneForcingCodeRFormula_sigmaOne.subst _))
    (.exs (.and (sigmaTwoInverseCodePosetFormula_sigmaTwo.subst _)
    (.raise (sigmaOneThreadOrderGraphFormula_sigmaOne.subst _)))))

instance sigmaTwoInverseCodeOrderFormula_defined : ℒₛₑₜ-function₂[V] forcingInverseCodeOrder via sigmaTwoInverseCodeOrderFormula :=
  ⟨fun v ↦ by simp [sigmaTwoInverseCodeOrderFormula, forcingInverseCodeOrder]⟩

def piTwoInverseCodeOrderFormula : SetTheorySemisentence 3 :=
  “G θ s. ∀ W, !sigmaTwoInverseCodeOrderFormula W θ s → G = W”

theorem piTwoInverseCodeOrderFormula_piTwo : IsPiFormula 2 piTwoInverseCodeOrderFormula :=
  .all (.or (sigmaTwoInverseCodeOrderFormula_sigmaTwo.subst _).neg (.bounded (.rel _ _)))

instance piTwoInverseCodeOrderFormula_defined : ℒₛₑₜ-function₂[V] forcingInverseCodeOrder via piTwoInverseCodeOrderFormula :=
  ⟨fun v ↦ by simp [piTwoInverseCodeOrderFormula]⟩

def sigmaOneInverseCodeTopFormula : SetTheorySemisentence 3 :=
  “G θ s. ∃ π, !sigmaOneForcingCodeπFormula π s ∧
    ∃ E, !sigmaOneForcingCodeEFormula E s ∧
    ∃ t, !sigmaOneForcingCodetFormula t s ∧
    ∃ o, !boundedEmptyFormula o ∧
    ∃ a, !boundedValueFormula a t o ∧
    !sigmaOneSectionThreadFormula G θ π E o a”

theorem sigmaOneInverseCodeTopFormula_sigmaOne : IsSigmaFormula 1 sigmaOneInverseCodeTopFormula :=
  .exs (.and (sigmaOneForcingCodeπFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneForcingCodeEFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneForcingCodetFormula_sigmaOne.subst _)
    (.exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (sigmaOneSectionThreadFormula_sigmaOne.subst _))))))))))

instance sigmaOneInverseCodeTopFormula_defined : ℒₛₑₜ-function₂[V] forcingInverseCodeTop via sigmaOneInverseCodeTopFormula :=
  ⟨fun v ↦ by simp [sigmaOneInverseCodeTopFormula, forcingInverseCodeTop]⟩

def piOneInverseCodeTopFormula : SetTheorySemisentence 3 :=
  “G θ s. ∀ W, !sigmaOneInverseCodeTopFormula W θ s → G = W”

theorem piOneInverseCodeTopFormula_piOne : IsPiFormula 1 piOneInverseCodeTopFormula :=
  .all (.or (sigmaOneInverseCodeTopFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

instance piOneInverseCodeTopFormula_defined : ℒₛₑₜ-function₂[V] forcingInverseCodeTop via piOneInverseCodeTopFormula :=
  ⟨fun v ↦ by simp [piOneInverseCodeTopFormula]⟩

def sigmaOneWoodinLimitCardinalFormula : SetTheorySemisentence 2 :=
  “G K. ∃ R, !boundedRangeFormula R K ∧
    !boundedSUnionFormula G R”

theorem sigmaOneWoodinLimitCardinalFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinLimitCardinalFormula :=
  .exs (.and (.bounded (boundedRangeFormula_bounded.subst _))
    (.bounded (boundedSUnionFormula_bounded.subst _)))

instance sigmaOneWoodinLimitCardinalFormula_defined : ℒₛₑₜ-function₁[V] woodinLimitCardinal via sigmaOneWoodinLimitCardinalFormula :=
  ⟨fun v ↦ by simp [sigmaOneWoodinLimitCardinalFormula, woodinLimitCardinal]⟩

def piOneWoodinLimitCardinalFormula : SetTheorySemisentence 2 :=
  “G K. ∀ W, !sigmaOneWoodinLimitCardinalFormula W K → G = W”

theorem piOneWoodinLimitCardinalFormula_piOne : IsPiFormula 1 piOneWoodinLimitCardinalFormula :=
  .all (.or (sigmaOneWoodinLimitCardinalFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

instance piOneWoodinLimitCardinalFormula_defined : ℒₛₑₜ-function₁[V] woodinLimitCardinal via piOneWoodinLimitCardinalFormula :=
  ⟨fun v ↦ by simp [piOneWoodinLimitCardinalFormula]⟩

end ZFVP
