import ZFVP.ModelTheory.WoodinStageUniform
import ZFVP.ModelTheory.DeltaOneForcingCodeComponents

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneWoodinStageCodeFormula : SetTheorySemisentence 5 :=
  “z P R o κ. ∃ a, ∃ b, !boundedKpairFormula b o κ ∧ !boundedKpairFormula a R b ∧ !boundedKpairFormula z P a”

theorem sigmaOneWoodinStageCodeFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinStageCodeFormula :=
  .exs (.exs (.bounded (.and (boundedKpairFormula_bounded.subst _)
    (.and (boundedKpairFormula_bounded.subst _) (boundedKpairFormula_bounded.subst _)))))

def piOneWoodinStageCodeFormula : SetTheorySemisentence 5 :=
  “z P R o κ. ∀ w, !sigmaOneWoodinStageCodeFormula w P R o κ → z = w”

theorem piOneWoodinStageCodeFormula_piOne : IsPiFormula 1 piOneWoodinStageCodeFormula :=
  .all (.or (sigmaOneWoodinStageCodeFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneWoodinStageCodeFormula_defined : ℒₛₑₜ-function₄[V] woodinStageCode via sigmaOneWoodinStageCodeFormula :=
  ⟨fun v ↦ by simp [sigmaOneWoodinStageCodeFormula, woodinStageCode]⟩
instance piOneWoodinStageCodeFormula_defined : ℒₛₑₜ-function₄[V] woodinStageCode via piOneWoodinStageCodeFormula :=
  ⟨fun v ↦ by simp [piOneWoodinStageCodeFormula]⟩

def sigmaOneWoodinStagePosetFormula : SetTheorySemisentence 2 := sigmaPairPathFormula true 0
theorem sigmaOneWoodinStagePosetFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinStagePosetFormula :=
  sigmaPairPathFormula_sigmaOne true 0
instance sigmaOneWoodinStagePosetFormula_defined : ℒₛₑₜ-function₁[V] woodinStagePoset via sigmaOneWoodinStagePosetFormula := by
  exact sigmaPairPathFormula_defined true 0

def piOneWoodinStagePosetFormula : SetTheorySemisentence 2 := piPairPathFormula true 0
theorem piOneWoodinStagePosetFormula_piOne : IsPiFormula 1 piOneWoodinStagePosetFormula :=
  piPairPathFormula_piOne true 0
instance piOneWoodinStagePosetFormula_defined : ℒₛₑₜ-function₁[V] woodinStagePoset via piOneWoodinStagePosetFormula := by
  exact piPairPathFormula_defined true 0

def sigmaOneWoodinStageOrderFormula : SetTheorySemisentence 2 := sigmaPairPathFormula true 1
theorem sigmaOneWoodinStageOrderFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinStageOrderFormula :=
  sigmaPairPathFormula_sigmaOne true 1
instance sigmaOneWoodinStageOrderFormula_defined : ℒₛₑₜ-function₁[V] woodinStageOrder via sigmaOneWoodinStageOrderFormula := by
  exact sigmaPairPathFormula_defined true 1

def piOneWoodinStageOrderFormula : SetTheorySemisentence 2 := piPairPathFormula true 1
theorem piOneWoodinStageOrderFormula_piOne : IsPiFormula 1 piOneWoodinStageOrderFormula :=
  piPairPathFormula_piOne true 1
instance piOneWoodinStageOrderFormula_defined : ℒₛₑₜ-function₁[V] woodinStageOrder via piOneWoodinStageOrderFormula := by
  exact piPairPathFormula_defined true 1

def sigmaOneWoodinStageTopFormula : SetTheorySemisentence 2 := sigmaPairPathFormula true 2
theorem sigmaOneWoodinStageTopFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinStageTopFormula :=
  sigmaPairPathFormula_sigmaOne true 2
instance sigmaOneWoodinStageTopFormula_defined : ℒₛₑₜ-function₁[V] woodinStageTop via sigmaOneWoodinStageTopFormula := by
  exact sigmaPairPathFormula_defined true 2

def piOneWoodinStageTopFormula : SetTheorySemisentence 2 := piPairPathFormula true 2
theorem piOneWoodinStageTopFormula_piOne : IsPiFormula 1 piOneWoodinStageTopFormula :=
  piPairPathFormula_piOne true 2
instance piOneWoodinStageTopFormula_defined : ℒₛₑₜ-function₁[V] woodinStageTop via piOneWoodinStageTopFormula := by
  exact piPairPathFormula_defined true 2

def sigmaOneWoodinStageCardinalFormula : SetTheorySemisentence 2 := sigmaPairPathFormula false 2
theorem sigmaOneWoodinStageCardinalFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinStageCardinalFormula :=
  sigmaPairPathFormula_sigmaOne false 2
instance sigmaOneWoodinStageCardinalFormula_defined : ℒₛₑₜ-function₁[V] woodinStageCardinal via sigmaOneWoodinStageCardinalFormula := by
  exact sigmaPairPathFormula_defined false 2

def piOneWoodinStageCardinalFormula : SetTheorySemisentence 2 := piPairPathFormula false 2
theorem piOneWoodinStageCardinalFormula_piOne : IsPiFormula 1 piOneWoodinStageCardinalFormula :=
  piPairPathFormula_piOne false 2
instance piOneWoodinStageCardinalFormula_defined : ℒₛₑₜ-function₁[V] woodinStageCardinal via piOneWoodinStageCardinalFormula := by
  exact piPairPathFormula_defined false 2

end ZFVP
