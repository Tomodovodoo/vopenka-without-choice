import ZFVP.ModelTheory.DeltaOneForcingCodeComponents
import ZFVP.ModelTheory.ForcingLimitCode
import ZFVP.SetTheory.BoundedSetUnionInter
import ZFVP.SetTheory.BoundedRelationRange

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneForcingCodeUniverseFormula : SetTheorySemisentence 2 :=
  “U s. ∃ P, !sigmaOneForcingCodePFormula P s ∧ ∃ R, !boundedRangeFormula R P ∧ !boundedSUnionFormula U R”

def piOneForcingCodeUniverseFormula : SetTheorySemisentence 2 :=
  “U s. ∀ P, !sigmaOneForcingCodePFormula P s → ∀ R, !boundedRangeFormula R P → !boundedSUnionFormula U R”

theorem sigmaOneForcingCodeUniverseFormula_sigmaOne : IsSigmaFormula 1 sigmaOneForcingCodeUniverseFormula :=
  .exs (.and (sigmaOneForcingCodePFormula_sigmaOne.subst _)
    (.exs (.bounded (.and (boundedRangeFormula_bounded.subst _) (boundedSUnionFormula_bounded.subst _)))))

theorem piOneForcingCodeUniverseFormula_piOne : IsPiFormula 1 piOneForcingCodeUniverseFormula :=
  .all (.or (sigmaOneForcingCodePFormula_sigmaOne.subst _).neg
    (.all (.bounded (.or (boundedRangeFormula_bounded.subst _).neg (boundedSUnionFormula_bounded.subst _)))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneForcingCodeUniverseFormula_defined :
    ℒₛₑₜ-function₁[V] forcingCodeUniverse via sigmaOneForcingCodeUniverseFormula :=
  ⟨fun v ↦ by simp [sigmaOneForcingCodeUniverseFormula, forcingCodeUniverse]⟩

instance piOneForcingCodeUniverseFormula_defined :
    ℒₛₑₜ-function₁[V] forcingCodeUniverse via piOneForcingCodeUniverseFormula :=
  ⟨fun v ↦ by simp [piOneForcingCodeUniverseFormula, forcingCodeUniverse]⟩

end ZFVP
