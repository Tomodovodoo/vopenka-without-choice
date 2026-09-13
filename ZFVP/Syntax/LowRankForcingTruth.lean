import ZFVP.Syntax.ForcingTranslationSemantics
import ZFVP.ModelTheory.ForcingRankTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def lowRankNamePredicateFormula : SetTheorySemisentence 4 :=
  f“P ξ D τ. τ ∈ !hierarchyFormula ξ ∧ !forcingNameFormula P τ”

def lowRankForcingTruthFormula {n : ℕ} (φ : SetTheorySemisentence n) : SetTheorySemisentence 6 :=
  forcingTranslation lowRankNamePredicateFormula φ

def lowRankCheckedUnaryForcingFormula (φ : SetTheorySemisentence 1) : SetTheorySemisentence 6 :=
  f“P R o ξ p a. !(lowRankForcingTruthFormula φ) P R ξ ξ p
    (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) (!checkNameFormula o a))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance lowRankNamePredicateFormula_defined :
    Defined (fun v : Fin 4 → V ↦ IsLowRankForcingName (v 0) (v 1) (v 3))
      lowRankNamePredicateFormula :=
  ⟨fun v ↦ by simp [lowRankNamePredicateFormula, IsLowRankForcingName]⟩

instance lowRankForcingTruthFormula_defined {n : ℕ} (φ : SetTheorySemisentence n) :
    Defined (fun v : Fin 6 → V ↦ v 4 ∈ classForcingFormula (v 0) (v 1)
      (IsLowRankForcingName (v 0) (v 2)) (by definability) φ (v 5))
      (lowRankForcingTruthFormula φ) := by
  exact forcingTranslation_defined lowRankNamePredicateFormula
    (fun P ξ _ τ ↦ IsLowRankForcingName P ξ τ) (by unfold IsLowRankForcingName; definability) φ

instance lowRankCheckedUnaryForcingFormula_defined (φ : SetTheorySemisentence 1) :
    Defined (fun v : Fin 6 → V ↦ v 4 ∈ classForcingFormula (v 0) (v 1)
      (IsLowRankForcingName (v 0) (v 3)) (by definability) φ
      (standardTuple ![checkName (v 2) (v 5)])) (lowRankCheckedUnaryForcingFormula φ) :=
  ⟨fun v ↦ by
    simp [lowRankCheckedUnaryForcingFormula, standardTuple, Semiformula.eval_nestFormulae,
      Matrix.vecForall_iff, Fin.forall_fin_succ]
    constructor
    · intro h
      exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    · rintro h a b c d e f rfl rfl rfl rfl rfl rfl
      exact h⟩

end ZFVP
