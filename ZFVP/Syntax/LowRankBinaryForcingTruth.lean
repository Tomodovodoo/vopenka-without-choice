import ZFVP.Syntax.LowRankForcingTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def lowRankCheckedBinaryForcingFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 7 :=
  f“P R o ξ p a b. !(lowRankForcingTruthFormula φ) P R ξ ξ p
    (!assignmentPrependFormula (!(numeralFormula 1))
      (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) (!checkNameFormula o b))
      (!checkNameFormula o a))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance lowRankCheckedBinaryForcingFormula_defined (φ : SetTheorySemisentence 2) :
    Defined (fun v : Fin 7 → V ↦ v 4 ∈ classForcingFormula (v 0) (v 1)
      (IsLowRankForcingName (v 0) (v 3)) (by definability) φ
      (standardTuple ![checkName (v 2) (v 5), checkName (v 2) (v 6)]))
      (lowRankCheckedBinaryForcingFormula φ) :=
  ⟨fun v ↦ by
    simp [lowRankCheckedBinaryForcingFormula, standardTuple, Semiformula.eval_nestFormulae,
      Matrix.vecForall_iff, Fin.forall_fin_succ]
    constructor
    · intro h
      exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    · rintro h a b c d e f rfl rfl rfl rfl rfl rfl
      exact h⟩

end ZFVP
