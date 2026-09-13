import ZFVP.SetTheory.BoundedCodingPrimitives
import ZFVP.Syntax.StandardTuples

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneBinaryTupleFormula : SetTheorySemisentence 3 :=
  “A x y. ∃ z, ∃ o, ∃ p, ∃ q,
    !boundedEmptyFormula z ∧ !boundedSuccFormula o z ∧
    !boundedKpairFormula p z x ∧ !boundedKpairFormula q o y ∧ !boundedDoubletonFormula A p q”

theorem sigmaOneBinaryTupleFormula_sigmaOne : IsSigmaFormula 1 sigmaOneBinaryTupleFormula :=
  .exs (.exs (.exs (.exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
    (.and (.bounded (boundedSuccFormula_bounded.subst _))
      (.and (.bounded (boundedKpairFormula_bounded.subst _))
        (.and (.bounded (boundedKpairFormula_bounded.subst _))
          (.bounded (boundedDoubletonFormula_bounded.subst _)))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem standardTuple_two_eq (x y : V) :
    standardTuple ![x, y] = doubleton ⟨(0 : V), x⟩ₖ ⟨(1 : V), y⟩ₖ := by
  apply mem_ext
  intro p
  simp [mem_standardTuple_iff, Fin.exists_fin_succ]

theorem eval_sigmaOneBinaryTupleFormula (A x y : V) :
    sigmaOneBinaryTupleFormula.Evalb ![A, x, y] ↔ A = standardTuple ![x, y] := by
  simp [sigmaOneBinaryTupleFormula, standardTuple_two_eq, zero_def, one_def, succ]

end ZFVP

