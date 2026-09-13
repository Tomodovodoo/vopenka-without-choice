import ZFVP.Syntax.ProgramZFVPConsistency
import ZFVP.Syntax.PrimitiveProgramTheoryRaw
import ZFVP.Syntax.ArithmeticZFVPConsistency

/-! Standard truth of the explicit consistency sentence for exactly ZF+VP. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

theorem eval_programZFVPConsistencySentence_nat :
    programZFVPConsistencySentence.Evalb (![] : Fin 0 → ℕ) ↔ Entailment.Consistent zfVPTheory := by
  rw [eval_programZFVPConsistencySentence, Entailment.consistent_iff_unprovable_bot]
  simpa only [evalArithmetic_programZFVPRefutation, arithmeticPair_nat, evalArithmetic_nat,
    natCast_nat, not_exists] using not_congr (externalZFVP_programProof_iff (⊥ : SetTheorySentence))

theorem programZFVPConsistency_standard_equivalence :
    programZFVPConsistencySentence.Evalb (![] : Fin 0 → ℕ) ↔
      arithmeticZFVPConsistencySentence.Evalb (![] : Fin 0 → ℕ) :=
  eval_programZFVPConsistencySentence_nat.trans eval_arithmeticZFVPConsistencySentence.symm

end ZFVP
