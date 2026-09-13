import ZFVP.Syntax.ProgramZFVPConsistencyStandard
import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic

/-! The explicit proof checker defines a Sigma-one provability predicate and satisfies D1. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram ProvabilityAbstraction

def programZFVPProvableFormula : 𝚺₁.Semisentence 1 :=
  .mkSigma “f. ∃ p z, !pairDef z f p ∧ !generatedTheoryProofCheck.arithmeticFormula 1 z”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eval_programZFVPProvableFormula (f : M) :
    programZFVPProvableFormula.val.Evalb ![f] ↔
      ∃ p : M, generatedTheoryProofCheck.evalArithmetic (Arithmetic.pair f p) = 1 := by
  simp [programZFVPProvableFormula, (evalArithmetic_defined generatedTheoryProofCheck).iff, eq_comm]

theorem eval_programZFVPProvableFormula_nat (φ : SetTheorySentence) :
    programZFVPProvableFormula.val.Evalb ![Encodable.encode φ] ↔ zfVPTheory ⊢ φ := by
  rw [eval_programZFVPProvableFormula]
  simpa only [arithmeticPair_nat, evalArithmetic_nat] using externalZFVP_programProof_iff φ

theorem models_programZFVPProvableFormula_quote (φ : SetTheorySentence) :
    M↓[ℒₒᵣ] ⊧ programZFVPProvableFormula.val/[⌜φ⌝] ↔
      ∃ p : M, generatedTheoryProofCheck.evalArithmetic (Arithmetic.pair (Encodable.encode φ : M) p) = 1 := by
  simpa [models_iff, Semiformula.eval_substs, gödelNumber'_eq_coe_encode,
    numeral_eq_natCast, Semiformula.Evalb] using
    eval_programZFVPProvableFormula (Encodable.encode φ : M)

theorem programZFVPProvability_D1 {φ : SetTheorySentence} (h : zfVPTheory ⊢ φ) :
    𝗜𝚺₁ ⊢ programZFVPProvableFormula.val/[⌜φ⌝] := by
  apply sigma_one_completeness (by simp)
  rw [models_programZFVPProvableFormula_quote]
  simpa only [natCast_nat, arithmeticPair_nat, evalArithmetic_nat] using
    (externalZFVP_programProof_iff φ).mpr h

def programZFVPProvability : Provability 𝗜𝚺₁ zfVPTheory where
  prov := programZFVPProvableFormula.val
  bew_def := programZFVPProvability_D1

instance programZFVPProvability_sound_nat : programZFVPProvability.SoundOn ℕ where
  sound_on {φ} h := by
    change ℕ↓[ℒₒᵣ] ⊧ programZFVPProvableFormula.val/[⌜φ⌝] at h
    have hp := (models_programZFVPProvableFormula_quote φ).mp h
    apply (externalZFVP_programProof_iff φ).mp
    simpa only [natCast_nat, arithmeticPair_nat, evalArithmetic_nat] using hp

theorem programZFVPProvability_con_models :
    M↓[ℒₒᵣ] ⊧ programZFVPProvability.con ↔ M↓[ℒₒᵣ] ⊧ programZFVPConsistencySentence := by
  simp only [Provability.con, models_iff, Semiformula.Realize,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
  change (¬M↓[ℒₒᵣ] ⊧ programZFVPProvableFormula.val/[⌜(⊥ : SetTheorySentence)⌝]) ↔ _
  rw [models_programZFVPProvableFormula_quote]
  change (¬∃ p : M, generatedTheoryProofCheck.evalArithmetic
    (Arithmetic.pair (Encodable.encode (⊥ : SetTheorySentence) : M) p) = 1) ↔
      programZFVPConsistencySentence.Evalb (![] : Fin 0 → M)
  simp only [eval_programZFVPConsistencySentence, evalArithmetic_programZFVPRefutation, not_exists]

theorem isigmaOne_proves_programZFVPConsistency_equiv :
    𝗜𝚺₁ ⊢ programZFVPProvability.con 🡘 programZFVPConsistencySentence :=
  complete 𝗜𝚺₁ _ fun (M : Type) _ _ ↦ by
    simpa [models_iff] using (programZFVPProvability_con_models (M := M))

end ZFVP
