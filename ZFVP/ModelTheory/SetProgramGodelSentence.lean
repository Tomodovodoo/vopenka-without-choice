import ZFVP.ModelTheory.SetProgramZFVPProvability
import ZFVP.ModelTheory.InternalFormulaRequirementEquations
import ZFVP.Syntax.SetDiagonalization

/-! A fixed sentence asserting its own unprovability by the explicit ZF+VP checker. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram ProvabilityAbstraction Entailment

def setProgramZFVPProvableFormula : SetTheorySemisentence 1 :=
  arithmeticInZF.translate programZFVPProvableFormula.val

def setProgramGodelSentence : SetTheorySentence := setFixedpoint (∼setProgramZFVPProvableFormula)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_setProgramZFVPProvableFormula (φ : SetTheorySentence) :
    setProgramZFVPProvableFormula.Evalb ![(Encodable.encode φ : V)] ↔
      V↓[ℒₛₑₜ] ⊧ setProgramZFVPProvable φ := by
  have h := internalArithmetic_evalb_translation (V := V) programZFVPProvableFormula.val
    ![(Encodable.encode φ : InternalArithmetic V)]
  have he : internalArithmeticVal ∘ ![(Encodable.encode φ : InternalArithmetic V)] =
      ![(Encodable.encode φ : V)] := by
    funext i
    exact Fin.cases (internalArithmeticVal_natCast _) (fun j ↦ Fin.elim0 j) i
  rw [he, eval_programZFVPProvableFormula] at h
  exact h.trans (models_setProgramZFVPProvable φ).symm

theorem zf_proves_setProgramZFVPProvableQuotation (φ : SetTheorySentence) :
    𝗭𝗙 ⊢ setNumeralSubstitution setProgramZFVPProvableFormula (Encodable.encode φ) 🡘
      setProgramZFVPProvable φ := by
  apply SetTheory.provable_of_models.{0}
  intro V _ _ _
  have h := (eval_setNumeralSubstitution (V := V) setProgramZFVPProvableFormula (Encodable.encode φ)).trans
    (eval_setProgramZFVPProvableFormula φ)
  simpa [models_iff] using h

theorem models_setProgramGodelSentence :
    V↓[ℒₛₑₜ] ⊧ setProgramGodelSentence ↔ ¬V↓[ℒₛₑₜ] ⊧ setProgramZFVPProvable setProgramGodelSentence := by
  rw [setProgramGodelSentence, models_setFixedpoint]
  simp only [Semiformula.Evalb, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
  change (¬setProgramZFVPProvableFormula.Evalb ![(Encodable.encode setProgramGodelSentence : V)]) ↔ _
  exact not_congr (eval_setProgramZFVPProvableFormula _)

theorem zf_proves_setProgramGodelSentence :
    𝗭𝗙 ⊢ setProgramGodelSentence 🡘 ∼setProgramZFVPProvable setProgramGodelSentence := by
  apply SetTheory.provable_of_models.{0}
  intro V _ _ _
  simpa [models_iff] using (models_setProgramGodelSentence (V := V))

theorem setProgramGodelSentence_unprovable [Consistent zfVPTheory] :
    zfVPTheory ⊬ setProgramGodelSentence := by
  let : 𝗭𝗙 ⪯ zfVPTheory := WeakerThan.ofSubset Set.subset_union_left
  intro h
  have hd : zfVPTheory ⊢ setProgramGodelSentence 🡘 ∼setProgramZFVPProvable setProgramGodelSentence :=
    WeakerThan.pbl zf_proves_setProgramGodelSentence
  have hp : zfVPTheory ⊢ setProgramZFVPProvable setProgramGodelSentence :=
    WeakerThan.pbl (setProgramZFVPProvability_D1 h)
  have hn := (K_left hd) ⨀ h
  exact Consistent.not_bot (𝓢 := zfVPTheory) ((N_iff_CO.mp hn) ⨀ hp)

end ZFVP
