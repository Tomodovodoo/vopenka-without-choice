import ZFVP.Syntax.ProgramZFVPProvabilityD2
import ZFVP.ModelTheory.InternalArithmeticGraphs

/-! Derivability for the explicit proof predicate after interpreting arithmetic in ZF. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram ProvabilityAbstraction

def setProgramZFVPProvable (φ : SetTheorySentence) : SetTheorySentence :=
  arithmeticInZF.translate (programZFVPProvability φ)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem models_setProgramZFVPProvable (φ : SetTheorySentence) :
    V↓[ℒₛₑₜ] ⊧ setProgramZFVPProvable φ ↔
      ProgramTheoryProvable (Encodable.encode φ : InternalArithmetic V) := by
  rw [setProgramZFVPProvable, internalArithmetic_translation]
  exact models_programZFVPProvableFormula_quote φ

theorem setProgramZFVPProvability_D1 {φ : SetTheorySentence} (h : zfVPTheory ⊢ φ) :
    𝗭𝗙 ⊢ setProgramZFVPProvable φ := by
  apply SetTheory.provable_of_models.{0}
  intro V _ _ _
  rw [setProgramZFVPProvable, internalArithmetic_translation]
  exact models_of_provable (M := InternalArithmetic V) inferInstance (programZFVPProvability_D1 h)

theorem setProgramZFVPProvability_D2 (φ ψ : SetTheorySentence) :
    𝗭𝗙 ⊢ setProgramZFVPProvable (φ 🡒 ψ) 🡒
      setProgramZFVPProvable φ 🡒 setProgramZFVPProvable ψ := by
  apply SetTheory.provable_of_models.{0}
  intro V _ _ _
  have h : (V↓[ℒₛₑₜ] ⊧ setProgramZFVPProvable (φ 🡒 ψ)) →
      (V↓[ℒₛₑₜ] ⊧ setProgramZFVPProvable φ) →
      (V↓[ℒₛₑₜ] ⊧ setProgramZFVPProvable ψ) := by
    simp only [models_setProgramZFVPProvable]
    exact ProgramTheoryProvable.modusPonens φ ψ
  simpa [models_iff] using h

theorem models_setProgramZFVPConsistency :
    V↓[ℒₛₑₜ] ⊧ ∼setProgramZFVPProvable ⊥ ↔
      V↓[ℒₛₑₜ] ⊧ arithmeticInZF.translate programZFVPConsistencySentence := by
  have h := programZFVPProvability_con_models (M := InternalArithmetic V)
  simpa only [setProgramZFVPProvable, ← LogicalConnective.HomClass.map_neg,
    internalArithmetic_translation, Provability.con] using h

theorem zf_proves_setProgramZFVPConsistency_equiv :
    𝗭𝗙 ⊢ (∼setProgramZFVPProvable ⊥) 🡘 arithmeticInZF.translate programZFVPConsistencySentence := by
  apply SetTheory.provable_of_models.{0}
  intro V _ _ _
  simpa [models_iff] using (models_setProgramZFVPConsistency (V := V))

end ZFVP
