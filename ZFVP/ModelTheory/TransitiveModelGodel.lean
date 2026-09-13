import ZFVP.ModelTheory.TransitiveZFArithmeticEquiv
import ZFVP.ModelTheory.SetProgramGodelSentence
import ZFVP.ModelTheory.InternalTheoryProofSoundness
import ZFVP.ModelTheory.InternalZFExternal

/-! A transitive model of all internal ZF+VP axioms yields the explicit Goedel sentence. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem setProgramZFVPProvable_model_sound {U : V} [Nonempty (SetDomain U)]
    (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes) (φ : SetTheorySentence)
    (hφ : V↓[ℒₛₑₜ] ⊧ setProgramZFVPProvable φ) : (SetDomain U)↓[ℒₛₑₜ] ⊧ φ := by
  obtain ⟨p, hp⟩ := (models_setProgramZFVPProvable φ).mp hφ
  have he := congrArg internalArithmeticVal hp
  rw [evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_natCast,
    internalArithmeticVal_one] at he
  have ht := (generatedTheoryProofCheck_sound_raw hU (by simp) (internalArithmeticVal_mem p) he).2
  rw [decodedNaturalFormula_membership] at ht
  have hs := membershipSatisfies_encode hU.1 φ (![] : Fin 0 → SetDomain U)
  apply (show φ.Evalb (![] : Fin 0 → SetDomain U) → (SetDomain U)↓[ℒₛₑₜ] ⊧ φ from fun h ↦ h)
  apply hs.mp
  simpa only [standardTuple, zero_def, show ((0 : ℕ) : V) = ∅ from rfl] using ht

theorem transitiveZFVP_model_impliesGodel {U : V} [IsTransitive U] [Nonempty (SetDomain U)]
    (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes) : V↓[ℒₛₑₜ] ⊧ setProgramGodelSentence := by
  let hZF := ((satisfiesOpenCodes_zfVP_iff U).mp hU).1.models_zf
  apply models_setProgramGodelSentence.mpr
  intro hp
  have hG := setProgramZFVPProvable_model_sound hU setProgramGodelSentence hp
  have hn := (models_setProgramGodelSentence (V := SetDomain U)).mp hG
  apply hn
  exact (TransitiveZF.arithmetic_translation_absolute U _).mpr hp

end ZFVP
