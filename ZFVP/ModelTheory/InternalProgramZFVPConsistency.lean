import ZFVP.Syntax.ProgramZFVPConsistency
import ZFVP.ModelTheory.InternalTheoryProofSoundness
import ZFVP.ModelTheory.ProtoRankBerkeleyConsistencySentence

/-! Proto rank-Berkeley rules out all refutations accepted by the explicit arithmetic checker. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem generatedTheoryProofCheck_no_refutation {U p : V}
    (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes) (hp : p ∈ (ω : V)) :
    generatedTheoryProofCheck.evalSet
      (naturalSquarePair (Encodable.encode (⊥ : SetTheorySentence) : V) p) ≠ 1 := by
  intro h
  have ht := (generatedTheoryProofCheck_sound_raw hU (by simp) hp h).2
  rw [decodedNaturalFormula_membership] at ht
  change Satisfies membershipLanguageCode ∅ (membershipStructureCode U) ∅ 0 falsityCode ∅ at ht
  exact not_satisfies_falsity membershipLanguageCode_valid (by simp [zero_def]) ht

theorem programZFVPConsistency_of_model {U : V} (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes) :
    programZFVPConsistencySentence.Evalb (![] : Fin 0 → InternalArithmetic V) := by
  rw [eval_programZFVPConsistencySentence]
  intro p hp
  rw [evalArithmetic_programZFVPRefutation] at hp
  have he := congrArg internalArithmeticVal hp
  rw [evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_natCast,
    internalArithmeticVal_one] at he
  exact generatedTheoryProofCheck_no_refutation hU (internalArithmeticVal_mem p) he

theorem IsProtoRankBerkeley.internalProgramZFVP_consistent {ζ δ : V} (hδ : IsProtoRankBerkeley ζ δ) :
    programZFVPConsistencySentence.Evalb (![] : Fin 0 → InternalArithmetic V) := by
  obtain ⟨Λ, _, _, _, _, hzf, hvp⟩ := hδ.exists_internalZF_codedVP
  exact programZFVPConsistency_of_model ((satisfiesOpenCodes_zfVP_iff (hierarchy Λ)).mpr ⟨hzf, hvp⟩)

theorem IsProtoRankBerkeley.models_programZFVPConsistency {ζ δ : V} (hδ : IsProtoRankBerkeley ζ δ) :
    V↓[ℒₛₑₜ] ⊧ arithmeticInZF.translate programZFVPConsistencySentence := by
  apply (internalArithmetic_translation programZFVPConsistencySentence).mpr
  simpa only [models_iff, Semiformula.Realize, Semiformula.Evalb] using hδ.internalProgramZFVP_consistent

def protoRankBerkeleyProgramConsistencySentence : SetTheorySentence :=
  protoRankBerkeleyExistenceSentence 🡒 arithmeticInZF.translate programZFVPConsistencySentence

theorem models_protoRankBerkeleyProgramConsistencySentence :
    V↓[ℒₛₑₜ] ⊧ protoRankBerkeleyProgramConsistencySentence := by
  have h : protoRankBerkeleyExistenceSentence.Evalb (![] : Fin 0 → V) →
      (arithmeticInZF.translate programZFVPConsistencySentence).Evalb (![] : Fin 0 → V) := by
    rw [eval_protoRankBerkeleyExistenceSentence]
    rintro ⟨ζ, δ, hδ⟩
    simpa only [models_iff, Semiformula.Realize, Semiformula.Evalb] using hδ.models_programZFVPConsistency
  simpa [models_iff, Semiformula.Realize, Semiformula.Evalb, protoRankBerkeleyProgramConsistencySentence] using h

theorem zf_proves_protoRankBerkeleyProgramConsistency : 𝗭𝗙 ⊢ protoRankBerkeleyProgramConsistencySentence :=
  provable_of_models 𝗭𝗙 protoRankBerkeleyProgramConsistencySentence
    (fun (M : Type) _ _ _ ↦ models_protoRankBerkeleyProgramConsistencySentence (V := M))

end ZFVP
