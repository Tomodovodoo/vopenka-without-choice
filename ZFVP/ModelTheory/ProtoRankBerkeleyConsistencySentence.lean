import ZFVP.ModelTheory.UniformCodedSequentProofs
import ZFVP.ModelTheory.ProtoRankBerkeleyCodedConsistency

/-! ZF proves the fixed sentence asserting coded consistency from proto rank-Berkeley. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def protoRankBerkeleyExistenceSentence : SetTheorySentence :=
  “∃ ζ δ, !protoRankBerkeleyFormula ζ δ”

def protoRankBerkeleyConsistencySentence : SetTheorySentence :=
  protoRankBerkeleyExistenceSentence 🡒 codedZFVPConsistencySentence

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem eval_protoRankBerkeleyExistenceSentence :
    protoRankBerkeleyExistenceSentence.Evalb (![] : Fin 0 → V) ↔ ∃ ζ δ : V, IsProtoRankBerkeley ζ δ := by
  simp [protoRankBerkeleyExistenceSentence]

theorem IsProtoRankBerkeley.models_codedZFVPConsistency {ζ δ : V} (hδ : IsProtoRankBerkeley ζ δ) :
    V↓[ℒₛₑₜ] ⊧ codedZFVPConsistencySentence := by
  simpa only [models_iff, Semiformula.Realize, Semiformula.Evalb, ← eval_codedZFVPConsistencySentence] using
    hδ.codedZFVP_consistent

theorem models_protoRankBerkeleyConsistencySentence :
    V↓[ℒₛₑₜ] ⊧ protoRankBerkeleyConsistencySentence := by
  have h : protoRankBerkeleyExistenceSentence.Evalb (![] : Fin 0 → V) →
      codedZFVPConsistencySentence.Evalb (![] : Fin 0 → V) := by
    rw [eval_protoRankBerkeleyExistenceSentence, eval_codedZFVPConsistencySentence]
    rintro ⟨ζ, δ, hδ⟩
    exact hδ.codedZFVP_consistent
  simpa [models_iff, Semiformula.Realize, Semiformula.Evalb, protoRankBerkeleyConsistencySentence] using h

theorem zf_proves_protoRankBerkeleyConsistency : 𝗭𝗙 ⊢ protoRankBerkeleyConsistencySentence :=
  provable_of_models 𝗭𝗙 protoRankBerkeleyConsistencySentence
    (fun (M : Type) _ _ _ ↦ models_protoRankBerkeleyConsistencySentence (V := M))

end ZFVP
