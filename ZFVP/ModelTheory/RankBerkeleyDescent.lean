import ZFVP.SetTheory.RankBerkeley
import ZFVP.ModelTheory.InternalProgramZFVPConsistency
import ZFVP.ModelTheory.CodedZFVPExternal

/-! Rank-Berkeley descent and its arithmetic consistency implication, with nonzero explicit. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def nonzeroRankBerkeleyProgramConsistencySentence : SetTheorySentence :=
  nonzeroRankBerkeleyExistenceSentence 🡒 arithmeticInZF.translate programZFVPConsistencySentence

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsNonzeroRankBerkeley.externalZFUEVP_model_above {δ ζ : V}
    (hδ : IsNonzeroRankBerkeley δ) (hζ : ζ ∈ δ) :
    ∃ Λ : V, IsOrdinal Λ ∧ Λ ⊆ δ ∧ ζ ∈ Λ ∧ internalCofinality Λ = (ω : V) ∧
      ∃ hN : Nonempty (SetDomain (hierarchy Λ)),
        letI := hN; (SetDomain (hierarchy Λ))↓[ℒₛₑₜ] ⊧* zfUEVPTheory :=
  (hδ.proto hζ).externalZFUEVP_model

theorem IsNonzeroRankBerkeley.exists_internalZF_codedVP {δ : V} (hδ : IsNonzeroRankBerkeley δ) :
    ∃ Λ : V, IsOrdinal Λ ∧ Λ ⊆ δ ∧ (0 : V) ∈ Λ ∧ internalCofinality Λ = (ω : V) ∧
      IsInternalZFModel (hierarchy Λ) ∧
      ∀ φ, IsMembershipFormulaCode (2 : V) φ → MembershipSatisfies (hierarchy Λ) 0 (vopenkaCode φ) ∅ :=
  hδ.proto_zero.exists_internalZF_codedVP

theorem IsNonzeroRankBerkeley.externalZFUEVP_consistent {δ : V} (hδ : IsNonzeroRankBerkeley δ) :
    Entailment.Consistent zfUEVPTheory := hδ.proto_zero.externalZFUEVP_consistent

theorem IsNonzeroRankBerkeley.internalProgramZFVP_consistent {δ : V} (hδ : IsNonzeroRankBerkeley δ) :
    programZFVPConsistencySentence.Evalb (![] : Fin 0 → InternalArithmetic V) :=
  hδ.proto_zero.internalProgramZFVP_consistent

theorem IsNonzeroRankBerkeley.models_programZFVPConsistency {δ : V} (hδ : IsNonzeroRankBerkeley δ) :
    V↓[ℒₛₑₜ] ⊧ arithmeticInZF.translate programZFVPConsistencySentence :=
  hδ.proto_zero.models_programZFVPConsistency

theorem models_nonzeroRankBerkeleyProgramConsistencySentence :
    V↓[ℒₛₑₜ] ⊧ nonzeroRankBerkeleyProgramConsistencySentence := by
  have h : nonzeroRankBerkeleyExistenceSentence.Evalb (![] : Fin 0 → V) →
      (arithmeticInZF.translate programZFVPConsistencySentence).Evalb (![] : Fin 0 → V) := by
    rw [eval_nonzeroRankBerkeleyExistenceSentence]
    rintro ⟨δ, hδ⟩
    simpa only [models_iff, Semiformula.Realize, Semiformula.Evalb] using hδ.models_programZFVPConsistency
  simpa [models_iff, Semiformula.Realize, Semiformula.Evalb,
    nonzeroRankBerkeleyProgramConsistencySentence] using h

theorem zf_proves_nonzeroRankBerkeleyProgramConsistency : 𝗭𝗙 ⊢ nonzeroRankBerkeleyProgramConsistencySentence :=
  provable_of_models 𝗭𝗙 nonzeroRankBerkeleyProgramConsistencySentence
    (fun (M : Type) _ _ _ ↦ models_nonzeroRankBerkeleyProgramConsistencySentence (V := M))

end ZFVP
