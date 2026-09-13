import ZFVP.SetTheory.ProperClassRanks
import ZFVP.ModelTheory.CodedElementaryEmbedding

/-! Parameterized Vopenka instances for arbitrary internal set-sized languages. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def vopenkaSentence (φ : SetTheorySemisentence 2) : SetTheorySentence :=
  “∀ L a,
    (∀ A, ∃ M, !φ M a ∧ M ∉ A) →
    (∀ M, !φ M a → !isStructureCodeFormula L M) →
    ∃ M N f, M ≠ N ∧ !φ M a ∧ !φ N a ∧ !codedElementaryEmbeddingFormula L M N f”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def VopenkaInstance (φ : SetTheorySemisentence 2) : Prop :=
  ∀ L a : V, IsProperClass (fun M ↦ φ.Evalb ![M, a]) →
    (∀ M : V, φ.Evalb ![M, a] → IsStructureCode L M) →
    ∃ M N f : V, M ≠ N ∧ φ.Evalb ![M, a] ∧ φ.Evalb ![N, a] ∧ IsCodedElementaryEmbedding L M N f

theorem eval_vopenkaSentence (φ : SetTheorySemisentence 2) :
    V↓[ℒₛₑₜ] ⊧ vopenkaSentence φ ↔ VopenkaInstance (V := V) φ := by
  change (vopenkaSentence φ).Evalb (![] : Fin 0 → V) ↔ _
  simp [vopenkaSentence, VopenkaInstance, IsProperClass]

end ZFVP
