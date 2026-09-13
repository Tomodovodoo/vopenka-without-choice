import ZFVP.ModelTheory.RankEmbeddingAction
import ZFVP.Syntax.DictionaryComplexity

/-! Finite dictionary bounds transfer arbitrary definable relations between correct rank stages. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_defined_iff {k : ℕ} {δ ε f : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (k + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    {p : LevyPolarity} {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula p (k + 1) φ) (R : (Fin n → V) → Prop) [Defined R φ]
    (v : Fin n → V) (hv : ∀ i, v i ∈ hierarchy δ) :
    R v ↔ R (fun i ↦ f ‘ (v i)) := by
  let b : Fin n → SetDomain (hierarchy δ) := fun i ↦ ⟨v i, hv i⟩
  have hs := hδ.defined_correct hφ R b
  have ht := hε.defined_correct hφ R (h.toFunction ∘ b)
  exact hs.symm.trans ((h.eval_semisentence φ b).trans ht)

theorem rankEmbedding_coreDictionary_iff {k : ℕ} {δ ε f : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (k + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hk : coreSyntaxDictionaryBound ≤ k + 1) {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ coreSyntaxDictionary) (R : (Fin n → V) → Prop) [Defined R φ]
    (v : Fin n → V) (hv : ∀ i, v i ∈ hierarchy δ) :
    R v ↔ R (fun i ↦ f ‘ (v i)) :=
  rankEmbedding_defined_iff hδ hε h ((coreSyntaxDictionary_complexity hφ .pi).mono hk) R v hv

end ZFVP
