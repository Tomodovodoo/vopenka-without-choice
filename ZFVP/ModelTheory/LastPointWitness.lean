import ZFVP.ModelTheory.LastPointSupercompact
import ZFVP.SetTheory.ChoicelessSupercompactExtendible

/-! Arbitrarily high embeddings with a fixed last point yield global
choiceless supercompactness at that last point. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def LastPointWitness (n : ℕ) (α δ θ : V) : Prop :=
  Cn (n + 2) θ ∧ CnCofinal (n + 2) θ ∧ δ ∈ θ ∧ ∃ η f κ,
    Cn (n + 1) η ∧ IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f ∧
    IsCriticalPoint (hierarchy θ) f κ ∧ α ∈ κ ∧ lastPoint θ f = δ

instance lastPointWitness_definable (n : ℕ) : ℒₛₑₜ-relation₃[V] (LastPointWitness n) := by
  unfold LastPointWitness
  definability

theorem lastPointWitness_unbounded_supercompact {n : ℕ} {α δ : V} [IsOrdinal δ]
    (h : ∀ β, IsOrdinal β → ∃ θ, β ∈ θ ∧ LastPointWitness n α δ θ) :
    IsAlphaChoicelessSupercompact (n + 2) α δ := by
  have hαδ : α ∈ δ := by
    obtain ⟨θ, _, hθ, _, _, η, f, κ, hη, hf, hc, hακ, heq⟩ := h δ inferInstance
    have hsub := hc.subset_lastPoint hθ hη hf
    rw [heq] at hsub
    exact hsub α hακ
  refine ⟨inferInstance, hαδ, ?_⟩
  intro μ hμ hδμ a ha
  obtain ⟨θ, hμθ, hθ, hlim, hδθ, η, f, κ, hη, hf, hc, hακ, heq⟩ := h μ hμ.ordinal
  have hs := rankEmbedding_lastPoint_supercompactBelow hθ hη hf hc hακ hlim
    (heq.symm ▸ hδθ)
  rw [heq] at hs
  exact hs μ hμ hδμ hμθ a ha

end ZFVP
