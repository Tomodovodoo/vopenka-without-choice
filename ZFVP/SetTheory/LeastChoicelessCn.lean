import ZFVP.SetTheory.LeastChoicelessLastPoint
import ZFVP.SetTheory.CnCofinalUnbounded

/-! Mohammd Proposition 6.5(ii): the least relative extendible ordinal
is a limit of correct heights one level higher. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem leastChoiceless_high_lastPoint_embeddings {n : ℕ} {α γ : V}
    (hγ : IsLeastOrdinal (IsAlphaChoicelessExtendible (n + 1) α) γ)
    (ξ : V) [IsOrdinal ξ] : ∃ θ η f κ, ξ ∈ θ ∧ γ ∈ θ ∧ Cn (n + 2) θ ∧
      CnCofinal (n + 2) θ ∧ Cn (n + 1) η ∧
      IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f ∧
      IsCriticalPoint (hierarchy θ) f κ ∧ α ∈ κ ∧ θ ∈ f ‘ γ ∧ lastPoint θ f = γ := by
  let := hγ.1
  obtain ⟨β, hβ, hb⟩ := leastChoiceless_eventual_lastPoint hγ
  let := hβ
  let := ordinal_union_ordinal β γ
  let := ordinal_union_ordinal (β ∪ γ) ξ
  obtain ⟨θ, hbound, hθ, hlim⟩ := cnCofinal_unbounded n ((β ∪ γ) ∪ ξ)
  let := hθ.ordinal
  have hβγθ : β ∪ γ ∈ θ := ordinal_mem_of_subset_mem
    (fun x hx ↦ mem_union_iff.mpr (Or.inl hx)) hbound
  have hβθ : β ∈ θ := ordinal_mem_of_subset_mem
    (fun x hx ↦ mem_union_iff.mpr (Or.inl hx)) hβγθ
  have hγθ : γ ∈ θ := ordinal_mem_of_subset_mem
    (fun x hx ↦ mem_union_iff.mpr (Or.inr hx)) hβγθ
  have hξθ : ξ ∈ θ := ordinal_mem_of_subset_mem
    (fun x hx ↦ mem_union_iff.mpr (Or.inr hx)) hbound
  obtain ⟨η, f, κ, hη, hf, hc, hακ, hmove⟩ :=
    hγ.2.1.2.2 θ (hθ.of_le (by omega : n + 1 ≤ n + 2)) hγθ
  refine ⟨θ, η, f, κ, hξθ, hγθ, hθ, hlim, hη, hf, hc, hακ, hmove, ?_⟩
  exact hb θ η f κ (IsOrdinal.toIsTransitive.transitive _ hβθ) hθ hlim hη hγθ hf hc hακ hmove

theorem leastChoiceless_cnCofinal {n : ℕ} {α γ : V}
    (hγ : IsLeastOrdinal (IsAlphaChoicelessExtendible (n + 1) α) γ) :
    CnCofinal (n + 2) γ := by
  let := hγ.1
  obtain ⟨θ, η, f, κ, _, _, hθ, hlim, hη, hf, _, _, _, heq⟩ :=
    leastChoiceless_high_lastPoint_embeddings hγ γ
  exact heq ▸ rankEmbedding_lastPoint_cnCofinal hθ hη hf hlim

theorem leastChoiceless_cn {n : ℕ} {α γ : V}
    (hγ : IsLeastOrdinal (IsAlphaChoicelessExtendible (n + 1) α) γ) : Cn (n + 2) γ := by
  let := hγ.1
  exact cn_closed _ ⟨α, hγ.2.1.2.1⟩ (leastChoiceless_cnCofinal hγ)

end ZFVP
