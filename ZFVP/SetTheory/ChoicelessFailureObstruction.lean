import ZFVP.SetTheory.ChoicelessFailureStructures
import ZFVP.SetTheory.ChoicelessFailureEmbedding

/-! Distinct structures in the failure class cannot be elementarily embedded. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem choicelessFailureStructures_no_embedding {n : ℕ} {α M N f : V}
    (hM : IsChoicelessFailureStructure (n + 1) (n + 2) α M)
    (hN : IsChoicelessFailureStructure (n + 1) (n + 2) α N) (hne : M ≠ N)
    (h : IsCodedElementaryEmbedding (namedMembershipLanguageCode (succ (succ α))) M N f) : False := by
  obtain ⟨σ, β, hσ, hβ, rfl⟩ := hM
  obtain ⟨τ, δ, hτ, hδ, rfl⟩ := hN
  let := hσ.1.1
  let := hτ.1.1
  let := hβ.1
  let := hδ.1
  let : IsOrdinal α := IsOrdinal.of_mem hσ.1.2.1
  let := hierarchy_transitive β
  let := hierarchy_transitive δ
  have hαβ := hβ.2.1.2.1.2.1
  have hαδ := hδ.2.1.2.1.2.1
  have hσβ := hβ.2.1.1
  have hτδ := hδ.2.1.1
  have hc := choicelessFailureNames_mem hαβ hσβ
  have hf := h.membership_reduct
    (choicelessFailureStructure_expansion hαβ hσβ)
    (choicelessFailureStructure_expansion hαδ hτδ)
  simp only [choicelessFailureStructure_domain] at hf
  have hmarker : f ‘ σ = τ := by
    have hm := h.named_values hc (mem_succ_self (succ α))
    simpa only [choicelessFailureNames_marker] using hm
  have hfix : ∀ i ∈ succ α, f ‘ i = i := by
    intro i hi
    have hm := h.named_values hc (mem_succ_iff.mpr (Or.inr hi))
    simpa only [choicelessFailureNames_fixed α σ hi, choicelessFailureNames_fixed α τ hi] using hm
  have hστ : σ ≠ τ := by
    intro he
    have hδ' : IsNextChoicelessFailureStage (n + 1) (n + 2) α σ δ := by rwa [he]
    have heβ := hβ.unique hδ'
    apply hne
    rw [he, heβ]
  have hσV := ordinal_subset_hierarchy β σ hσβ
  have hσfle := hf.ordinal_subset_value hσ.1.1 hσV
  rw [hmarker] at hσfle
  have hστmem : σ ∈ τ := (IsOrdinal.subset_iff.mp hσfle).resolve_left hστ
  have hbig : β ⊆ f ‘ σ := by
    rw [hmarker]
    exact hβ.no_between hτ hστmem
  have hmove : f ‘ σ ≠ σ := by rw [hmarker]; exact hστ.symm
  obtain ⟨κ, hκ, _⟩ := rankEmbedding_criticalPoint_existsUnique
    hβ.2.1.2.2 hδ.2.1.2.2 hf ⟨σ, hσV, hmove⟩
  let := hκ.ordinal
  have hακ : α ∈ κ := by
    rcases IsOrdinal.mem_trichotomy κ α with hlt | he | hgt
    · exact False.elim (hκ.moved (hfix κ (mem_succ_iff.mpr (Or.inr hlt))))
    · exact False.elim (hκ.moved (hfix κ (mem_succ_iff.mpr (Or.inl he))))
    · exact hgt
  exact choicelessFailureLimit_no_embedding hβ.2.1.2.1 hβ.2.1.2.2 hδ.2.1.2.2
    hf hκ hακ hσ.1.2.1 hσβ hbig

end ZFVP
