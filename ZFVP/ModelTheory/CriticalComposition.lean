import ZFVP.ModelTheory.CriticalPoint

/-! Critical points above a fixed ordinal for compositions of elementary graphs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem criticalPoint_exists_above {A f α : V} [IsTransitive A] [IsOrdinal α]
    (hm : ∃ ξ, IsOrdinal ξ ∧ ξ ∈ A ∧ f ‘ ξ ≠ ξ)
    (hfix : ∀ ξ, IsOrdinal ξ → ξ ∈ A → ξ ⊆ α → f ‘ ξ = ξ) :
    ∃ κ, IsCriticalPoint A f κ ∧ α ∈ κ := by
  obtain ⟨κ, hκ, _⟩ := leastOrdinal_existsUnique (fun ξ ↦ ξ ∈ A ∧ f ‘ ξ ≠ ξ)
    (by definability) hm
  have hc : IsCriticalPoint A f κ := hκ
  let := hc.ordinal
  refine ⟨κ, hc, ?_⟩
  rcases IsOrdinal.mem_trichotomy κ α with hl | he | hg
  · exact False.elim (hc.moved (hfix κ hc.ordinal hc.mem_domain
      (IsOrdinal.toIsTransitive.transitive κ hl)))
  · exact False.elim (hc.moved (hfix κ hc.ordinal hc.mem_domain (subset_of_eq he)))
  · exact hg

namespace IsCodedMembershipEmbedding

variable {A B C f g α : V} [IsTransitive A] [IsTransitive B] [IsTransitive C]

theorem comp_moves_left (hf : IsCodedMembershipEmbedding A B f)
    (hg : IsCodedMembershipEmbedding B C g) {ξ : V} (ho : IsOrdinal ξ)
    (hx : ξ ∈ A) (hm : f ‘ ξ ≠ ξ) : (compose f g) ‘ ξ ≠ ξ := by
  let := ho
  let := hf.value_ordinal ho hx
  have hlt : ξ ∈ f ‘ ξ := by
    rcases IsOrdinal.subset_iff.mp (hf.ordinal_subset_value ho hx) with he | hl
    · exact False.elim (hm he.symm)
    · exact hl
  have hle := hg.ordinal_subset_value (hf.value_ordinal ho hx)
    (function_value_mem hf.function hx)
  rw [value_compose_of_mem_function hf.function hg.function hx]
  intro he
  have hh := hle ξ hlt
  rw [he] at hh
  exact mem_irrefl ξ hh

theorem comp_criticalPoint_above (hf : IsCodedMembershipEmbedding A B f)
    (hg : IsCodedMembershipEmbedding B C g) [IsOrdinal α]
    (hm : ∃ ξ, IsOrdinal ξ ∧ ξ ∈ A ∧ f ‘ ξ ≠ ξ)
    (hfixf : ∀ ξ, IsOrdinal ξ → ξ ∈ A → ξ ⊆ α → f ‘ ξ = ξ)
    (hfixg : ∀ ξ, IsOrdinal ξ → ξ ∈ B → ξ ⊆ α → g ‘ ξ = ξ) :
    ∃ κ, IsCriticalPoint A (compose f g) κ ∧ α ∈ κ := by
  apply criticalPoint_exists_above
  · obtain ⟨ξ, ho, hx, hm⟩ := hm
    exact ⟨ξ, ho, hx, hf.comp_moves_left hg ho hx hm⟩
  · intro ξ ho hx hle
    have hfξ := hfixf ξ ho hx hle
    have hξB : ξ ∈ B := hfξ ▸ function_value_mem hf.function hx
    rw [value_compose_of_mem_function hf.function hg.function hx, hfξ,
      hfixg ξ ho hξB hle]

end IsCodedMembershipEmbedding

end ZFVP
