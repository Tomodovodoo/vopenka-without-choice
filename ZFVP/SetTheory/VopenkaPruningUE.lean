import ZFVP.SetTheory.LeastChoicelessCnExtendible
import ZFVP.SetTheory.VopenkaChoicelessExtendible

/-! Full VP and bounded nonzero rank-Berkeley cardinals imply unbounded
C(n)-extendibility at every positive standard level. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem vopenka_bounded_rankBerkeley_unboundedExtendibility
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (β : V) [IsOrdinal β] (hno : ∀ μ : V, β ∈ μ → ¬IsNonzeroRankBerkeley μ)
    (n : ℕ) (ξ : V) [IsOrdinal ξ] : ∃ γ : V, ξ ∈ γ ∧ IsCnExtendible (n + 1) γ := by
  let := ordinal_union_ordinal β ξ
  let α := (β ∪ ξ) ∪ (ω : V)
  let := ordinal_union_ordinal (β ∪ ξ) (ω : V)
  have hωα : (ω : V) ⊆ α := fun x hx ↦ mem_union_iff.mpr (Or.inr hx)
  have hβα : β ⊆ α := fun x hx ↦ mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inl hx)))
  have hξα : ξ ⊆ α := fun x hx ↦ mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inr hx)))
  obtain ⟨γ, hγ, _⟩ := vopenka_least_alphaChoicelessExtendible hVP (n + 1) α
  let := hγ.1
  have hext := leastChoiceless_cnExtendible_of_no_rankBerkeley hγ hωα (by
    intro μ hαμ hRB
    let := hRB.2.1.1
    exact hno μ (ordinal_mem_of_subset_mem hβα hαμ) hRB)
  exact ⟨γ, ordinal_mem_of_subset_mem hξα hγ.2.1.2.1, hext.predecessor⟩

theorem vopenka_no_rankBerkeley_unboundedExtendibility
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (hno : ∀ μ : V, ¬IsNonzeroRankBerkeley μ)
    (n : ℕ) (ξ : V) [IsOrdinal ξ] : ∃ γ : V, ξ ∈ γ ∧ IsCnExtendible (n + 1) γ :=
  vopenka_bounded_rankBerkeley_unboundedExtendibility hVP 0 (fun μ _ ↦ hno μ) n ξ

theorem vopenka_bounded_extendibility_unbounded_rankBerkeley
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (n : ℕ) (ξ : V) [IsOrdinal ξ]
    (hno : ∀ γ : V, ξ ∈ γ → ¬IsCnExtendible (n + 1) γ)
    (α : V) [IsOrdinal α] : ∃ μ : V, α ∈ μ ∧ IsNonzeroRankBerkeley μ := by
  classical
  by_contra hn
  have hbound : ∀ μ : V, α ∈ μ → ¬IsNonzeroRankBerkeley μ := fun μ hαμ hμ ↦ hn ⟨μ, hαμ, hμ⟩
  obtain ⟨γ, hξγ, hγ⟩ := vopenka_bounded_rankBerkeley_unboundedExtendibility hVP α hbound n ξ
  exact hno γ hξγ hγ

end ZFVP
