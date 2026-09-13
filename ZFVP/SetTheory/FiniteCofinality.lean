import ZFVP.SetTheory.CofinalityDictionary

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinal_union_mem {α x y : V} [IsOrdinal α] (hx : x ∈ α) (hy : y ∈ α) : x ∪ y ∈ α := by
  have : IsOrdinal x := IsOrdinal.of_mem hx
  have : IsOrdinal y := IsOrdinal.of_mem hy
  rcases IsOrdinal.subset_or_supset x y with h | h
  · rw [union_eq_iff_left.mpr h]
    exact hy
  · rw [union_eq_iff_right.mpr h]
    exact hx

theorem finite_map_bounded (α : V) [IsOrdinal α] (hz : (0 : V) ∈ α)
    (hs : ∀ ξ ∈ α, succ ξ ∈ α) :
    ∀ n ∈ (ω : V), ∀ f ∈ α ^ n, ∃ ξ ∈ α, ∀ i ∈ n, f ‘ i ∈ ξ := by
  apply naturalNumber_induction
    (fun n ↦ ∀ f ∈ α ^ n, ∃ ξ ∈ α, ∀ i ∈ n, f ‘ i ∈ ξ) (by definability)
  · intro f _
    exact ⟨0, hz, fun _ hi ↦ False.elim (not_mem_empty hi)⟩
  · intro n hn ih f hf
    have : IsFunction f := IsFunction.of_mem hf
    have hsub : n ⊆ succ n := by intro i hi; exact mem_succ_iff.mpr (Or.inr hi)
    have hr : f ↾ n ∈ α ^ n := restrict_mem_function_of_values
      (by simpa only [domain_eq_of_mem_function hf] using hsub)
      (fun i hi ↦ function_value_mem hf (hsub i hi))
    obtain ⟨ξ, hξ, hbound⟩ := ih (f ↾ n) hr
    have hn' : n ∈ succ n := by simp
    have hv := function_value_mem hf hn'
    refine ⟨ξ ∪ succ (f ‘ n), ordinal_union_mem hξ (hs _ hv), ?_⟩
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact mem_union_iff.mpr (Or.inr (by simp))
    · apply mem_union_iff.mpr
      left
      have h := hbound i hi
      rw [value_restrict (by simpa only [domain_eq_of_mem_function hf] using hsub i hi) hi] at h
      exact h

theorem infinite_cofinality_of_succ_closed (α : V) [IsOrdinal α] (hz : (0 : V) ∈ α)
    (hs : ∀ ξ ∈ α, succ ξ ∈ α) : (ω : V) ⊆ internalCofinality α := by
  rcases IsOrdinal.subset_or_supset (ω : V) (internalCofinality α) with h | h
  · exact h
  rcases IsOrdinal.subset_iff.mp h with heq | hlt
  · exact heq ▸ subset_refl _
  obtain ⟨f, hf⟩ := cofinalMap_exists α
  obtain ⟨ξ, hξ, hbound⟩ := finite_map_bounded α hz hs _ hlt f hf.1
  obtain ⟨i, hi, hξi⟩ := hf.2 ξ hξ
  exact False.elim (mem_irrefl (f ‘ i) (hξi _ (hbound i hi)))

theorem internalCofinality_omega : internalCofinality (ω : V) = ω :=
  SetTheory.subset_antisymm (internalCofinality_subset _)
    (infinite_cofinality_of_succ_closed _ (by simp) (fun _ h ↦ ω_succ_closed h))

theorem omega_regular : IsRegularCardinal (ω : V) := by
  have h := internalCofinality_initial (ω : V)
  rw [internalCofinality_omega] at h
  exact ⟨h, subset_refl _, internalCofinality_omega⟩

theorem regularCardinal_succ_closed {κ ξ : V} (hκ : IsRegularCardinal κ) (hξ : ξ ∈ κ) :
    succ ξ ∈ κ := by
  have : IsOrdinal κ := hκ.1.1
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hs : succ ξ ⊆ κ := by
    intro x hx
    rcases mem_succ_iff.mp hx with rfl | hx
    · exact hξ
    · exact IsOrdinal.toIsTransitive.transitive ξ hξ x hx
  rcases IsOrdinal.subset_iff.mp hs with heq | hlt
  · have hone : κ = 1 := calc
      κ = internalCofinality κ := hκ.2.2.symm
      _ = internalCofinality (succ ξ) := congrArg internalCofinality heq.symm
      _ = 1 := internalCofinality_succ ξ
    have hm : (1 : V) ∈ κ := hκ.2.1 _ (by simp)
    rw [hone] at hm
    exact False.elim (mem_irrefl _ hm)
  · exact hlt

end ZFVP
