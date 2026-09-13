import ZFVP.SetTheory.FiniteSets
import ZFVP.SetTheory.NaturalPredecessor
import ZFVP.SetTheory.FunctionValue

/-! The pigeonhole principle for internal naturals: an injection between sets with one fresh
point removed on each side, naturals compare in size exactly by inclusion, and no natural
injects its successor. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Removing a fresh point on both sides of an injection. -/
theorem cardLE_of_insert_cardLE_insert {A B x y : V} (hx : x ∉ A) (hy : y ∉ B)
    (h : insert x A ≤# insert y B) : A ≤# B := by
  obtain ⟨f, hf, hinj⟩ := h
  let := IsFunction.of_mem hf
  have hdf : domain f = insert x A := domain_eq_of_mem_function hf
  have hpair : ∀ a ∈ insert x A, ⟨a, f ‘ a⟩ₖ ∈ f := fun a ha ↦
    kpair_value_mem (by rw [hdf]; exact ha)
  have hfx : ∀ a ∈ insert x A, f ‘ a ∈ insert y B := fun a ha ↦ function_value_mem hf ha
  have hxA : x ∈ insert x A := mem_insert.mpr (Or.inl rfl)
  let g := {z ∈ A ×ˢ B ; (f ‘ (kpair.π₁ z) ≠ y ∧ kpair.π₂ z = f ‘ (kpair.π₁ z)) ∨
    (f ‘ (kpair.π₁ z) = y ∧ kpair.π₂ z = f ‘ x)}
  have hg : ∀ a b, ⟨a, b⟩ₖ ∈ g ↔ a ∈ A ∧ b ∈ B ∧
      ((f ‘ a ≠ y ∧ b = f ‘ a) ∨ (f ‘ a = y ∧ b = f ‘ x)) := by
    intro a b
    simp only [g, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]
  refine ⟨g, ?_, ?_⟩
  · apply mem_function.intro
    · intro z hz
      exact (mem_sep_iff.mp hz).1
    · intro a ha
      have haA : a ∈ insert x A := mem_insert.mpr (Or.inr ha)
      by_cases hya : f ‘ a = y
      · have hxa : x ≠ a := fun h ↦ hx (h ▸ ha)
        have hfxy : f ‘ x ≠ y := by
          intro h
          have h1 := hpair x hxA
          have h2 := hpair a haA
          rw [h] at h1
          rw [hya] at h2
          exact hxa (hinj x a y h1 h2)
        have hfxB : f ‘ x ∈ B := by
          rcases mem_insert.mp (hfx x hxA) with h | h
          · exact (hfxy h).elim
          · exact h
        refine ⟨f ‘ x, (hg _ _).mpr ⟨ha, hfxB, Or.inr ⟨hya, rfl⟩⟩, ?_⟩
        intro b hb
        rcases ((hg _ _).mp hb).2.2 with ⟨h, _⟩ | ⟨_, h⟩
        · exact (h hya).elim
        · exact h
      · have hfaB : f ‘ a ∈ B := by
          rcases mem_insert.mp (hfx a haA) with h | h
          · exact (hya h).elim
          · exact h
        refine ⟨f ‘ a, (hg _ _).mpr ⟨ha, hfaB, Or.inl ⟨hya, rfl⟩⟩, ?_⟩
        intro b hb
        rcases ((hg _ _).mp hb).2.2 with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact (hya h).elim
  · intro a₁ a₂ b h₁ h₂
    obtain ⟨ha₁, _, hc₁⟩ := (hg _ _).mp h₁
    obtain ⟨ha₂, _, hc₂⟩ := (hg _ _).mp h₂
    have hA₁ : a₁ ∈ insert x A := mem_insert.mpr (Or.inr ha₁)
    have hA₂ : a₂ ∈ insert x A := mem_insert.mpr (Or.inr ha₂)
    rcases hc₁ with ⟨hn₁, hb₁⟩ | ⟨he₁, hb₁⟩ <;> rcases hc₂ with ⟨hn₂, hb₂⟩ | ⟨he₂, hb₂⟩
    · have h1 := hpair a₁ hA₁
      have h2 := hpair a₂ hA₂
      rw [← hb₁] at h1
      rw [← hb₂] at h2
      exact hinj a₁ a₂ b h1 h2
    · have h1 := hpair a₁ hA₁
      have h2 := hpair x hxA
      rw [← hb₁] at h1
      rw [← hb₂] at h2
      exact (hx ((hinj a₁ x b h1 h2) ▸ ha₁)).elim
    · have h1 := hpair x hxA
      have h2 := hpair a₂ hA₂
      rw [← hb₁] at h1
      rw [← hb₂] at h2
      exact (hx ((hinj x a₂ b h1 h2).symm ▸ ha₂)).elim
    · have h1 := hpair a₁ hA₁
      have h2 := hpair a₂ hA₂
      rw [he₁] at h1
      rw [he₂] at h2
      exact hinj a₁ a₂ y h1 h2

/-- Naturals compare in size by inclusion. -/
theorem natural_subset_of_cardLE {n m : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (h : n ≤# m) : n ⊆ m := by
  revert n
  apply naturalNumber_induction (fun m ↦ ∀ n ∈ (ω : V), n ≤# m → n ⊆ m) (by definability) ?_ ?_ m hm
  · intro n _ h
    obtain ⟨f, hf, _⟩ := h
    intro a ha
    exact (not_mem_empty (function_value_mem hf ha)).elim
  · intro m hm ih n hn h
    rcases internalNatural_cases hn with rfl | ⟨k, hk, rfl⟩
    · exact empty_subset _
    · have : IsOrdinal k := IsOrdinal.of_mem hk
      have : IsOrdinal m := IsOrdinal.of_mem hm
      have hk' : k ⊆ m := ih k hk
        (cardLE_of_insert_cardLE_insert (mem_irrefl k) (mem_irrefl m) h)
      intro a ha
      rcases mem_succ_iff.mp ha with rfl | ha
      · rcases IsOrdinal.subset_iff.mp hk' with rfl | h
        · exact mem_succ_self _
        · exact mem_succ_iff.mpr (Or.inr h)
      · exact mem_succ_iff.mpr (Or.inr (hk' _ ha))

theorem not_succ_cardLE_self {n : V} (hn : n ∈ (ω : V)) : ¬succ n ≤# n := fun h ↦
  mem_irrefl n (natural_subset_of_cardLE (ω_succ_closed hn) hn h _ (mem_succ_self n))

/-- An internally finite set does not contain injective copies of all naturals. -/
theorem internallyFinite_not_all_cardLE {A : V} (hA : IsInternallyFinite A) :
    ∃ n ∈ (ω : V), ¬succ n ≤# A := by
  obtain ⟨n, hn, hAn⟩ := hA
  exact ⟨n, hn, fun h ↦ not_succ_cardLE_self hn (h.trans hAn.le)⟩

end ZFVP
