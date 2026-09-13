import ZFVP.SetTheory.OrdinalMultiplication

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinalBlockCode_injective {α β i j k l : V} [IsOrdinal α] [IsOrdinal β]
    (hi : i ∈ β) (hj : j ∈ α) (hk : k ∈ β) (hl : l ∈ α)
    (he : ordinalAdd (ordinalMul α i) j = ordinalAdd (ordinalMul α k) l) :
    i = k ∧ j = l := by
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hk
  let := IsOrdinal.of_mem hl
  have hsep {u v w t : V} [IsOrdinal v] [IsOrdinal w] [IsOrdinal t]
      (hu : u ∈ α) (hvw : v ∈ w) :
      ordinalAdd (ordinalMul α v) u ∈ ordinalAdd (ordinalMul α w) t :=
    subset_ordinalAdd _ _ _ (ordinalMul_block_subset hvw _ (ordinalAdd_mem hu))
  have hik : i = k := by
    rcases IsOrdinal.mem_trichotomy i k with h | h | h
    · have hh := hsep (t := l) hj h
      rw [he] at hh
      exact False.elim (mem_irrefl _ hh)
    · exact h
    · have hh := hsep (t := j) hl h
      rw [he] at hh
      exact False.elim (mem_irrefl _ hh)
  refine ⟨hik, ?_⟩
  rw [hik] at he
  exact ordinalAdd_right_injective he

theorem ordinal_prod_cardLE_mul (α β : V) [IsOrdinal α] [IsOrdinal β] :
    (β ×ˢ α) ≤# ordinalMul α β := by
  let F : V → V := fun p ↦ ordinalAdd (ordinalMul α (kpair.π₁ p)) (kpair.π₂ p)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let f := definableGraph (β ×ˢ α) F hF
  have hf : f ∈ (ordinalMul α β) ^ (β ×ˢ α) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (by
      intro p hp
      obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hp
      let := IsOrdinal.of_mem hi
      let := IsOrdinal.of_mem hj
      simpa only [F, kpair.π₁_kpair, kpair.π₂_kpair] using
        ordinalMul_block_subset (α := α) hi _ (ordinalAdd_mem (α := ordinalMul α i) hj))
  refine ⟨f, hf, ?_⟩
  intro p q z hp hq
  obtain ⟨hpD, hzp⟩ := (pair_mem_definableGraph_iff _ F hF p z).mp hp
  obtain ⟨hqD, hzq⟩ := (pair_mem_definableGraph_iff _ F hF q z).mp hq
  obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hpD
  obtain ⟨k, hk, l, hl, rfl⟩ := mem_prod_iff.mp hqD
  have he : ordinalAdd (ordinalMul α i) j = ordinalAdd (ordinalMul α k) l := by
    simpa only [F, kpair.π₁_kpair, kpair.π₂_kpair] using hzp.symm.trans hzq
  exact kpair_iff.mpr (ordinalBlockCode_injective hi hj hk hl he)

def IsCardinalSmall (κ A : V) : Prop := ∃ α ∈ κ, A ≤# α

def cardinalSmallFormula : SetTheorySemisentence 2 := f“κ A. ∃ α ∈ κ, !CardLE.dfn A α”

instance cardinalSmallFormula_defined :
    ℒₛₑₜ-relation[V] IsCardinalSmall via cardinalSmallFormula :=
  ⟨fun v ↦ by simp [cardinalSmallFormula, IsCardinalSmall]⟩

instance isCardinalSmall_definable : ℒₛₑₜ-relation[V] IsCardinalSmall :=
  cardinalSmallFormula_defined.to_definable

theorem IsCardinalSmall.of_cardLE {κ A B : V} (hB : IsCardinalSmall κ B) (h : A ≤# B) :
    IsCardinalSmall κ A := by
  obtain ⟨α, hα, hBα⟩ := hB
  exact ⟨α, hα, h.trans hBα⟩

theorem IsCardinalSmall.subset {κ A B : V} (hB : IsCardinalSmall κ B) (h : A ⊆ B) :
    IsCardinalSmall κ A := hB.of_cardLE (cardLE_of_subset h)

theorem regularCardinal_ordinal_prod_small {κ α β : V} (hκ : IsRegularCardinal κ)
    (hα : α ∈ κ) (hβ : β ∈ κ) : IsCardinalSmall κ (β ×ˢ α) := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hα
  let := IsOrdinal.of_mem hβ
  exact ⟨ordinalMul α β, regularCardinal_ordinalMul_closed hκ hα hβ,
    ordinal_prod_cardLE_mul α β⟩

end ZFVP
