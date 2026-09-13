import ZFVP.SetTheory.OrdinalTriangle

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open Classical

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def ordinalPairRow (x y : V) : V := if x ∈ y then y else x

instance ordinalPairRow_definable : ℒₛₑₜ-function₂[V] ordinalPairRow := by
  have hd : ℒₛₑₜ-relation₃ (fun z x y : V ↦
      (x ∈ y ∧ z = y) ∨ (x ∉ y ∧ z = x)) := by definability
  apply Language.Definable.of_iff hd
  intro v
  by_cases h : v 1 ∈ v 2 <;> simp [ordinalPairRow, h]

noncomputable def ordinalPairCode (x y : V) : V :=
  if x ∈ y then ordinalAdd (ordinalTriangle y) x
  else ordinalAdd (ordinalTriangle x) (ordinalAdd x y)

instance ordinalPairCode_definable : ℒₛₑₜ-function₂[V] ordinalPairCode := by
  have hd : ℒₛₑₜ-relation₃ (fun z x y : V ↦
      (x ∈ y ∧ z = ordinalAdd (ordinalTriangle y) x) ∨
      (x ∉ y ∧ z = ordinalAdd (ordinalTriangle x) (ordinalAdd x y))) := by definability
  apply Language.Definable.of_iff hd
  intro v
  by_cases h : v 1 ∈ v 2 <;> simp [ordinalPairCode, h]

instance ordinalPairRow_ordinal (x y : V) [IsOrdinal x] [IsOrdinal y] :
    IsOrdinal (ordinalPairRow x y) := by
  unfold ordinalPairRow
  split_ifs <;> infer_instance

instance ordinalPairCode_ordinal (x y : V) [IsOrdinal x] [IsOrdinal y] :
    IsOrdinal (ordinalPairCode x y) := by
  unfold ordinalPairCode
  split_ifs <;> infer_instance

theorem ordinalPairCode_bounds (x y : V) [IsOrdinal x] [IsOrdinal y] :
    ordinalTriangle (ordinalPairRow x y) ⊆ ordinalPairCode x y ∧
    ordinalPairCode x y ∈ ordinalTriangle (succ (ordinalPairRow x y)) := by
  unfold ordinalPairRow ordinalPairCode
  split_ifs with h
  · rw [ordinalTriangle_succ]
    exact ⟨subset_ordinalAdd _ _, ordinalAdd_mem (subset_ordinalAdd y (succ y) x h)⟩
  · rw [ordinalTriangle_succ]
    have hy : y ∈ succ x := by
      rcases IsOrdinal.mem_trichotomy x y with hxy | he | hyx
      · exact False.elim (h hxy)
      · simp [he]
      · exact mem_succ_iff.mpr (Or.inr hyx)
    exact ⟨subset_ordinalAdd _ _, ordinalAdd_mem (ordinalAdd_mem hy)⟩

theorem ordinalPairCode_separated (x y u v : V)
    [IsOrdinal x] [IsOrdinal y] [IsOrdinal u] [IsOrdinal v]
    (h : ordinalPairRow x y ∈ ordinalPairRow u v) :
    ordinalPairCode x y ∈ ordinalPairCode u v := by
  have hs : succ (ordinalPairRow x y) ⊆ ordinalPairRow u v := by
    intro z hz
    rcases mem_succ_iff.mp hz with rfl | hz
    · exact h
    · exact IsOrdinal.toIsTransitive.mem_trans hz h
  exact (ordinalPairCode_bounds u v).1 _
    (ordinalTriangle_mono hs _ (ordinalPairCode_bounds x y).2)

theorem ordinalPairCode_injective {x y u v : V}
    [IsOrdinal x] [IsOrdinal y] [IsOrdinal u] [IsOrdinal v]
    (he : ordinalPairCode x y = ordinalPairCode u v) : x = u ∧ y = v := by
  have hr : ordinalPairRow x y = ordinalPairRow u v := by
    rcases IsOrdinal.mem_trichotomy (ordinalPairRow x y) (ordinalPairRow u v) with h | h | h
    · exact False.elim (mem_irrefl _ (he ▸ ordinalPairCode_separated x y u v h))
    · exact h
    · exact False.elim (mem_irrefl _ (he.symm ▸ ordinalPairCode_separated u v x y h))
  unfold ordinalPairRow at hr
  unfold ordinalPairCode at he
  by_cases hxy : x ∈ y <;> by_cases huv : u ∈ v
  · simp only [ite_eq_left hxy, ite_eq_left huv] at hr he
    subst v
    exact ⟨ordinalAdd_right_injective he, rfl⟩
  · simp only [ite_eq_left hxy, ite_eq_right huv] at hr he
    subst u
    have hh : x = ordinalAdd y v := ordinalAdd_right_injective he
    have hx := subset_ordinalAdd y v x hxy
    rw [hh] at hx
    exact False.elim (mem_irrefl _ hx)
  · simp only [ite_eq_right hxy, ite_eq_left huv] at hr he
    subst v
    have hh : ordinalAdd x y = u := ordinalAdd_right_injective he
    have hu := subset_ordinalAdd x y u huv
    rw [hh] at hu
    exact False.elim (mem_irrefl _ hu)
  · simp only [ite_eq_right hxy, ite_eq_right huv] at hr he
    subst u
    exact ⟨rfl, ordinalAdd_right_injective (ordinalAdd_right_injective he)⟩

theorem ordinalPairCode_mem_of_closed {κ x y : V} [IsOrdinal κ]
    (hs : ∀ β ∈ κ, succ β ∈ κ) (ht : ∀ β ∈ κ, ordinalTriangle β ∈ κ)
    (hx : x ∈ κ) (hy : y ∈ κ) : ordinalPairCode x y ∈ κ := by
  let := IsOrdinal.of_mem hx
  let := IsOrdinal.of_mem hy
  have hr : ordinalPairRow x y ∈ κ := by
    unfold ordinalPairRow
    split_ifs <;> assumption
  exact IsOrdinal.toIsTransitive.mem_trans (ordinalPairCode_bounds x y).2
    (ht _ (hs _ hr))

theorem ordinal_square_cardLE_of_triangle_closed {κ : V} [IsOrdinal κ]
    (hs : ∀ β ∈ κ, succ β ∈ κ) (ht : ∀ β ∈ κ, ordinalTriangle β ∈ κ) :
    (κ ×ˢ κ) ≤# κ := by
  let F : V → V := fun p ↦ ordinalPairCode (kpair.π₁ p) (kpair.π₂ p)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let f := definableGraph (κ ×ˢ κ) F hF
  have hf : f ∈ κ ^ (κ ×ˢ κ) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (by
      intro p hp
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp hp
      simpa only [F, kpair.π₁_kpair, kpair.π₂_kpair] using ordinalPairCode_mem_of_closed hs ht hx hy)
  refine ⟨f, hf, ?_⟩
  intro p q z hp hq
  obtain ⟨hpD, hzp⟩ := (pair_mem_definableGraph_iff _ F hF p z).mp hp
  obtain ⟨hqD, hzq⟩ := (pair_mem_definableGraph_iff _ F hF q z).mp hq
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp hpD
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_prod_iff.mp hqD
  let := IsOrdinal.of_mem hx
  let := IsOrdinal.of_mem hy
  let := IsOrdinal.of_mem hu
  let := IsOrdinal.of_mem hv
  have he : ordinalPairCode x y = ordinalPairCode u v := by
    simpa only [F, kpair.π₁_kpair, kpair.π₂_kpair] using hzp.symm.trans hzq
  exact kpair_iff.mpr (ordinalPairCode_injective he)

theorem regularCardinal_square_cardLE {κ : V} (hκ : IsRegularCardinal κ) : (κ ×ˢ κ) ≤# κ := by
  let := hκ.1.1
  exact ordinal_square_cardLE_of_triangle_closed
    (fun _ ↦ regularCardinal_succ_closed hκ) (fun _ ↦ regularCardinal_ordinalTriangle_closed hκ)

theorem limit_regularCardinals_square_cardLE {κ : V} [IsOrdinal κ]
    (h : ∀ β ∈ κ, ∃ ρ ∈ κ, IsRegularCardinal ρ ∧ β ∈ ρ) : (κ ×ˢ κ) ≤# κ := by
  apply ordinal_square_cardLE_of_triangle_closed
  · intro β hβ
    obtain ⟨ρ, hρ, hr, hβρ⟩ := h β hβ
    exact IsOrdinal.toIsTransitive.mem_trans (regularCardinal_succ_closed hr hβρ) hρ
  · intro β hβ
    obtain ⟨ρ, hρ, hr, hβρ⟩ := h β hβ
    exact IsOrdinal.toIsTransitive.mem_trans (regularCardinal_ordinalTriangle_closed hr hβρ) hρ

end ZFVP

