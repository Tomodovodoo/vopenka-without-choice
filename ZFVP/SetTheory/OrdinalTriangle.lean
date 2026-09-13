import ZFVP.SetTheory.OrdinalMultiplication

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def ordinalTriangleStep (f : V) : V :=
  ⋃ˢ repl (fun i ↦ ordinalAdd (f ‘ i) (ordinalAdd i (succ i))) (by definability) (domain f)

theorem mem_ordinalTriangleStep (f x : V) :
    x ∈ ordinalTriangleStep f ↔ ∃ i ∈ domain f,
      x ∈ ordinalAdd (f ‘ i) (ordinalAdd i (succ i)) := by
  simp only [ordinalTriangleStep, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨B, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨i, hi, hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hx⟩

def ordinalTriangleStepFormula : SetTheorySemisentence 2 :=
  f“z f. ∀ x, x ∈ z ↔ ∃ i ∈ !domain.dfn f,
    x ∈ !ordinalAddFormula (!value.dfn f i) (!ordinalAddFormula i (!succ.dfn i))”

instance ordinalTriangleStepFormula_defined :
    ℒₛₑₜ-function₁[V] ordinalTriangleStep via ordinalTriangleStepFormula :=
  ⟨fun v ↦ by
    simp [ordinalTriangleStepFormula]
    rw [mem_ext_iff]
    simp only [mem_ordinalTriangleStep]⟩

instance ordinalTriangleStep_definable : ℒₛₑₜ-function₁[V] ordinalTriangleStep :=
  ordinalTriangleStepFormula_defined.to_definable

noncomputable def ordinalTriangle (β : V) : V :=
  Replacement.transfiniteRec ordinalTriangleStep ordinalTriangleStep_definable β

instance ordinalTriangle_definable : ℒₛₑₜ-function₁[V] ordinalTriangle :=
  Replacement.transfiniteRec_definable ordinalTriangleStep_definable

theorem mem_ordinalTriangle (β x : V) [IsOrdinal β] :
    x ∈ ordinalTriangle β ↔ ∃ i ∈ β,
      x ∈ ordinalAdd (ordinalTriangle i) (ordinalAdd i (succ i)) := by
  have hr := Replacement.transfiniteRec_spec ordinalTriangleStep
    ordinalTriangleStep_definable (IsOrdinal.toOrdinal β)
  change ordinalTriangle β = ordinalTriangleStep
    (definableGraph β ordinalTriangle ordinalTriangle_definable) at hr
  rw [hr, mem_ordinalTriangleStep, domain_definableGraph]
  apply exists_congr
  intro i
  apply and_congr_right
  intro hi
  rw [value_definableGraph _ _ _ hi]

instance ordinalTriangle_ordinal (β : V) [IsOrdinal β] : IsOrdinal (ordinalTriangle β) := by
  apply transfinite_induction (fun β ↦ IsOrdinal (ordinalTriangle β)) (by definability)
    ?_ (IsOrdinal.toOrdinal β)
  intro β ih
  apply IsOrdinal.of_transitive_of_isOrdinal
  · constructor
    intro x hx y hy
    obtain ⟨i, hi, hx⟩ := (mem_ordinalTriangle β.val x).mp hx
    let := IsOrdinal.of_mem hi
    let : IsOrdinal (ordinalTriangle i) := ih (IsOrdinal.toOrdinal i) hi
    exact (mem_ordinalTriangle β.val y).mpr ⟨i, hi, IsOrdinal.toIsTransitive.mem_trans hy hx⟩
  · intro x hx
    obtain ⟨i, hi, hx⟩ := (mem_ordinalTriangle β.val x).mp hx
    let := IsOrdinal.of_mem hi
    let : IsOrdinal (ordinalTriangle i) := ih (IsOrdinal.toOrdinal i) hi
    exact IsOrdinal.of_mem hx

theorem ordinalTriangle_block_subset {β γ : V} [IsOrdinal γ] (hβ : β ∈ γ) :
    ordinalAdd (ordinalTriangle β) (ordinalAdd β (succ β)) ⊆ ordinalTriangle γ :=
  fun x hx ↦ (mem_ordinalTriangle γ x).mpr ⟨β, hβ, hx⟩

theorem ordinalTriangle_mono {β γ : V} [IsOrdinal β] [IsOrdinal γ] (h : β ⊆ γ) :
    ordinalTriangle β ⊆ ordinalTriangle γ := by
  intro x hx
  obtain ⟨i, hi, hx⟩ := (mem_ordinalTriangle β x).mp hx
  exact (mem_ordinalTriangle γ x).mpr ⟨i, h i hi, hx⟩

theorem ordinalTriangle_succ (β : V) [IsOrdinal β] :
    ordinalTriangle (succ β) = ordinalAdd (ordinalTriangle β) (ordinalAdd β (succ β)) := by
  apply mem_ext
  intro x
  rw [mem_ordinalTriangle]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hx
    · exact subset_ordinalAdd _ _ x (ordinalTriangle_block_subset hi x hx)
  · intro hx
    exact ⟨β, by simp, hx⟩

theorem regularCardinal_ordinalTriangle_closed {κ β : V} (hκ : IsRegularCardinal κ)
    (hβ : β ∈ κ) : ordinalTriangle β ∈ κ := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hβ
  apply transfinite_induction (fun β ↦ β ∈ κ → ordinalTriangle β ∈ κ) (by definability)
    ?_ (IsOrdinal.toOrdinal β) hβ
  intro β ih hβ
  let F := definableGraph β.val
    (fun i ↦ ordinalAdd (ordinalTriangle i) (ordinalAdd i (succ i))) (by definability)
  have hF : F ∈ κ ^ β.val := definableGraph_mem_function_of_mapsTo _ _ _ _ (by
    intro i hi
    let := IsOrdinal.of_mem hi
    have hiκ := IsOrdinal.toIsTransitive.mem_trans hi hβ
    exact regularCardinal_ordinalAdd_closed hκ
      (ih (IsOrdinal.toOrdinal i) hi hiκ)
      (regularCardinal_ordinalAdd_closed hκ hiκ (regularCardinal_succ_closed hκ hiκ)))
  obtain ⟨ξ, hξ, hb⟩ := regularCardinal_maps_bounded hκ hβ hF
  let := IsOrdinal.of_mem hξ
  have hsub : ordinalTriangle β.val ⊆ ξ := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := (mem_ordinalTriangle β.val x).mp hx
    have hh := hb i hi
    rw [show F ‘ i = ordinalAdd (ordinalTriangle i) (ordinalAdd i (succ i)) from
      value_definableGraph _ _ _ hi] at hh
    exact IsOrdinal.toIsTransitive.mem_trans hx hh
  exact ordinal_mem_of_subset_mem hsub hξ

end ZFVP
