import ZFVP.SetTheory.RegularOrdinalAddition
import ZFVP.SetTheory.NaturalAddition

/-! Ordinal multiplication by internal recursion, with a uniform formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def ordinalMulStepFormula : SetTheorySemisentence 3 :=
  f“z α f. ∀ x, x ∈ z ↔ ∃ i ∈ !domain.dfn f, x ∈ !ordinalAddFormula (!value.dfn f i) α”

def ordinalMulFormula : SetTheorySemisentence 3 := parameterRecursionFormula ordinalMulStepFormula

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def ordinalMulStep (α f : V) : V :=
  ⋃ˢ repl (fun i ↦ ordinalAdd (f ‘ i) α) (by definability) (domain f)

theorem mem_ordinalMulStep (α f x : V) :
    x ∈ ordinalMulStep α f ↔ ∃ i ∈ domain f, x ∈ ordinalAdd (f ‘ i) α := by
  simp only [ordinalMulStep, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨B, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨i, hi, hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨ordinalAdd (f ‘ i) α, ⟨i, hi, rfl⟩, hx⟩

instance ordinalMulStepFormula_defined :
    ℒₛₑₜ-function₂[V] ordinalMulStep via ordinalMulStepFormula :=
  ⟨fun v ↦ by
    simp [ordinalMulStepFormula]
    rw [mem_ext_iff]
    simp only [mem_ordinalMulStep]⟩

instance ordinalMulStep_definable : ℒₛₑₜ-function₂[V] ordinalMulStep :=
  ordinalMulStepFormula_defined.to_definable

noncomputable def ordinalMul (α β : V) : V :=
  parameterRecursion ordinalMulStep ordinalMulStep_definable α β

instance ordinalMulFormula_defined : ℒₛₑₜ-function₂[V] ordinalMul via ordinalMulFormula :=
  parameterRecursionFormula_defined ordinalMulStep ordinalMulStepFormula

instance ordinalMul_definable : ℒₛₑₜ-function₂[V] ordinalMul :=
  ordinalMulFormula_defined.to_definable

theorem mem_ordinalMul (α β x : V) [IsOrdinal β] :
    x ∈ ordinalMul α β ↔ ∃ i ∈ β, x ∈ ordinalAdd (ordinalMul α i) α := by
  have hr := Replacement.transfiniteRec_spec (ordinalMulStep α) (by definability) (IsOrdinal.toOrdinal β)
  change ordinalMul α β = ordinalMulStep α
    (definableGraph β (ordinalMul α) (by definability)) at hr
  rw [hr, mem_ordinalMulStep, domain_definableGraph]
  apply exists_congr
  intro i
  apply and_congr_right
  intro hi
  rw [value_definableGraph _ _ _ hi]

instance ordinalMul_ordinal (α β : V) [IsOrdinal α] [IsOrdinal β] : IsOrdinal (ordinalMul α β) := by
  apply transfinite_induction (fun β ↦ IsOrdinal (ordinalMul α β)) (by definability)
    ?_ (IsOrdinal.toOrdinal β)
  intro β ih
  apply IsOrdinal.of_transitive_of_isOrdinal
  · constructor
    intro x hx y hy
    obtain ⟨i, hi, hx⟩ := (mem_ordinalMul α β x).mp hx
    let := IsOrdinal.of_mem hi
    let : IsOrdinal (ordinalMul α i) := ih (IsOrdinal.toOrdinal i) hi
    exact (mem_ordinalMul α β y).mpr ⟨i, hi, IsOrdinal.toIsTransitive.mem_trans hy hx⟩
  · intro x hx
    obtain ⟨i, hi, hx⟩ := (mem_ordinalMul α β x).mp hx
    let := IsOrdinal.of_mem hi
    let : IsOrdinal (ordinalMul α i) := ih (IsOrdinal.toOrdinal i) hi
    exact IsOrdinal.of_mem hx

theorem ordinalMul_zero (α : V) : ordinalMul α ∅ = ∅ := by
  apply mem_ext
  intro x
  simp [mem_ordinalMul]

theorem ordinalMul_block_subset {α β γ : V} [IsOrdinal γ] (hβ : β ∈ γ) :
    ordinalAdd (ordinalMul α β) α ⊆ ordinalMul α γ :=
  fun x hx ↦ (mem_ordinalMul α γ x).mpr ⟨β, hβ, hx⟩

theorem ordinalMul_mono_right (α : V) {β γ : V} [IsOrdinal β] [IsOrdinal γ] (h : β ⊆ γ) :
    ordinalMul α β ⊆ ordinalMul α γ := by
  intro x hx
  obtain ⟨i, hi, hx⟩ := (mem_ordinalMul α β x).mp hx
  exact (mem_ordinalMul α γ x).mpr ⟨i, h i hi, hx⟩

theorem ordinalMul_succ (α β : V) [IsOrdinal α] [IsOrdinal β] :
    ordinalMul α (succ β) = ordinalAdd (ordinalMul α β) α := by
  apply mem_ext
  intro x
  rw [mem_ordinalMul]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hx
    · exact subset_ordinalAdd (ordinalMul α β) α x (ordinalMul_block_subset hi x hx)
  · intro hx
    exact ⟨β, by simp, hx⟩

theorem regularCardinal_ordinalMul_closed {κ α β : V} (hκ : IsRegularCardinal κ)
    (hα : α ∈ κ) (hβ : β ∈ κ) : ordinalMul α β ∈ κ := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hα
  let := IsOrdinal.of_mem hβ
  apply transfinite_induction (fun β ↦ β ∈ κ → ordinalMul α β ∈ κ) (by definability)
    ?_ (IsOrdinal.toOrdinal β) hβ
  intro β ih hβ
  let F := definableGraph β.val (fun i ↦ ordinalAdd (ordinalMul α i) α) (by definability)
  have hF : F ∈ κ ^ β.val := definableGraph_mem_function_of_mapsTo _ _ _ _ (by
    intro i hi
    let := IsOrdinal.of_mem hi
    exact regularCardinal_ordinalAdd_closed hκ
      (ih (IsOrdinal.toOrdinal i) hi (IsOrdinal.toIsTransitive.mem_trans hi hβ)) hα)
  obtain ⟨ξ, hξ, hb⟩ := regularCardinal_maps_bounded hκ hβ hF
  let := IsOrdinal.of_mem hξ
  have hsub : ordinalMul α β.val ⊆ ξ := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := (mem_ordinalMul α β.val x).mp hx
    have hh := hb i hi
    rw [show F ‘ i = ordinalAdd (ordinalMul α i) α from value_definableGraph _ _ _ hi] at hh
    exact IsOrdinal.toIsTransitive.mem_trans hx hh
  exact ordinal_mem_of_subset_mem hsub hξ

end ZFVP
