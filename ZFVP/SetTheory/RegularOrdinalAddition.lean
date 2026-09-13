import ZFVP.SetTheory.UniformCodingUniverse
import ZFVP.SetTheory.FiniteCofinality
import ZFVP.SetTheory.FormulaReflection

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem regularCardinal_ordinalAdd_closed {κ α β : V} (hκ : IsRegularCardinal κ)
    (hα : α ∈ κ) (hβ : β ∈ κ) : ordinalAdd α β ∈ κ := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hα
  let := IsOrdinal.of_mem hβ
  apply transfinite_induction (fun β ↦ β ∈ κ → ordinalAdd α β ∈ κ) (by definability)
    ?_ (IsOrdinal.toOrdinal β) hβ
  intro β ih hβ
  let F := definableGraph β.val (fun ξ ↦ succ (ordinalAdd α ξ)) (by definability)
  have hF : F ∈ κ ^ β.val := definableGraph_mem_function_of_mapsTo _ _ _ _ (by
    intro ξ hξ
    let := IsOrdinal.of_mem hξ
    exact regularCardinal_succ_closed hκ
      (ih (IsOrdinal.toOrdinal ξ) hξ (IsOrdinal.toIsTransitive.mem_trans hξ hβ)))
  obtain ⟨η, hη, hb⟩ := regularCardinal_maps_bounded hκ hβ hF
  let := IsOrdinal.of_mem hη
  let := ordinal_union_ordinal α η
  have hsub : ordinalAdd α β.val ⊆ α ∪ η := by
    intro x hx
    rcases (mem_ordinalAdd_iff α β.val x).mp hx with hx | ⟨ξ, hξ, hx⟩
    · exact mem_union_iff.mpr (Or.inl hx)
    · have hh := hb ξ hξ
      rw [show F ‘ ξ = succ (ordinalAdd α ξ) from value_definableGraph _ _ _ hξ] at hh
      exact mem_union_iff.mpr (Or.inr (IsOrdinal.toIsTransitive.mem_trans hx hh))
  exact ordinal_mem_of_subset_mem hsub (ordinal_union_mem hα hη)

end ZFVP
