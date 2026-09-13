import ZFVP.SetTheory.WoodinCollapse
import ZFVP.SetTheory.ForcingSeparativeOrder
import ZFVP.SetTheory.ForcingClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Separatively descending partial functions remain pairwise compatible as
functions, so their union is still functional. -/
theorem compatible_range_of_separative_descending {P α f : V} [IsOrdinal α]
    (hP : ∀ p ∈ P, IsFunction p)
    (hf : IsForcingDescending P (forcingSeparativeOrder P (reverseInclusionOrder P)) α f) :
    CompatibleFunctionFamily (range f) := by
  let := IsFunction.of_mem hf.1
  intro p hp q hq x y z hxy hxz
  obtain ⟨i, hip⟩ := mem_range_iff.mp hp
  obtain ⟨j, hjq⟩ := mem_range_iff.mp hq
  have hi : i ∈ α := domain_eq_of_mem_function hf.1 ▸ mem_domain_of_kpair_mem hip
  have hj : j ∈ α := domain_eq_of_mem_function hf.1 ▸ mem_domain_of_kpair_mem hjq
  have hpP := function_value_mem hf.1 hi
  have hqP := function_value_mem hf.1 hj
  have hc : ForcingCompatible P (reverseInclusionOrder P) (f ‘ i) (f ‘ j) := by
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hj
    rcases IsOrdinal.mem_trichotomy i j with hij | rfl | hji
    · exact forcingCompatible_symm (forcingSeparativeOrder_compatible
        (reverseInclusionOrder_poset P).1 (hf.2 j hj i hij))
    · exact ⟨f ‘ i, hpP, (reverseInclusionOrder_poset P).1.2.1 _ hpP,
        (reverseInclusionOrder_poset P).1.2.1 _ hpP⟩
    · exact forcingSeparativeOrder_compatible (reverseInclusionOrder_poset P).1 (hf.2 i hi j hji)
  obtain ⟨r, hr, hrp, hrq⟩ := hc
  let := hP r hr
  have hpr : p ⊆ r := by
    rw [← value_eq_of_kpair_mem hip]
    exact ((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2
  have hqr : q ⊆ r := by
    rw [← value_eq_of_kpair_mem hjq]
    exact ((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2
  exact IsFunction.unique (hpr _ hxy) (hqr _ hxz)

theorem woodinCollapse_separative_closedAt {κ δ α : V} (hκ : IsRegularCardinal κ)
    (hα : α ∈ κ) (hDC : InternalDependentChoiceAt α) :
    IsForcingClosedAt (woodinCollapse κ δ)
      (forcingSeparativeOrder (woodinCollapse κ δ) (woodinCollapseOrder κ δ)) α := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hα
  intro f hf
  let := IsFunction.of_mem hf.1
  have hc := compatible_range_of_separative_descending
    (fun p hp ↦ ((mem_woodinCollapse κ δ p).mp hp).2.1) hf
  have hu := woodinCollapse_sequence_union hκ hα hDC hf.1 hc
  refine ⟨⋃ˢ range f, hu, ?_⟩
  intro i hi
  apply forcingOrder_subset_separative (woodinCollapse_poset κ δ).1
  apply (pair_mem_reverseInclusionOrder _ _ _).mpr
  refine ⟨hu, function_value_mem hf.1 hi, ?_⟩
  intro x hx
  exact mem_sUnion_iff.mpr ⟨f ‘ i, mem_range_of_kpair_mem
    (kpair_value_mem ((domain_eq_of_mem_function hf.1).symm ▸ hi)), hx⟩

end ZFVP
