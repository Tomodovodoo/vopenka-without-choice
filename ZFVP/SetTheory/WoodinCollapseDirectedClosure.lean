import ZFVP.SetTheory.ForcingDirectedClosure
import ZFVP.SetTheory.WoodinCollapse

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCollapse_directed_union {κ δ γ H : V} (hκ : IsRegularCardinal κ)
    (hγ : γ ∈ κ) (hDC : InternalDependentChoiceAt γ)
    (hH : IsForcingDirectedFamily (woodinCollapse κ δ) (woodinCollapseOrder κ δ) γ H) :
    ⋃ˢ range H ∈ woodinCollapse κ δ ∧
      ∀ i ∈ γ, ⟨⋃ˢ range H, H ‘ i⟩ₖ ∈ woodinCollapseOrder κ δ := by
  let := IsFunction.of_mem hH.1
  have hc : CompatibleFunctionFamily (range H) := by
    intro p hp q hq x y z hxy hxz
    obtain ⟨i, hip⟩ := mem_range_iff.mp hp
    obtain ⟨j, hjq⟩ := mem_range_iff.mp hq
    have hi : i ∈ γ := domain_eq_of_mem_function hH.1 ▸ mem_domain_of_kpair_mem hip
    have hj : j ∈ γ := domain_eq_of_mem_function hH.1 ▸ mem_domain_of_kpair_mem hjq
    obtain ⟨k, hk, hki, hkj⟩ := hH.2 i hi j hj
    have hp' : p ⊆ H ‘ k := by
      rw [← value_eq_of_kpair_mem hip]
      exact ((pair_mem_reverseInclusionOrder _ _ _).mp hki).2.2
    have hq' : q ⊆ H ‘ k := by
      rw [← value_eq_of_kpair_mem hjq]
      exact ((pair_mem_reverseInclusionOrder _ _ _).mp hkj).2.2
    let := ((mem_woodinCollapse _ _ _).mp (function_value_mem hH.1 hk)).2.1
    exact (value_eq_of_kpair_mem (hp' _ hxy)).symm.trans (value_eq_of_kpair_mem (hq' _ hxz))
  have hu := woodinCollapse_sequence_union hκ hγ hDC hH.1 hc
  refine ⟨hu, fun i hi ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, function_value_mem hH.1 hi, ?_⟩⟩
  intro x hx
  exact mem_sUnion_iff.mpr ⟨H ‘ i, mem_range_of_kpair_mem
    (kpair_value_mem ((domain_eq_of_mem_function hH.1).symm ▸ hi)), hx⟩

theorem woodinCollapse_directedClosedAt {κ δ γ : V} (hκ : IsRegularCardinal κ)
    (hγ : γ ∈ κ) (hDC : InternalDependentChoiceAt γ) :
    IsForcingDirectedClosedAt (woodinCollapse κ δ) (woodinCollapseOrder κ δ) γ := by
  intro H hH
  exact ⟨⋃ˢ range H, woodinCollapse_directed_union hκ hγ hDC hH⟩

end ZFVP
