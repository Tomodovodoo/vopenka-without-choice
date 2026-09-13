import ZFVP.SetTheory.CardinalSmallComplements

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem range_compose_surjective {X Y Z f g : V} (hf : f ∈ Y ^ X) (hg : g ∈ Z ^ Y)
    (hfr : range f = Y) (hgr : range g = Z) : range (compose f g) = Z := by
  apply subset_antisymm (range_subset_of_mem_function (compose_function hf hg))
  intro z hz
  obtain ⟨y, hyz⟩ := mem_range_iff.mp (hgr.symm ▸ hz)
  have hy : y ∈ Y := domain_eq_of_mem_function hg ▸ mem_domain_of_kpair_mem hyz
  obtain ⟨x, hxy⟩ := mem_range_iff.mp (hfr.symm ▸ hy)
  exact mem_range_of_kpair_mem (kpair_mem_compose_iff.mpr ⟨y, hxy, hyz⟩)

/-- A cofinal map from any set onto a regular ordinal can be converted to a
surjection, by enumerating its ordinal range. This needs no choice function. -/
theorem IsCofinalMap.surjection_of_regular {κ X f : V} (hf : IsCofinalMap κ X f)
    (hκ : IsRegularCardinal κ) : ∃ g ∈ κ ^ X, range g = κ := by
  let := hκ.1.1
  let := IsFunction.of_mem hf.1
  let D := range f
  have hD : D ⊆ κ := range_subset_of_mem_function hf.1
  have hw := ordinalSubset_membership_wellOrder hD
  let α := internalOrderType (membershipRelation D) D
  let := internalOrderType_ordinal hw
  have hz : (0 : V) ∈ κ := hκ.2.1 _ (by simp)
  obtain ⟨x, hx, _⟩ := hf.2 0 hz
  have hDn : IsNonempty D := ⟨f ‘ x, value_mem_range hf.1 hx⟩
  obtain ⟨e, he, her⟩ := surjection_of_injection (internalOrderType_cardEQ hw).2 hDn
  change e ∈ D ^ α at he
  have hcof : IsCofinalMap κ α e := by
    refine ⟨mem_function_of_mem_function_of_subset he hD, ?_⟩
    intro β hβ
    obtain ⟨y, hy, hβy⟩ := hf.2 β hβ
    have hyD : f ‘ y ∈ D := value_mem_range hf.1 hy
    obtain ⟨i, hie⟩ := mem_range_iff.mp (her.symm ▸ hyD)
    let := IsFunction.of_mem he
    exact ⟨i, domain_eq_of_mem_function he ▸ mem_domain_of_kpair_mem hie,
      (value_eq_of_kpair_mem hie).symm ▸ hβy⟩
  have hακ : α = κ := subset_antisymm (ordinalSubset_orderType_subset hD)
    (hκ.2.2 ▸ internalCofinality_minimal hcof)
  have hκD : κ ≤# D := hακ ▸ (internalOrderType_cardEQ hw).1
  obtain ⟨g, hg, hgr⟩ := surjection_of_injection hκD ⟨0, hz⟩
  have hfD : f ∈ D ^ X := by
    rw [← domain_eq_of_mem_function hf.1]
    exact IsFunction.mem_function f
  exact ⟨compose f g, compose_function hfD hg, range_compose_surjective hfD hg rfl hgr⟩

end ZFVP
