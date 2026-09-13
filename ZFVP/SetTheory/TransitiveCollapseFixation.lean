import ZFVP.SetTheory.TransitiveCollapseRestriction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A membership collapse fixes every element of a transitive subset of its domain. -/
theorem transitiveCollapse_fixes_transitive_subset {X C f a : V}
    (hf : IsTransitiveCollapse (membershipRelation X) X C f)
    [IsTransitive a] (ha : a ⊆ X) : ∀ x ∈ a, f ‘ x = x := by
  apply internalWellFounded_induction (membershipRelation_wellFounded a)
    (fun x ↦ f ‘ x = x) (by definability)
  intro x hx ih
  apply mem_ext
  intro z
  rw [transitiveCollapse_mem_value hf (ha x hx)]
  constructor
  · rintro ⟨y, _, hyx, hval⟩
    have hy : y ∈ a := (inferInstance : IsTransitive a).mem_trans hyx hx
    rw [ih y hy ((pair_mem_membershipRelation a y x).mpr ⟨hy, hx, hyx⟩)] at hval
    exact hval ▸ hyx
  · intro hz
    have hza : z ∈ a := (inferInstance : IsTransitive a).mem_trans hz hx
    exact ⟨z, ha z hza, hz,
      ih z hza ((pair_mem_membershipRelation a z x).mpr ⟨hza, hx, hz⟩)⟩

/-- A transitive member wholly contained in the domain is fixed by its collapse. -/
theorem transitiveCollapse_fixes_transitive_member {X C f a : V}
    (hf : IsTransitiveCollapse (membershipRelation X) X C f)
    [IsTransitive a] (ha : a ⊆ X) (haX : a ∈ X) : f ‘ a = a := by
  apply mem_ext
  intro z
  rw [transitiveCollapse_mem_value hf haX]
  constructor
  · rintro ⟨x, _, hxa, hval⟩
    rw [transitiveCollapse_fixes_transitive_subset hf ha x hxa] at hval
    exact hval ▸ hxa
  · intro hz
    exact ⟨z, ha z hz, hz, transitiveCollapse_fixes_transitive_subset hf ha z hz⟩

end ZFVP
