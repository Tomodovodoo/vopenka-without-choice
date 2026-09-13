import ZFVP.SetTheory.UniformCollapse

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The members of the image of `a` are precisely the images of members of `a`
that belong to the domain of the collapse. -/
theorem transitiveCollapse_mem_value {X C f a z : V}
    (hf : IsTransitiveCollapse (membershipRelation X) X C f) (ha : a ∈ X) :
    z ∈ f ‘ a ↔ ∃ x ∈ X, x ∈ a ∧ f ‘ x = z := by
  have : IsFunction f := IsFunction.of_mem hf.2.1
  have hd := domain_eq_of_mem_function hf.2.1
  constructor
  · intro hz
    have hzC := hf.1.mem_trans hz (function_value_mem hf.2.1 ha)
    obtain ⟨x, hx⟩ := mem_range_iff.mp (hf.2.2.1.symm ▸ hzC)
    have hxX : x ∈ X := hd ▸ mem_domain_of_kpair_mem hx
    have heq := value_eq_of_kpair_mem hx
    exact ⟨x, hxX, ((pair_mem_membershipRelation X x a).mp
      ((hf.2.2.2.2 x hxX a ha).mp (heq.symm ▸ hz))).2.2, heq⟩
  · rintro ⟨x, hx, hxa, rfl⟩
    exact (hf.2.2.2.2 x hx a ha).mpr
      ((pair_mem_membershipRelation X x a).mpr ⟨hx, ha, hxa⟩)

/-- A membership collapse sends a transitive member of its domain to a transitive set. -/
theorem transitiveCollapse_value_transitive {X C f a : V}
    (hf : IsTransitiveCollapse (membershipRelation X) X C f) (ha : a ∈ X)
    [IsTransitive a] : IsTransitive (f ‘ a) := by
  constructor
  intro y hy z hz
  obtain ⟨x, hx, hxa, rfl⟩ := (transitiveCollapse_mem_value hf ha).mp hy
  obtain ⟨w, hw, hwx, rfl⟩ := (transitiveCollapse_mem_value hf hx).mp hz
  exact (transitiveCollapse_mem_value hf ha).mpr
    ⟨w, hw, (inferInstance : IsTransitive a).mem_trans hwx hxa, rfl⟩

/-- Restricting a membership collapse to `X ∩ a` collapses it onto the image of `a`. -/
theorem transitiveCollapse_restrict_member {X C f a : V}
    (hf : IsTransitiveCollapse (membershipRelation X) X C f) (ha : a ∈ X)
    [IsTransitive a] :
    IsTransitiveCollapse (membershipRelation (X ∩ a)) (X ∩ a) (f ‘ a) (f ↾ (X ∩ a)) := by
  have : IsFunction f := IsFunction.of_mem hf.2.1
  have hd := domain_eq_of_mem_function hf.2.1
  have hrange : range (f ↾ (X ∩ a)) = f ‘ a := by
    apply mem_ext
    intro z
    rw [mem_range_iff, transitiveCollapse_mem_value hf ha]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨hxf, hxi⟩ := kpair_mem_restrict_iff.mp hx
      exact ⟨x, (mem_inter_iff.mp hxi).1, (mem_inter_iff.mp hxi).2,
        value_eq_of_kpair_mem hxf⟩
    · rintro ⟨x, hx, hxa, rfl⟩
      exact ⟨x, kpair_mem_restrict_iff.mpr
        ⟨kpair_value_mem (hd.symm ▸ hx), mem_inter_iff.mpr ⟨hx, hxa⟩⟩⟩
  have hdom : domain (f ↾ (X ∩ a)) = X ∩ a := by
    rw [domain_restrict_eq, hd]
    apply mem_ext
    intro x
    simp only [mem_inter_iff]
    tauto
  have hval : ∀ x ∈ X ∩ a, (f ↾ (X ∩ a)) ‘ x = f ‘ x := by
    intro x hx
    exact value_restrict (hd.symm ▸ (mem_inter_iff.mp hx).1) hx
  refine ⟨transitiveCollapse_value_transitive hf ha, ?_, hrange, ?_, ?_⟩
  · simpa only [hrange, hdom] using IsFunction.mem_function (f ↾ (X ∩ a))
  · intro x hx y hy heq
    rw [hval x hx, hval y hy] at heq
    exact hf.2.2.2.1 x (mem_inter_iff.mp hx).1 y (mem_inter_iff.mp hy).1 heq
  · intro x hx y hy
    rw [hval x hx, hval y hy, hf.2.2.2.2 x (mem_inter_iff.mp hx).1 y (mem_inter_iff.mp hy).1,
      pair_mem_membershipRelation, pair_mem_membershipRelation]
    exact ⟨fun h ↦ ⟨hx, hy, h.2.2⟩,
      fun h ↦ ⟨(mem_inter_iff.mp hx).1, (mem_inter_iff.mp hy).1, h.2.2⟩⟩

end ZFVP

