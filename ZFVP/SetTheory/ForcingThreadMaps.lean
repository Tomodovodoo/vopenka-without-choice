import ZFVP.SetTheory.ForcingInverseLimit

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingThreadRestriction (C η : V) : V :=
  definableGraph C (fun f ↦ f ↾ η) (by definability)

theorem forcingThreadRestriction_value {C η f : V} (hf : f ∈ C) :
    (forcingThreadRestriction C η) ‘ f = f ↾ η :=
  value_definableGraph _ _ _ hf

theorem forcingThreadRestriction_maps {θ η P π U : V} (hη : η ⊆ θ) :
    forcingThreadRestriction (forcingInverseLimit θ P π U) η ∈
      forcingInverseLimit η P π U ^ forcingInverseLimit θ P π U :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hf ↦ forcingInverseLimit_restrict hη hf)

noncomputable def forcingThreadCoordinate (C i : V) : V :=
  definableGraph C (fun f ↦ f ‘ i) (by definability)

theorem forcingThreadCoordinate_value {C i f : V} (hf : f ∈ C) :
    (forcingThreadCoordinate C i) ‘ f = f ‘ i :=
  value_definableGraph _ _ _ hf

theorem forcingThreadCoordinate_maps {θ P π U i : V} (hi : i ∈ θ) :
    forcingThreadCoordinate (forcingInverseLimit θ P π U) i ∈
      (P ‘ i) ^ forcingInverseLimit θ P π U :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hf ↦
    ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 i hi)

theorem forcingThreadCoordinate_monotone {θ P R π U i f g : V} (hi : i ∈ θ)
    (hfg : ⟨f, g⟩ₖ ∈ forcingThreadOrder θ R (forcingInverseLimit θ P π U)) :
    ⟨(forcingThreadCoordinate (forcingInverseLimit θ P π U) i) ‘ f,
      (forcingThreadCoordinate (forcingInverseLimit θ P π U) i) ‘ g⟩ₖ ∈ R ‘ i := by
  obtain ⟨hf, hg, h⟩ := (mem_forcingThreadOrder_iff _ _ _ _ _).mp hfg
  rw [forcingThreadCoordinate_value hf, forcingThreadCoordinate_value hg]
  exact h i hi

/-- Coherence makes the coordinate maps commute with the given projections. -/
theorem forcingThreadCoordinate_coherent {θ P π U i j f : V}
    (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ∈ j)
    (hf : f ∈ forcingInverseLimit θ P π U) :
    (π ‘ ⟨i, j⟩ₖ) ‘ ((forcingThreadCoordinate (forcingInverseLimit θ P π U) j) ‘ f) =
      (forcingThreadCoordinate (forcingInverseLimit θ P π U) i) ‘ f := by
  rw [forcingThreadCoordinate_value hf, forcingThreadCoordinate_value hf]
  exact ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.2 j hj i hij hi

theorem forcingInverseLimit_top {θ P R π U t : V} (ht : t ∈ U ^ θ)
    (hcoh : IsCoherentThread θ π t)
    (htop : ∀ i ∈ θ, IsForcingTop (P ‘ i) (R ‘ i) (t ‘ i)) :
    IsForcingTop (forcingInverseLimit θ P π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ P π U)) t := by
  apply forcingThreadOrder_top
  · exact (mem_forcingInverseLimit_iff _ _ _ _ _).mpr
      ⟨ht, fun i hi ↦ (htop i hi).1, hcoh⟩
  · exact fun _ hf ↦ ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1
  · exact htop

end ZFVP
