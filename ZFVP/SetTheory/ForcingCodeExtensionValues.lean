import ZFVP.SetTheory.ForcingBoundCodeExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingCodeExtends.of_values {θ η s z : V}
    (hs : IsForcingIterationCode θ s) (hz : IsForcingIterationCode η z) (hθη : θ ⊆ η)
    (hP : ∀ i ∈ θ, (forcingCodeP s) ‘ i = (forcingCodeP z) ‘ i)
    (hR : ∀ i ∈ θ, (forcingCodeR s) ‘ i = (forcingCodeR z) ‘ i)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, (forcingCodeπ s) ‘ ⟨i, j⟩ₖ = (forcingCodeπ z) ‘ ⟨i, j⟩ₖ)
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, (forcingCodeE s) ‘ ⟨i, j⟩ₖ = (forcingCodeE z) ‘ ⟨i, j⟩ₖ)
    (hL : ∀ i ∈ θ, ∀ j ∈ θ, (forcingCodeL s) ‘ ⟨i, j⟩ₖ = (forcingCodeL z) ‘ ⟨i, j⟩ₖ)
    (ht : ∀ i ∈ θ, (forcingCodet s) ‘ i = (forcingCodet z) ‘ i) : ForcingCodeExtends s z := by
  have hsq : θ ×ˢ θ ⊆ η ×ˢ η := by
    intro x hx
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hx
    exact kpair_mem_iff.mpr ⟨hθη i hi, hθη j hj⟩
  refine ⟨hs.tableP.subset_of_values hz.tableP hθη hP, hs.tableR.subset_of_values hz.tableR hθη hR,
    ?_, ?_, ?_, hs.tablet.subset_of_values hz.tablet hθη ht⟩
  · apply hs.tableπ.subset_of_values hz.tableπ hsq
    intro x hx
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hx
    exact hπ i hi j hj
  · apply hs.tableE.subset_of_values hz.tableE hsq
    intro x hx
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hx
    exact hE i hi j hj
  · apply hs.tableL.subset_of_values hz.tableL hsq
    intro x hx
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hx
    exact hL i hi j hj

theorem IsIterationTable.restrict_of_subset {A B f g : V}
    (hf : IsIterationTable A f) (hg : IsIterationTable B g) (hfg : f ⊆ g) (hAB : A ⊆ B) :
    g ↾ A = f := by
  let := hf.function
  let := hg.function
  apply functions_eq_of_domain_values
  · rw [domain_restrict_eq, hf.domain_eq, hg.domain_eq]
    apply mem_ext
    intro x
    simp only [mem_inter_iff]
    exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨hAB x hx, hx⟩⟩
  · intro x hx
    have hxA : x ∈ A := by
      rw [domain_restrict_eq, hg.domain_eq, mem_inter_iff] at hx
      exact hx.2
    rw [value_restrict (hg.domain_eq.symm ▸ hAB x hxA) hxA]
    exact (hf.value_of_subset hg hfg hxA).symm

theorem ForcingCodeExtends.restrictions {θ η s z : V}
    (h : ForcingCodeExtends s z) (hs : IsForcingIterationCode θ s) (hz : IsForcingIterationCode η z)
    (hθη : θ ⊆ η) :
    (forcingCodeP z) ↾ θ = forcingCodeP s ∧ (forcingCodeR z) ↾ θ = forcingCodeR s ∧
    (forcingCodeπ z) ↾ (θ ×ˢ θ) = forcingCodeπ s ∧ (forcingCodeE z) ↾ (θ ×ˢ θ) = forcingCodeE s ∧
    (forcingCodeL z) ↾ (θ ×ˢ θ) = forcingCodeL s ∧ (forcingCodet z) ↾ θ = forcingCodet s := by
  have hsq : θ ×ˢ θ ⊆ η ×ˢ η := by
    intro x hx
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hx
    exact kpair_mem_iff.mpr ⟨hθη i hi, hθη j hj⟩
  exact ⟨hs.tableP.restrict_of_subset hz.tableP h.subP hθη,
    hs.tableR.restrict_of_subset hz.tableR h.subR hθη,
    hs.tableπ.restrict_of_subset hz.tableπ h.subπ hsq,
    hs.tableE.restrict_of_subset hz.tableE h.subE hsq,
    hs.tableL.restrict_of_subset hz.tableL h.subL hsq,
    hs.tablet.restrict_of_subset hz.tablet h.subt hθη⟩

end ZFVP
