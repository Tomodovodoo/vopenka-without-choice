import ZFVP.SetTheory.ForcingBoundCongruence
import ZFVP.SetTheory.ForcingIterationCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsIterationTable.value_of_subset {A B f g x : V}
    (hf : IsIterationTable A f) (hg : IsIterationTable B g) (hfg : f ⊆ g) (hx : x ∈ A) :
    f ‘ x = g ‘ x := by
  let := hf.function
  let := hg.function
  exact (value_eq_of_kpair_mem (hfg _ (kpair_mem_iff_value.mpr
    ⟨hf.domain_eq.symm ▸ hx, rfl⟩))).symm

theorem ForcingCodeExtends.bound_iff {θ η s z B i I : V}
    (h : ForcingCodeExtends s z) (hs : IsForcingIterationCode θ s)
    (hz : IsForcingIterationCode η z) (hi : i ∈ θ) :
    IsCoherentForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B i I ↔
    IsCoherentForcingBound θ (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z) B i I := by
  have hp := fun j hj ↦ hs.tableP.value_of_subset hz.tableP h.subP (x := j) hj
  have hr := fun j hj ↦ hs.tableR.value_of_subset hz.tableR h.subR (x := j) hj
  have hm := fun j hj k hk ↦ hs.tableπ.value_of_subset hz.tableπ h.subπ
    (kpair_mem_iff.mpr ⟨hj, hk⟩ : ⟨j, k⟩ₖ ∈ θ ×ˢ θ)
  constructor
  · intro hb
    exact hb.congr (hp i hi) (hr i hi) hp hr (fun j hj _ ↦ hm i hi j hj)
      (fun j hj k hk _ _ ↦ hm j hj k hk) (fun _ _ _ ↦ rfl)
  · intro hb
    exact hb.congr (hp i hi).symm (hr i hi).symm
      (fun j hj ↦ (hp j hj).symm) (fun j hj ↦ (hr j hj).symm)
      (fun j hj _ ↦ (hm i hi j hj).symm)
      (fun j hj k hk _ _ ↦ (hm j hj k hk).symm) (fun _ _ _ ↦ rfl)

theorem ForcingCodeExtends.bound_sectionCompatible_iff {θ η s z B i I : V}
    (h : ForcingCodeExtends s z) (hs : IsForcingIterationCode θ s)
    (hz : IsForcingIterationCode η z) (hi : i ∈ θ) :
    IsSectionCompatibleForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s)
      (forcingCodeE s) B i I ↔
    IsSectionCompatibleForcingBound θ (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z)
      (forcingCodeE z) B i I := by
  have hp := fun j hj ↦ hs.tableP.value_of_subset hz.tableP h.subP (x := j) hj
  have hr := fun j hj ↦ hs.tableR.value_of_subset hz.tableR h.subR (x := j) hj
  have hm := fun j hj k hk ↦ hs.tableπ.value_of_subset hz.tableπ h.subπ
    (kpair_mem_iff.mpr ⟨hj, hk⟩ : ⟨j, k⟩ₖ ∈ θ ×ˢ θ)
  have he := fun j hj k hk ↦ hs.tableE.value_of_subset hz.tableE h.subE
    (kpair_mem_iff.mpr ⟨hj, hk⟩ : ⟨j, k⟩ₖ ∈ θ ×ˢ θ)
  constructor
  · intro hb
    exact hb.congr (hp i hi) (hr i hi) hp hr (fun j hj _ ↦ hm i hi j hj)
      (fun j hj k hk _ _ ↦ he j hj k hk) (fun _ _ _ ↦ rfl)
  · intro hb
    exact hb.congr (hp i hi).symm (hr i hi).symm
      (fun j hj ↦ (hp j hj).symm) (fun j hj ↦ (hr j hj).symm)
      (fun j hj _ ↦ (hm i hi j hj).symm)
      (fun j hj k hk _ _ ↦ (he j hj k hk).symm) (fun _ _ _ ↦ rfl)

end ZFVP
