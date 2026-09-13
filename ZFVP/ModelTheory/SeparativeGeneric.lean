import ZFVP.SetTheory.ForcingSeparativeOrder
import ZFVP.ModelTheory.ForcingGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem externalForcingGeneric_separative_upward {P R p q : V} {G : Set V}
    (hR : IsForcingPreorder P R) (hG : IsExternalForcingGeneric P R G)
    (hp : p ∈ G) (hpq : ⟨p, q⟩ₖ ∈ forcingSeparativeOrder P R) : q ∈ G := by
  obtain ⟨_, hq, h⟩ := (kpair_mem_forcingSeparativeOrder P R p q).mp hpq
  let D : V := {r ∈ P ; ⟨r, q⟩ₖ ∈ R}
  have hD : ForcingDenseBelow P R D p := by
    refine ⟨fun r hr ↦ (mem_sep_iff.mp hr).1, ?_⟩
    intro r hr hrp
    obtain ⟨s, hs, hsr, hsq⟩ := h r hr hrp
    exact ⟨s, mem_sep_iff.mpr ⟨hs, hsq⟩, hsr⟩
  obtain ⟨r, hrG, hrD⟩ := externalForcingGeneric_meets_denseBelow hR hG hp hD
  exact hG.1.2.2.1 r hrG q hq (mem_sep_iff.mp hrD).2

theorem externalForcingGeneric_separative {P R : V} {G : Set V}
    (hR : IsForcingPreorder P R) (hG : IsExternalForcingGeneric P R G) :
    IsExternalForcingGeneric P (forcingSeparativeOrder P R) G := by
  refine ⟨⟨hG.1.1, hG.1.2.1, ?_, ?_⟩, ?_⟩
  · intro p hp q _ hpq
    exact externalForcingGeneric_separative_upward hR hG hp hpq
  · intro p hp q hq
    obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p hp q hq
    exact ⟨r, hr, forcingOrder_subset_separative hR _ hrp, forcingOrder_subset_separative hR _ hrq⟩
  · intro D hD
    let E : V := {r ∈ P ; ∃ d ∈ D, ⟨r, d⟩ₖ ∈ R}
    have hE : ForcingDense P R E := by
      refine ⟨fun r hr ↦ (mem_sep_iff.mp hr).1, ?_⟩
      intro p hp
      obtain ⟨d, hd, hdp⟩ := hD.2 p hp
      obtain ⟨r, hr, hrd, hrp⟩ := forcingSeparativeOrder_compatible hR hdp
      exact ⟨r, mem_sep_iff.mpr ⟨hr, d, hd, hrd⟩, hrp⟩
    obtain ⟨r, hrG, hrE⟩ := hG.2 E hE
    obtain ⟨d, hd, hrd⟩ := (mem_sep_iff.mp hrE).2
    exact ⟨d, hG.1.2.2.1 r hrG d (hD.1 d hd) hrd, hd⟩

end ZFVP
