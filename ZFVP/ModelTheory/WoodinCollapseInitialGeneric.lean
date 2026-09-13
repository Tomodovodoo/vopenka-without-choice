import ZFVP.SetTheory.WoodinCollapseProjection
import ZFVP.ModelTheory.ForcingGeneric

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The initial collapse filter is the intersection with the smaller poset. -/
def woodinCollapseInitialGeneric (κ β : V) (G : Set V) : Set V :=
  {p | p ∈ G ∧ p ∈ woodinCollapse κ β}

theorem woodinCollapseCut_mem_generic {κ β δ : V} {G : Set V}
    (hβ : IsRegularCardinal β) [IsOrdinal δ] (hβδ : β ⊆ δ)
    (hG : IsExternalForcingFilter (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G)
    {p : V} (hp : p ∈ G) : woodinCollapseCut κ β p ∈ woodinCollapseInitialGeneric κ β G := by
  let := hβ.1.1
  have hcut := woodinCollapseCut_mem hβ (hG.1 p hp)
  have hcutδ := woodinCollapse_mono hβδ _ hcut
  exact ⟨hG.2.2.1 p hp _ hcutδ ((pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hG.1 p hp, hcutδ, woodinCollapseCut_subset _ _ _⟩), hcut⟩

theorem woodinCollapse_initial_filter {κ β δ : V} {G : Set V}
    (hβ : IsRegularCardinal β) [IsOrdinal δ] (hβδ : β ⊆ δ)
    (hG : IsExternalForcingFilter (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G) :
    IsExternalForcingFilter (woodinCollapse κ β) (woodinCollapseOrder κ β)
      (woodinCollapseInitialGeneric κ β G) := by
  let := hβ.1.1
  refine ⟨fun p hp ↦ hp.2, ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hG.2.1
    exact ⟨_, woodinCollapseCut_mem_generic hβ hβδ hG hp⟩
  · intro p hp q hq hpq
    have hqδ := woodinCollapse_mono hβδ q hq
    exact ⟨hG.2.2.1 p hp.1 q hqδ ((pair_mem_reverseInclusionOrder _ _ _).mpr
      ⟨hG.1 p hp.1, hqδ, ((pair_mem_reverseInclusionOrder _ _ _).mp hpq).2.2⟩), hq⟩
  · intro p hp q hq
    obtain ⟨r, hr, hrp, hrq⟩ := hG.2.2.2 p hp.1 q hq.1
    have hc := woodinCollapseCut_mem_generic hβ hβδ hG hr
    refine ⟨_, hc, (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hc.2, hp.2, ?_⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hc.2, hq.2, ?_⟩⟩
    · have hm := woodinCollapseCut_mono (κ := κ) (β := β)
        ((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2
      rwa [woodinCollapseCut_eq hp.2] at hm
    · have hm := woodinCollapseCut_mono (κ := κ) (β := β)
        ((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2
      rwa [woodinCollapseCut_eq hq.2] at hm

theorem woodinCollapseCut_dense_preimage {κ β δ D : V}
    (hκ : IsRegularCardinal κ) (hβ : IsRegularCardinal β) [IsOrdinal δ]
    (hβδ : β ⊆ δ) (hD : ForcingDense (woodinCollapse κ β) (woodinCollapseOrder κ β) D) :
    ForcingDense (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
      {p ∈ woodinCollapse κ δ ; woodinCollapseCut κ β p ∈ D} := by
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, fun p hp ↦ ?_⟩
  obtain ⟨q, hq, hqp⟩ := hD.2 _ (woodinCollapseCut_mem hβ hp)
  obtain ⟨hu, hpu, he⟩ := woodinCollapseCut_extension hκ hβ hβδ hp (hD.1 q hq)
    ((pair_mem_reverseInclusionOrder _ _ _).mp hqp).2.2
  exact ⟨p ∪ q, mem_sep_iff.mpr ⟨hu, he.symm ▸ hq⟩,
    (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, hp, hpu⟩⟩

theorem woodinCollapse_initial_generic {κ β δ : V} {G : Set V}
    (hκ : IsRegularCardinal κ) (hβ : IsRegularCardinal β) [IsOrdinal δ]
    (hβδ : β ⊆ δ)
    (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G) :
    IsExternalForcingGeneric (woodinCollapse κ β) (woodinCollapseOrder κ β)
      (woodinCollapseInitialGeneric κ β G) := by
  refine ⟨woodinCollapse_initial_filter hβ hβδ hG.1, fun D hD ↦ ?_⟩
  obtain ⟨p, hp, hpD⟩ := hG.2 _ (woodinCollapseCut_dense_preimage hκ hβ hβδ hD)
  exact ⟨_, woodinCollapseCut_mem_generic hβ hβδ hG.1 hp, (mem_sep_iff.mp hpD).2⟩

end ZFVP
