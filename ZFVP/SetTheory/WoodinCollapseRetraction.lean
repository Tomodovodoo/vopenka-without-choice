import ZFVP.SetTheory.WoodinCollapseProjection
import ZFVP.SetTheory.ForcingRetraction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinCollapseProjection (κ β δ : V) : V :=
  definableGraph (woodinCollapse κ δ) (woodinCollapseCut κ β) (by definability)

instance woodinCollapseProjection_definable : ℒₛₑₜ-function₃[V] woodinCollapseProjection := by
  have h : ℒₛₑₜ-relation₄[V] (fun f κ β δ ↦ ∀ z,
      z ∈ f ↔ ∃ p ∈ woodinCollapse κ δ, z = ⟨p, woodinCollapseCut κ β p⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [woodinCollapseProjection, mem_definableGraph_iff]
  rfl

theorem woodinCollapseProjection_value {κ β δ p : V} (hp : p ∈ woodinCollapse κ δ) :
    (woodinCollapseProjection κ β δ) ‘ p = woodinCollapseCut κ β p :=
  value_definableGraph _ _ _ hp

theorem woodinCollapse_retraction {κ β δ : V} (hκ : IsRegularCardinal κ)
    (hβ : IsRegularCardinal β) [IsOrdinal δ] (hβδ : β ⊆ δ) :
    IsForcingRetraction (woodinCollapse κ β) (woodinCollapseOrder κ β)
      (woodinCollapse κ δ) (woodinCollapseOrder κ δ) (woodinCollapseProjection κ β δ) := by
  let := hβ.1.1
  refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ (fun p hp ↦ woodinCollapseCut_mem hβ hp),
    woodinCollapse_mono hβδ, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [woodinCollapseProjection_value (woodinCollapse_mono hβδ p hp), woodinCollapseCut_eq hp]
  · intro p hp q hq hpq
    rw [woodinCollapseProjection_value hp, woodinCollapseProjection_value hq]
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨woodinCollapseCut_mem hβ hp,
      woodinCollapseCut_mem hβ hq,
      woodinCollapseCut_mono ((pair_mem_reverseInclusionOrder _ _ _).mp hpq).2.2⟩
  · intro q hq p hp
    rw [woodinCollapseProjection_value hq]
    constructor
    · intro hqp
      have hm := woodinCollapseCut_mono (κ := κ) (β := β)
        ((pair_mem_reverseInclusionOrder _ _ _).mp hqp).2.2
      rw [woodinCollapseCut_eq hp] at hm
      exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨woodinCollapseCut_mem hβ hq, hp, hm⟩
    · intro hqp
      exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, woodinCollapse_mono hβδ p hp,
        subset_trans ((pair_mem_reverseInclusionOrder _ _ _).mp hqp).2.2
          (woodinCollapseCut_subset _ _ _)⟩
  · intro q hq p hp hpq
    rw [woodinCollapseProjection_value hq] at hpq
    obtain ⟨hu, hqu, he⟩ := woodinCollapseCut_extension hκ hβ hβδ hq hp
      ((pair_mem_reverseInclusionOrder _ _ _).mp hpq).2.2
    exact ⟨q ∪ p, hu, (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, hq, hqu⟩,
      (woodinCollapseProjection_value hu).trans he⟩

end ZFVP
