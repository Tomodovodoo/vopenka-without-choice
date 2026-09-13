import ZFVP.ModelTheory.NormalizedMapDefinability
import ZFVP.ModelTheory.ForcingLimitCode
import ZFVP.SetTheory.ForcingRetractionFixedPoints

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The target coordinate carriers recovered from an internal map table. -/
noncomputable def forcingNormalizationCarriers (θ s m : V) : V :=
  definableGraph θ (fun i ↦ forcingMapFixedPoints ((forcingCodeP s) ‘ i) (m ‘ i)) (by definability)

instance forcingNormalizationCarriers_definable : ℒₛₑₜ-function₃[V] forcingNormalizationCarriers := by
  have h : ℒₛₑₜ-relation₄[V] (fun N θ s m ↦ ∀ z, z ∈ N ↔ ∃ i ∈ θ,
      z = ⟨i, forcingMapFixedPoints ((forcingCodeP s) ‘ i) (m ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingNormalizationCarriers (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingNormalizationCarriers, mem_definableGraph_iff]

theorem forcingNormalizationCarriers_value {θ s m i : V} (hi : i ∈ θ) :
    (forcingNormalizationCarriers θ s m) ‘ i = forcingMapFixedPoints ((forcingCodeP s) ‘ i) (m ‘ i) :=
  value_definableGraph _ _ _ hi

/-- Induction invariant for specified coordinate normalizers of the source code. -/
structure IsForcingNormalizationFamily (θ s m : V) : Prop where
  table : IsIterationTable θ m
  retraction : (∀ i ∈ θ,
    IsForcingRetraction (forcingMapFixedPoints ((forcingCodeP s) ‘ i) (m ‘ i))
      (forcingOrderRestriction (forcingMapFixedPoints ((forcingCodeP s) ‘ i) (m ‘ i)) ((forcingCodeR s) ‘ i))
      ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i) (m ‘ i))
  equivalent : (∀ i ∈ θ, ∀ p ∈ (forcingCodeP s) ‘ i,
    ⟨(m ‘ i) ‘ p, p⟩ₖ ∈ (forcingCodeR s) ‘ i ∧ ⟨p, (m ‘ i) ‘ p⟩ₖ ∈ (forcingCodeR s) ‘ i)
  fixesTop : (∀ i ∈ θ, (m ‘ i) ‘ ((forcingCodet s) ‘ i) = (forcingCodet s) ‘ i)
  projection : (∀ j ∈ θ, ∀ i ∈ j, i ∈ θ → ∀ p ∈ (forcingCodeP s) ‘ j,
    ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ j) ‘ p) = (m ‘ i) ‘ (((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ p))
  sectionCoherent : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP s) ‘ i,
    (m ‘ j) ‘ (((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ‘ p) = ((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ i) ‘ p))

variable {θ s m : V}

theorem IsForcingNormalizationFamily.inclusion (h : IsForcingNormalizationFamily θ s m) :
    ∀ i ∈ θ, (forcingNormalizationCarriers θ s m) ‘ i ⊆ (forcingCodeP s) ‘ i := by
  intro i hi
  rw [forcingNormalizationCarriers_value hi]
  exact (h.retraction i hi).inclusion

theorem IsForcingNormalizationFamily.maps (h : IsForcingNormalizationFamily θ s m) :
    ∀ i ∈ θ, m ‘ i ∈ ((forcingNormalizationCarriers θ s m) ‘ i) ^ ((forcingCodeP s) ‘ i) := by
  intro i hi
  rw [forcingNormalizationCarriers_value hi]
  exact (h.retraction i hi).maps

theorem IsForcingNormalizationFamily.fixes (h : IsForcingNormalizationFamily θ s m) :
    ∀ i ∈ θ, ∀ p ∈ (forcingNormalizationCarriers θ s m) ‘ i, (m ‘ i) ‘ p = p := by
  intro i hi p hp
  rw [forcingNormalizationCarriers_value hi] at hp
  exact (h.retraction i hi).fixes p hp

end ZFVP
