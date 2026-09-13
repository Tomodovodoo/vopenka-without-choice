import ZFVP.ModelTheory.WoodinSparseInactive
import ZFVP.ModelTheory.WoodinSparseQuotientInputs
import ZFVP.ModelTheory.WoodinSparseSourceCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def sparseCarrierCut (P a : V) : V :=
  sep P (fun p ↦ domain p ⊆ a) (by definability)

instance sparseCarrierCut_definable : ℒₛₑₜ-function₂[V] sparseCarrierCut := by
  have hd : ℒₛₑₜ-relation₃[V] (fun C P a ↦ ∀ p, p ∈ C ↔ p ∈ P ∧ domain p ⊆ a) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = sparseCarrierCut (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [sparseCarrierCut, mem_sep_iff]
theorem mem_sparseCarrierCut_iff {P a p : V} :
    p ∈ sparseCarrierCut P a ↔ p ∈ P ∧ domain p ⊆ a := by
  simp only [sparseCarrierCut, mem_sep_iff]

variable {Ω θ : V} [IsOrdinal θ]
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ

theorem woodinSparseStageCode_carrier_subset
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ θ) :
    (forcingCodeP (woodinSparseStageCode i)) ‘ i ⊆ P := by
  rw [← (woodinSparseStage_old_row hi).1]
  rcases mem_succ_iff.mp hi with he | hi
  · subst i
    exact subset_refl _
  · intro p hp
    have hh := (woodinSparseStageCode_valid hΩ hAC hθ).system.split.secMaps
      i (mem_succ_iff.mpr (Or.inr hi)) θ (mem_succ_self θ)
      (IsOrdinal.toIsTransitive.transitive _ hi) p hp
    rwa [woodinSparseStageCode_section hΩ hAC hθ hi hp] at hh

theorem woodinSparseStageCode_carrier_recovery
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ θ) :
    (forcingCodeP (woodinSparseStageCode i)) ‘ i =
      sparseCarrierCut P (succ (woodinSourceIndex i)) := by
  let := IsOrdinal.of_mem hi
  have hisub : i ⊆ Ω := subset_trans (IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hi)) hθ
  apply mem_ext_iff.mpr
  intro p
  rw [mem_sparseCarrierCut_iff]
  constructor
  · intro hp
    exact ⟨woodinSparseStageCode_carrier_subset hΩ hAC hθ hi p hp,
      (woodinSparseStageCode_sparse hΩ hAC hisub hp).2.1⟩
  · rintro ⟨hp, hd⟩
    rcases mem_succ_iff.mp hi with he | hi
    · subst i
      exact hp
    · let := (woodinSparseStageCode_sparse hΩ hAC hθ hp).1
      have hh := woodinSparseStageCode_restrict_mem hΩ hAC hθ hi hp
      rwa [IsFunction.restrict_eq_self p _ hd] at hh

theorem woodinSparseStageCode_order_restriction
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i p q : V} (hi : i ∈ succ θ)
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode i)) ‘ i)
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode i)) ‘ i) :
    ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode θ)) ‘ θ ↔
      ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode i)) ‘ i := by
  rcases mem_succ_iff.mp hi with he | hi
  · subst i
    rfl
  · have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
    have hpθ := woodinSparseStageCode_carrier_subset hΩ hAC hθ hi' p hp
    have hq' : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ i := (woodinSparseStage_old_row hi').1 ▸ hq
    have hh := (woodinSparseStageCode_valid hΩ hAC hθ).system.order.below
      i hi' θ (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi) p hpθ q hq'
    rw [woodinSparseStageCode_section hΩ hAC hθ hi hq',
      woodinSparseStageCode_projection hΩ hAC hθ hi hpθ, (woodinSparseStage_old_row hi').2] at hh
    let := IsOrdinal.of_mem hi
    have hisub : i ⊆ Ω := subset_trans (IsOrdinal.toIsTransitive.transitive _ hi) hθ
    have hs := woodinSparseStageCode_sparse hΩ hAC hisub hp
    let := hs.1
    rwa [IsFunction.restrict_eq_self p _ hs.2.1] at hh

end ZFVP



