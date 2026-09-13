import ZFVP.ModelTheory.WoodinSourceCode
import ZFVP.ModelTheory.WoodinSparseCanonicalLift

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseSourcePrefixCode (θ : V) : V := woodinSourceCode θ (woodinSparsePrefixCode θ)
noncomputable def woodinSparseSourceStageCode (θ : V) : V := woodinSourceCode (succ θ) (woodinSparseStageCode θ)
noncomputable def woodinSparseSourcePrefixCardinals (θ : V) : V := woodinSourceCardinals θ (woodinIterationCardinalPrefix θ)
noncomputable def woodinSparseSourceStageCardinals (θ : V) : V := woodinSourceCardinals (succ θ) (kpair.π₂ (woodinIterationRec θ))

instance woodinSparseSourcePrefixCode_definable : ℒₛₑₜ-function₁[V] woodinSparseSourcePrefixCode := by
  unfold woodinSparseSourcePrefixCode
  definability
instance woodinSparseSourceStageCode_definable : ℒₛₑₜ-function₁[V] woodinSparseSourceStageCode := by
  unfold woodinSparseSourceStageCode
  definability
instance woodinSparseSourcePrefixCardinals_definable : ℒₛₑₜ-function₁[V] woodinSparseSourcePrefixCardinals := by
  unfold woodinSparseSourcePrefixCardinals
  definability
instance woodinSparseSourceStageCardinals_definable : ℒₛₑₜ-function₁[V] woodinSparseSourceStageCardinals := by
  unfold woodinSparseSourceStageCardinals
  definability

variable {Ω θ : V} [IsOrdinal θ]

theorem woodinSparseSourcePrefixCode_valid (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingIterationCode (woodinSourceIndex θ) (woodinSparseSourcePrefixCode θ) :=
  woodinSourceCode_valid (woodinSparsePrefixCode_valid hΩ hAC hθ)

theorem woodinSparseSourceStageCode_valid (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingIterationCode (succ (woodinSourceIndex θ)) (woodinSparseSourceStageCode θ) := by
  simpa only [woodinSourceIndex_successor, woodinSparseSourceStageCode] using woodinSourceCode_valid (woodinSparseStageCode_valid hΩ hAC hθ)

theorem woodinSparseSourcePrefixCode_row {i : V} (hi : i ∈ θ) :
    (forcingCodeP (woodinSparseSourcePrefixCode θ)) ‘ (woodinSourceIndex i) = (forcingCodeP (woodinSparsePrefixCode θ)) ‘ i ∧
    (forcingCodeR (woodinSparseSourcePrefixCode θ)) ‘ (woodinSourceIndex i) = (forcingCodeR (woodinSparsePrefixCode θ)) ‘ i := by
  simp only [woodinSparseSourcePrefixCode, woodinSourceCode, forcingCodeP_code, forcingCodeR_code,
    woodinInsertSeed_at_sourceIndex hi, and_self]

theorem woodinSparseSourceStageCode_row {i : V} (hi : i ∈ succ θ) :
    (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex i) = (forcingCodeP (woodinSparseStageCode θ)) ‘ i ∧
    (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex i) = (forcingCodeR (woodinSparseStageCode θ)) ‘ i := by
  simp only [woodinSparseSourceStageCode, woodinSourceCode, forcingCodeP_code, forcingCodeR_code,
    woodinInsertSeed_at_sourceIndex hi, and_self]

private theorem sparseStage_tops (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ θ) : (forcingCodet (woodinSparseStageCode θ)) ‘ i = ∅ := by
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact woodinSparseStageCode_top hΩ hAC hθ
  · rw [← (woodinSparsePrefixCode_valid hΩ hAC hθ).tablet.value_of_subset
      (woodinSparseStageCode_valid hΩ hAC hθ).tablet (woodinSparseStageCode_extends hΩ hAC hθ).subt hi]
    exact woodinSparsePrefixCode_top hΩ hAC hθ hi

private theorem source_top_empty {κ s j : V} [IsOrdinal κ]
    (ht : ∀ i ∈ κ, (forcingCodet s) ‘ i = ∅) (hj : j ∈ woodinSourceIndex κ) :
    (forcingCodet (woodinSourceCode κ s)) ‘ j = ∅ := by
  rcases woodinSourceIndex_cases hj with rfl | ⟨i, hi, rfl⟩
  · simp only [woodinSourceCode, forcingCodet_code, woodinInsertSeed_zero]
  · simpa only [woodinSourceCode, forcingCodet_code, woodinInsertSeed_at_sourceIndex hi] using ht i hi

theorem woodinSparseSourcePrefixCode_top (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {j : V} (hj : j ∈ woodinSourceIndex θ) : (forcingCodet (woodinSparseSourcePrefixCode θ)) ‘ j = ∅ :=
  source_top_empty (fun _ hi ↦ woodinSparsePrefixCode_top hΩ hAC hθ hi) hj

theorem woodinSparseSourceStageCode_top (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {j : V} (hj : j ∈ succ (woodinSourceIndex θ)) : (forcingCodet (woodinSparseSourceStageCode θ)) ‘ j = ∅ := by
  apply source_top_empty (fun _ hi ↦ sparseStage_tops hΩ hAC hθ hi)
  simpa only [woodinSourceIndex_successor] using hj

theorem woodinSparseSourcePrefixCode_seed :
    (forcingCodeP (woodinSparseSourcePrefixCode θ)) ‘ ∅ = ({∅} : V) ∧
    (forcingCodeR (woodinSparseSourcePrefixCode θ)) ‘ ∅ = (({∅} : V) ×ˢ {∅}) ∧
    (forcingCodet (woodinSparseSourcePrefixCode θ)) ‘ ∅ = ∅ := by
  simp only [woodinSparseSourcePrefixCode, woodinSourceCode, forcingCodeP_code, forcingCodeR_code,
    forcingCodet_code, woodinInsertSeed_zero, and_self]

theorem woodinSparseSourceStageCode_seed :
    (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ ∅ = ({∅} : V) ∧
    (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ ∅ = (({∅} : V) ×ˢ {∅}) ∧
    (forcingCodet (woodinSparseSourceStageCode θ)) ‘ ∅ = ∅ := by
  simp only [woodinSparseSourceStageCode, woodinSourceCode, forcingCodeP_code, forcingCodeR_code,
    forcingCodet_code, woodinInsertSeed_zero, and_self]

private theorem source_seed_columns {κ s j p : V} [IsOrdinal κ]
    (ht : ∀ i ∈ κ, (forcingCodet s) ‘ i = ∅) (hj : j ∈ woodinSourceIndex κ)
    (hp : p ∈ (forcingCodeP (woodinSourceCode κ s)) ‘ j) :
    ((forcingCodeπ (woodinSourceCode κ s)) ‘ ⟨∅, j⟩ₖ) ‘ p = ∅ ∧
    ((forcingCodeE (woodinSourceCode κ s)) ‘ ⟨∅, j⟩ₖ) ‘ ∅ = ∅ ∧
    ((forcingCodeL (woodinSourceCode κ s)) ‘ ⟨∅, j⟩ₖ) ‘ ⟨p, ∅⟩ₖ = p := by
  have he := source_top_empty ht hj
  simp only [woodinSourceCode, forcingCodeP_code] at hp
  simp only [woodinSourceCode, forcingCodet_code] at he
  simp only [woodinSourceCode, forcingCodeπ_code, forcingCodeE_code, forcingCodeL_code,
    woodinSeedProjections_zero_value hj hp, woodinSeedSections_zero_value hj, woodinSeedLifts_zero_value hj hp, he, and_self]

theorem woodinSparseSourcePrefixCode_seed_columns (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {j p : V} (hj : j ∈ woodinSourceIndex θ) (hp : p ∈ (forcingCodeP (woodinSparseSourcePrefixCode θ)) ‘ j) :
    ((forcingCodeπ (woodinSparseSourcePrefixCode θ)) ‘ ⟨∅, j⟩ₖ) ‘ p = ∅ ∧
    ((forcingCodeE (woodinSparseSourcePrefixCode θ)) ‘ ⟨∅, j⟩ₖ) ‘ ∅ = ∅ ∧
    ((forcingCodeL (woodinSparseSourcePrefixCode θ)) ‘ ⟨∅, j⟩ₖ) ‘ ⟨p, ∅⟩ₖ = p :=
  source_seed_columns (fun _ hi ↦ woodinSparsePrefixCode_top hΩ hAC hθ hi) hj hp

theorem woodinSparseSourceStageCode_seed_columns (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {j p : V} (hj : j ∈ succ (woodinSourceIndex θ)) (hp : p ∈ (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ j) :
    ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨∅, j⟩ₖ) ‘ p = ∅ ∧
    ((forcingCodeE (woodinSparseSourceStageCode θ)) ‘ ⟨∅, j⟩ₖ) ‘ ∅ = ∅ ∧
    ((forcingCodeL (woodinSparseSourceStageCode θ)) ‘ ⟨∅, j⟩ₖ) ‘ ⟨p, ∅⟩ₖ = p := by
  apply source_seed_columns (fun _ hi ↦ sparseStage_tops hΩ hAC hθ hi) ?_ hp
  simpa only [woodinSourceIndex_successor] using hj

theorem woodinSparseSourcePrefixCode_matrices {i j : V} (hi : i ∈ θ) (hj : j ∈ θ) :
    (forcingCodeπ (woodinSparseSourcePrefixCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex j⟩ₖ = (forcingCodeπ (woodinSparsePrefixCode θ)) ‘ ⟨i, j⟩ₖ ∧
    (forcingCodeE (woodinSparseSourcePrefixCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex j⟩ₖ = (forcingCodeE (woodinSparsePrefixCode θ)) ‘ ⟨i, j⟩ₖ ∧
    (forcingCodeL (woodinSparseSourcePrefixCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex j⟩ₖ = (forcingCodeL (woodinSparsePrefixCode θ)) ‘ ⟨i, j⟩ₖ :=
  ⟨woodinSourceCode_projection hi hj, woodinSourceCode_section hi hj, woodinSourceCode_lift hi hj⟩

theorem woodinSparseSourceStageCode_matrices {i j : V} (hi : i ∈ succ θ) (hj : j ∈ succ θ) :
    (forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex j⟩ₖ = (forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨i, j⟩ₖ ∧
    (forcingCodeE (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex j⟩ₖ = (forcingCodeE (woodinSparseStageCode θ)) ‘ ⟨i, j⟩ₖ ∧
    (forcingCodeL (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex j⟩ₖ = (forcingCodeL (woodinSparseStageCode θ)) ‘ ⟨i, j⟩ₖ :=
  ⟨woodinSourceCode_projection hi hj, woodinSourceCode_section hi hj, woodinSourceCode_lift hi hj⟩

theorem woodinSparseSourcePrefixCode_projection (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i j q : V} (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    (hq : q ∈ (forcingCodeP (woodinSparseSourcePrefixCode θ)) ‘ (woodinSourceIndex j)) :
    ((forcingCodeπ (woodinSparseSourcePrefixCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex j⟩ₖ) ‘ q =
      q ↾ (succ (woodinSourceIndex i)) := by
  rw [(woodinSparseSourcePrefixCode_row hj).1] at hq
  rw [(woodinSparseSourcePrefixCode_matrices hi hj).1]
  exact woodinSparsePrefixCode_projection hΩ hAC hθ hi hj hij hq

theorem woodinSparseSourcePrefixCode_section (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i j q : V} (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    (hq : q ∈ (forcingCodeP (woodinSparseSourcePrefixCode θ)) ‘ (woodinSourceIndex i)) :
    ((forcingCodeE (woodinSparseSourcePrefixCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex j⟩ₖ) ‘ q = q := by
  rw [(woodinSparseSourcePrefixCode_row hi).1] at hq
  rw [(woodinSparseSourcePrefixCode_matrices hi hj).2.1]
  exact woodinSparsePrefixCode_section hΩ hAC hθ hi hj hij hq

theorem woodinSparseSourcePrefixCode_lift (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i j q b : V} (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    (hq : q ∈ (forcingCodeP (woodinSparseSourcePrefixCode θ)) ‘ (woodinSourceIndex j))
    (hb : b ∈ (forcingCodeP (woodinSparseSourcePrefixCode θ)) ‘ (woodinSourceIndex i))
    (hle : ⟨b, q ↾ (succ (woodinSourceIndex i))⟩ₖ ∈ (forcingCodeR (woodinSparseSourcePrefixCode θ)) ‘ (woodinSourceIndex i)) :
    ((forcingCodeL (woodinSparseSourcePrefixCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex j⟩ₖ) ‘ ⟨q, b⟩ₖ =
      sparsePrefixReplace (succ (woodinSourceIndex i)) q b := by
  rw [(woodinSparseSourcePrefixCode_row hj).1] at hq
  rw [(woodinSparseSourcePrefixCode_row hi).1] at hb
  rw [(woodinSparseSourcePrefixCode_row hi).2] at hle
  rw [(woodinSparseSourcePrefixCode_matrices hi hj).2.2]
  apply woodinSparsePrefixCode_lift hΩ hAC hθ hi hj hij hq hb
  rwa [woodinSparsePrefixCode_projection hΩ hAC hθ hi hj hij hq]

theorem woodinSparseSourceStageCode_projection (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i q : V} (hi : i ∈ θ)
    (hq : q ∈ (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)) :
    ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ) ‘ q =
      q ↾ (succ (woodinSourceIndex i)) := by
  rw [(woodinSparseSourceStageCode_row (mem_succ_self θ)).1] at hq
  rw [(woodinSparseSourceStageCode_matrices (mem_succ_iff.mpr (Or.inr hi)) (mem_succ_self θ)).1]
  exact woodinSparseStageCode_projection hΩ hAC hθ hi hq

theorem woodinSparseSourceStageCode_section (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i q : V} (hi : i ∈ θ)
    (hq : q ∈ (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex i)) :
    ((forcingCodeE (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ) ‘ q = q := by
  rw [(woodinSparseSourceStageCode_row (mem_succ_iff.mpr (Or.inr hi))).1] at hq
  rw [(woodinSparseSourceStageCode_matrices (mem_succ_iff.mpr (Or.inr hi)) (mem_succ_self θ)).2.1]
  exact woodinSparseStageCode_section hΩ hAC hθ hi hq

theorem woodinSparseSourceStageCode_lift (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i q b : V} (hi : i ∈ succ θ)
    (hq : q ∈ (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
    (hb : b ∈ (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex i))
    (hle : ⟨b, ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ) ‘ q⟩ₖ ∈
      (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex i)) :
    ((forcingCodeL (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ) ‘ ⟨q, b⟩ₖ =
      sparsePrefixReplace (succ (woodinSourceIndex i)) q b := by
  rw [(woodinSparseSourceStageCode_row (mem_succ_self θ)).1] at hq
  rw [(woodinSparseSourceStageCode_row hi).1] at hb
  rw [(woodinSparseSourceStageCode_row hi).2, (woodinSparseSourceStageCode_matrices hi (mem_succ_self θ)).1] at hle
  rw [(woodinSparseSourceStageCode_matrices hi (mem_succ_self θ)).2.2]
  exact woodinSparseStageCode_lift hΩ hAC hθ hi hq hb hle

theorem woodinSparseSourcePrefixCardinals_table :
    IsIterationTable (woodinSourceIndex θ) (woodinSparseSourcePrefixCardinals θ) := woodinSourceCardinals_table _ _

theorem woodinSparseSourceStageCardinals_table :
    IsIterationTable (succ (woodinSourceIndex θ)) (woodinSparseSourceStageCardinals θ) := by
  simpa only [woodinSourceIndex_successor, woodinSparseSourceStageCardinals] using
    woodinSourceCardinals_table (succ θ) (kpair.π₂ (woodinIterationRec θ))

theorem woodinSparseSourcePrefixCardinals_seed :
    (woodinSparseSourcePrefixCardinals θ) ‘ ∅ = woodinSeedCardinal := woodinSourceCardinals_seed _ _

theorem woodinSparseSourceStageCardinals_seed :
    (woodinSparseSourceStageCardinals θ) ‘ ∅ = woodinSeedCardinal := woodinSourceCardinals_seed _ _

theorem woodinSparseSourcePrefixCardinals_value (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ θ) : (woodinSparseSourcePrefixCardinals θ) ‘ (woodinSourceIndex i) =
      (kpair.π₂ (woodinIterationRec i)) ‘ i := by
  rw [woodinSparseSourcePrefixCardinals, woodinSourceCardinals_stage hi]
  have hh := woodinIterationHistory_of_stages (fun j hj ↦ ((woodinIterationExit hΩ hAC).2.1 j (hθ j hj)).1)
  simpa only [woodinIterationCardinalPrefix, woodinIterationHistory_cardinal_value hi] using
    hh.cardinal_union_value hi (mem_succ_self i)

theorem woodinSparseSourceStageCardinals_value (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ θ) : (woodinSparseSourceStageCardinals θ) ‘ (woodinSourceIndex i) =
      (kpair.π₂ (woodinIterationRec i)) ‘ i := by
  rw [woodinSparseSourceStageCardinals, woodinSourceCardinals_stage hi]
  rcases mem_succ_iff.mp hi with rfl | hi
  · rfl
  · let := hΩ.inaccessible.1
    let := IsOrdinal.of_mem hi
    have hh := woodinIterationHistory_of_stages (fun j hj ↦ ((woodinIterationExit hΩ hAC).2.1 j (hθ j hj)).1)
    have he := (woodinIterationRec_extends_previous hh hi).2
    have hs := ((woodinIterationExit hΩ hAC).2.1 i (hθ i hi)).1
    rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
    · exact (hs.cardinals.value_of_subset (woodinIteration_endpoint_valid hΩ hAC).1.cardinals he (mem_succ_self i)).symm
    · exact (hs.cardinals.value_of_subset ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.cardinals he (mem_succ_self i)).symm
end ZFVP

