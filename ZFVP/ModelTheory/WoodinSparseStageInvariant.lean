import ZFVP.ModelTheory.WoodinSparseGeneric
import ZFVP.ModelTheory.WoodinSparseSourceCode
import ZFVP.ModelTheory.WoodinSparseQuotientInputs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
local notation "A" => kpair.π₁ (woodinIterationRec θ)
local notation "K" => kpair.π₂ (woodinIterationRec θ)
local notation "C" => woodinSparseStageCode θ

theorem woodinSparseRealizationMap_checked_forcing_iff
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {k : ℕ} (φ : SetTheorySemisentence k) (v : Fin k → V)
    {p : V} (hp : p ∈ (forcingCodeP A) ‘ θ) :
    p ∈ forcingFormula ((forcingCodeP A) ‘ θ) ((forcingCodeR A) ‘ θ) φ
      (standardTuple (fun i ↦ checkName ((forcingCodet A) ‘ θ) (v i))) ↔
    (woodinSparseRealizationMap θ) ‘ p ∈ forcingFormula ((forcingCodeP C) ‘ θ) ((forcingCodeR C) ‘ θ) φ
      (standardTuple (fun i ↦ checkName ∅ (v i))) := by
  have ht := ((woodinIterationStageCode_valid_le hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)).1
  simpa only [nameAction_checkName_map ht, woodinSparseRealizationMap_top hΩ hAC hθ] using
    woodinSparseRealizationMap_forcingFormula_iff hΩ hAC hθ φ
      (fun i ↦ checkName ((forcingCodet A) ‘ θ) (v i)) (fun i ↦ checkName_isName ht (v i)) hp

theorem woodinIterationRec_stage_le
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsWoodinStage (woodinIterationStage A K θ) := by
  let := hΩ.inaccessible.1
  rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
  · exact (woodinIteration_endpoint_valid hΩ hAC).1.stage θ (mem_succ_self θ)
  · exact ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.stage θ (mem_succ_self θ)

theorem woodinSparseStageCode_stage
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsWoodinStage (woodinIterationStage C K θ) := by
  have hs := woodinIterationRec_stage_le hΩ hAC hθ
  have hc := woodinSparseStageCode_valid hΩ hAC hθ
  have hcheck (t x : V) : (fun j : Fin 1 ↦ checkName t ((![x] : Fin 1 → V) j)) = ![checkName t x] := by
    funext j
    exact Fin.cases rfl (fun k ↦ Fin.elim0 k) j
  simp only [IsWoodinStage, woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code] at hs ⊢
  refine ⟨hc.system.order.preorder θ (mem_succ_self θ), hc.system.tops.top θ (mem_succ_self θ), hs.2.2.1, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, he⟩ := woodinSparseRealizationMap_surjective hΩ hAC hθ q hq
    have hh := (woodinSparseRealizationMap_checked_forcing_iff hΩ hAC hθ regularCardinalFormula ![K ‘ θ] hp).mp
      (by simpa only [hcheck] using hs.2.2.2.1 p hp)
    simpa only [he, woodinSparseStageCode_top hΩ hAC hθ, hcheck] using hh
  · intro q hq
    obtain ⟨p, hp, he⟩ := woodinSparseRealizationMap_surjective hΩ hAC hθ q hq
    have hh := (woodinSparseRealizationMap_checked_forcing_iff hΩ hAC hθ dependentChoiceBelowFormula ![K ‘ θ] hp).mp
      (by simpa only [hcheck] using hs.2.2.2.2 p hp)
    simpa only [he, woodinSparseStageCode_top hΩ hAC hθ, hcheck] using hh

theorem woodinSparseStageCode_stage_small
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsWoodinStageSmall (woodinIterationStage C K θ) := by
  intro ξ hξ hcard
  simp only [woodinIterationStage, woodinStagePoset_code]
  exact woodinSparseStageCode_small hΩ hAC hθ hξ (by
    simpa only [woodinIterationStage, woodinStageCardinal_code] using hcard)

theorem woodinSparseStageCode_all_tops
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ θ) : (forcingCodet C) ‘ i = ∅ := by
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact woodinSparseStageCode_top hΩ hAC hθ
  · rw [← (woodinSparsePrefixCode_valid hΩ hAC hθ).tablet.value_of_subset
      (woodinSparseStageCode_valid hΩ hAC hθ).tablet (woodinSparseStageCode_extends hΩ hAC hθ).subt hi]
    exact woodinSparsePrefixCode_top hΩ hAC hθ hi

theorem woodinSparseStageCode_old_stage
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ θ) :
    woodinIterationStage C K i = woodinIterationStage (woodinSparseStageCode i) (kpair.π₂ (woodinIterationRec i)) i := by
  have hcard := woodinSparseSourceStageCardinals_value hΩ hAC hθ hi
  rw [woodinSparseSourceStageCardinals, woodinSourceCardinals_stage hi] at hcard
  rcases mem_succ_iff.mp hi with rfl | hilow
  · rfl
  · let := IsOrdinal.of_mem hilow
    have hisub : i ⊆ Ω := fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.transitive _ hilow x hx)
    simp only [woodinIterationStage, (woodinSparseStage_old_row hi).1, (woodinSparseStage_old_row hi).2,
      hcard, woodinSparseStageCode_all_tops hΩ hAC hθ hi, woodinSparseStageCode_top hΩ hAC hisub]

theorem woodinSparseStageCode_invariant_of_raw
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {δ : V} (hr : IsWoodinIteration δ (succ θ) A K) :
    IsWoodinIteration δ (succ θ) C K := by
  refine ⟨woodinSparseStageCode_valid hΩ hAC hθ, hr.cardinals, ?_, ?_, hr.inaccessible, hr.bounded, hr.increasing⟩
  · intro i hi
    rw [woodinSparseStageCode_old_stage hΩ hAC hθ hi]
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact woodinSparseStageCode_stage hΩ hAC hθ
    · let := IsOrdinal.of_mem hi
      exact woodinSparseStageCode_stage hΩ hAC (fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.transitive _ hi x hx))
  · intro i hi
    rw [woodinSparseStageCode_old_stage hΩ hAC hθ hi]
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact woodinSparseStageCode_stage_small hΩ hAC hθ
    · let := IsOrdinal.of_mem hi
      exact woodinSparseStageCode_stage_small hΩ hAC (fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.transitive _ hi x hx))

theorem woodinSparseStageCode_invariant
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) :
    IsWoodinIteration Ω (succ θ) C K := by
  let := hΩ.inaccessible.1
  exact woodinSparseStageCode_invariant_of_raw hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ)
    ((woodinIterationExit hΩ hAC).2.1 θ hθ).1

theorem woodinSparseStageCode_endpoint_invariant
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    IsWoodinIteration (succ Ω) (succ Ω) (woodinSparseStageCode Ω) (kpair.π₂ (woodinIterationRec Ω)) := by
  let := hΩ.inaccessible.1
  exact woodinSparseStageCode_invariant_of_raw hΩ hAC (subset_refl Ω) (woodinIteration_endpoint_valid hΩ hAC).1

end ZFVP

