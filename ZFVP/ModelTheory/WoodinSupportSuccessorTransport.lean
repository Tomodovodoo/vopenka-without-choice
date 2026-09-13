import ZFVP.ModelTheory.NormalizedCanonicalTwoStep
import ZFVP.ModelTheory.WoodinNormalizedSupport
import ZFVP.ModelTheory.ForcingRetractionCutoff
import ZFVP.ModelTheory.WoodinNormalizedSuccessorCanonical

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V}

local notation "P" => (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ
local notation "R" => (forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ
local notation "one" => (forcingCodet (woodinNormalizedStageCode θ)) ‘ θ
local notation "A" => woodinNormalizedSupportCodes θ
local notation "B" => woodinNormalizedSupportOrder θ
local notation "top" => woodinNormalizedSupportTop θ
local notation "f" => woodinNormalizedSupportEncode θ
local notation "P₀" => (forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ
local notation "R₀" => (forcingCodeR (kpair.π₁ (woodinIterationRec θ))) ‘ θ

theorem woodinNormalizedStage_retraction
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) :
    IsForcingRetraction P R P₀ R₀ (woodinNormalizationRec θ) := by
  have hr := (woodinNormalizationHistory_family hΩ hAC θ hθ).retraction θ (mem_succ_self θ)
  simpa only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeP_code,
    forcingCodeR_code, forcingNormalizationOrders_value (mem_succ_self θ),
    forcingNormalizationCarriers_value (mem_succ_self θ),
    woodinNormalizationHistory_value (mem_succ_self θ)] using hr

theorem woodinNormalizedStage_checked_iff
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V) {p : V} (hp : p ∈ P) :
    p ∈ forcingFormula P₀ R₀ φ (standardTuple (fun i ↦ checkName one (v i))) ↔
      p ∈ forcingFormula P R φ (standardTuple (fun i ↦ checkName one (v i))) := by
  have hr := woodinNormalizedStage_retraction hΩ hAC hθ
  have hv := woodinNormalizedStageCode_valid hΩ hAC hθ
  have hs := ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.code
  have he := (woodinNormalizationHistory_family hΩ hAC θ hθ).equivalent θ (mem_succ_self θ)
  simp only [woodinNormalizationHistory_value (mem_succ_self θ)] at he
  have hh := hr.forcingFormula_check_iff (hs.system.order.preorder θ (mem_succ_self θ))
    (hv.system.order.preorder θ (mem_succ_self θ)) he
    (hv.system.tops.top θ (mem_succ_self θ)).1 φ v (hr.inclusion p hp)
  rwa [hr.fixes p hp] at hh

theorem woodinNormalizedStage_prefix_cutoff
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) (κ : V) :
    woodinPrefixCutoff P₀ R₀ ((forcingCodet (kpair.π₁ (woodinIterationRec θ))) ‘ θ) κ =
      woodinPrefixCutoff P R one κ := by
  have hr := woodinNormalizedStage_retraction hΩ hAC hθ
  have hv := woodinNormalizedStageCode_valid hΩ hAC hθ
  have hs := ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.code
  have he := (woodinNormalizationHistory_family hΩ hAC θ hθ).equivalent θ (mem_succ_self θ)
  simp only [woodinNormalizationHistory_value (mem_succ_self θ)] at he
  have hh := hr.prefix_cutoff (hs.system.order.preorder θ (mem_succ_self θ))
    (hv.system.order.preorder θ (mem_succ_self θ)) he
    (hv.system.tops.top θ (mem_succ_self θ)).1 κ
  have hone : one = (forcingCodet (kpair.π₁ (woodinIterationRec θ))) ‘ θ := by
    simp only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodet_code]
  rw [← hone]
  exact hh

theorem woodinNormalizedStage_subset :
    P ⊆ (forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ := by
  unfold woodinNormalizedStageCode forcingNormalizedCode
  rw [forcingCodeP_code, forcingNormalizationCarriers_value (mem_succ_self θ)]
  exact sep_subset

theorem woodinNormalizedStage_small {ξ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (hξ : IsChoicelessInaccessible ξ) (hc : (kpair.π₂ (woodinIterationRec θ)) ‘ θ ∈ ξ) :
    P ∈ hierarchy ξ := by
  let := hξ.1
  have hs := ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.small θ (mem_succ_self θ) ξ hξ
  simp only [woodinIterationStage, woodinStagePoset_code, woodinStageCardinal_code] at hs
  exact subset_mem_hierarchy_limit hξ.rankCriterion.2.2.1 (hs hc) woodinNormalizedStage_subset

theorem woodinSupportCodes_mem_hierarchy {ξ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hξ : IsChoicelessInaccessible ξ) (hθξ : θ ∈ ξ) : A ∈ hierarchy ξ := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  let := hξ.1
  exact subset_mem_hierarchy_limit hξ.rankCriterion.2.2.1 (hierarchy_mem hθξ)
    (woodinNormalizedSupport_rank hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ) hlim hinac).2.1

theorem woodinNormalizedDirect_small {ξ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hξ : IsChoicelessInaccessible ξ) (hθξ : θ ∈ ξ) : P ∈ hierarchy ξ := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ (hx.2.1 i (IsOrdinal.toIsTransitive.mem_trans hi hθ)).1)
  have he := hs.index_eq_regular_limit (ordinal_limit_of_not_successor hlim) hinac.regular
  apply woodinNormalizedStage_small hΩ hAC hθ hξ
  rw [woodinIterationRec_direct h0 hlim hinac, kpair.π₂_kpair, forcingFamilyNext_new, ← he]
  exact hθξ

theorem woodinDirect_stage_cardinal
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    (kpair.π₂ (woodinIterationRec θ)) ‘ θ = θ := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ (hx.2.1 i (IsOrdinal.toIsTransitive.mem_trans hi hθ)).1)
  rw [woodinIterationRec_direct h0 hlim hinac, kpair.π₂_kpair, forcingFamilyNext_new]
  exact (hs.index_eq_regular_limit (ordinal_limit_of_not_successor hlim) hinac.regular).symm

theorem woodinNormalizedDirect_cutoff_exists
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    ∃ c ∈ Ω, IsWoodinPrefixCutoff P R one θ c := by
  have hv := woodinNormalizedStageCode_valid hΩ hAC hθ
  have hR := hv.system.order.preorder θ (mem_succ_self θ)
  have ht := hv.system.tops.top θ (mem_succ_self θ)
  have hP := woodinNormalizedDirect_small hΩ hAC hθ h0 hlim hinac hΩ.inaccessible hθ
  let := hΩ.inaccessible.1
  have hrel : R ∈ hierarchy Ω := subset_mem_hierarchy_limit hΩ.inaccessible.rankCriterion.2.2.1
    (prod_mem_hierarchy_limit hΩ.inaccessible.rankCriterion.2.2.1 hP hP) hR.1
  have hs := ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.stage θ (mem_succ_self θ)
  have hecard := woodinDirect_stage_cardinal hΩ hAC hθ h0 hlim hinac
  have hreg := hs.2.2.2.1
  have hDC := hs.2.2.2.2
  simp only [woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code, hecard] at hreg hDC
  have hone : one = (forcingCodet (kpair.π₁ (woodinIterationRec θ))) ‘ θ := by
    simp only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodet_code]
  have htuple (o : V) : (fun i : Fin 1 ↦ checkName o (![θ] i)) = ![checkName o θ] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  apply hΩ.strictPrefixCutoff hR ht hP hrel hθ
  · intro p hp
    have hh := woodinNormalizedStage_checked_iff hΩ hAC hθ regularCardinalFormula ![θ] hp
    rw [htuple] at hh
    exact hh.mp (by simpa only [hone] using hreg p (woodinNormalizedStage_subset p hp))
  · intro p hp
    have hh := woodinNormalizedStage_checked_iff hΩ hAC hθ dependentChoiceBelowFormula ![θ] hp
    rw [htuple] at hh
    exact hh.mp (by simpa only [hone] using hDC p (woodinNormalizedStage_subset p hp))

/-- Direct-limit compression preserves the actual least successor cutoff. -/
theorem woodinSupport_prefix_cutoff
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (κ : V) : woodinPrefixCutoff P R one κ = woodinPrefixCutoff A B top κ := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hv := woodinNormalizedStageCode_valid hΩ hAC hθ
  have hi := (woodinNormalizedSupportMap_isomorphism hΩ hAC hsub h0 hlim hinac).inverse
  exact hi.prefix_cutoff (hv.system.order.preorder θ (mem_succ_self θ))
    (woodinNormalizedSupportOrder_preorder hΩ hAC hsub)
    (hv.system.tops.top θ (mem_succ_self θ))
    (woodinNormalizedSupportTop_spec hΩ hAC hθ h0 hlim hinac) rfl κ

/-- The original source, its normalization, and direct compression select
the same cutoff, despite the first map being only an equivalent retraction. -/
theorem woodinSupport_source_prefix_cutoff
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (κ : V) :
    woodinPrefixCutoff P₀ R₀ ((forcingCodet (kpair.π₁ (woodinIterationRec θ))) ‘ θ) κ =
      woodinPrefixCutoff A B top κ :=
  (woodinNormalizedStage_prefix_cutoff hΩ hAC hθ κ).trans
    (woodinSupport_prefix_cutoff hΩ hAC hθ h0 hlim hinac κ)

/-- The normalized successor over the compressed direct stage uses its own
canonical cutoff and iterand. The cutoff rank hypotheses remain explicit. -/
theorem woodinSupport_normalized_successor
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (κ : V)
    (hδ : IsChoicelessInaccessible (woodinPrefixCutoff P R one κ))
    (hP : P ∈ hierarchy (woodinPrefixCutoff P R one κ))
    (hA : A ∈ hierarchy (woodinPrefixCutoff P R one κ)) :
    let δ := woodinPrefixCutoff P R one κ
    let ε := woodinPrefixCutoff A B top κ
    let U := saturatedWoodinPrefixPosetName P R one κ δ
    let W := saturatedWoodinPrefixPosetName A B top κ ε
    IsForcingIsomorphism (normalizedNameTwoStep P R one δ U)
      (nameTwoStepOrderOn P R (saturatedWoodinPrefixOrderName P R one κ δ)
        (normalizedNameTwoStep P R one δ U))
      (normalizedNameTwoStep A B top ε W)
      (nameTwoStepOrderOn A B (saturatedWoodinPrefixOrderName A B top κ ε)
        (normalizedNameTwoStep A B top ε W))
      (normalizedTwoStepIsoMap P R one δ U A B top f) := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hv := woodinNormalizedStageCode_valid hΩ hAC hθ
  have hi := (woodinNormalizedSupportMap_isomorphism hΩ hAC hsub h0 hlim hinac).inverse
  exact normalizedPrefixSuccessor_isomorphism hi (hv.system.order.preorder θ (mem_succ_self θ))
    (woodinNormalizedSupportOrder_preorder hΩ hAC hsub)
    (hv.system.tops.top θ (mem_succ_self θ))
    (woodinNormalizedSupportTop_spec hΩ hAC hθ h0 hlim hinac) rfl hδ hP hA

theorem woodinSupport_normalized_successor_of_cutoff {c : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hc : IsWoodinPrefixCutoff P R one θ c) :
    let δ := woodinPrefixCutoff P R one θ
    let ε := woodinPrefixCutoff A B top θ
    let U := saturatedWoodinPrefixPosetName P R one θ δ
    let W := saturatedWoodinPrefixPosetName A B top θ ε
    IsForcingIsomorphism (normalizedNameTwoStep P R one δ U)
      (nameTwoStepOrderOn P R (saturatedWoodinPrefixOrderName P R one θ δ)
        (normalizedNameTwoStep P R one δ U))
      (normalizedNameTwoStep A B top ε W)
      (nameTwoStepOrderOn A B (saturatedWoodinPrefixOrderName A B top θ ε)
        (normalizedNameTwoStep A B top ε W))
      (normalizedTwoStepIsoMap P R one δ U A B top f) := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hd := (woodinPrefixCutoff_spec hc).2.1
  exact woodinSupport_normalized_successor hΩ hAC hθ h0 hlim hinac θ hd.2.1
    (woodinNormalizedDirect_small hΩ hAC hθ h0 hlim hinac hd.2.1 hd.1)
    (woodinSupportCodes_mem_hierarchy hΩ hAC hθ (ordinal_limit_of_not_successor hlim) hinac hd.2.1 hd.1)

/-- The actual compressed direct stage and the normalized source have
isomorphic canonical successors, with all cutoff and rank obligations proved. -/
theorem woodinSupport_actual_successor_isomorphism
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    let δ := woodinPrefixCutoff P R one θ
    let ε := woodinPrefixCutoff A B top θ
    let U := saturatedWoodinPrefixPosetName P R one θ δ
    let W := saturatedWoodinPrefixPosetName A B top θ ε
    IsForcingIsomorphism (normalizedNameTwoStep P R one δ U)
      (nameTwoStepOrderOn P R (saturatedWoodinPrefixOrderName P R one θ δ)
        (normalizedNameTwoStep P R one δ U))
      (normalizedNameTwoStep A B top ε W)
      (nameTwoStepOrderOn A B (saturatedWoodinPrefixOrderName A B top θ ε)
        (normalizedNameTwoStep A B top ε W))
      (normalizedTwoStepIsoMap P R one δ U A B top f) := by
  obtain ⟨c, _, hc⟩ := woodinNormalizedDirect_cutoff_exists hΩ hAC hθ h0 hlim hinac
  exact woodinSupport_normalized_successor_of_cutoff hΩ hAC hθ h0 hlim hinac hc

/-- The existing normalized recursion at the next stage is isomorphic to
the canonical successor over the compressed direct stage. -/
theorem woodinSupport_recursive_successor_isomorphism
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    let δ := woodinPrefixCutoff P R one θ
    let ε := woodinPrefixCutoff A B top θ
    let U := saturatedWoodinPrefixPosetName P R one θ δ
    let W := saturatedWoodinPrefixPosetName A B top θ ε
    IsForcingIsomorphism
      ((forcingCodeP (woodinNormalizedStageCode (succ θ))) ‘ (succ θ))
      ((forcingCodeR (woodinNormalizedStageCode (succ θ))) ‘ (succ θ))
      (normalizedNameTwoStep A B top ε W)
      (nameTwoStepOrderOn A B (saturatedWoodinPrefixOrderName A B top θ ε)
        (normalizedNameTwoStep A B top ε W))
      (normalizedTwoStepIsoMap P R one δ U A B top f) := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hc := woodinNormalizedStage_successor_eq hΩ hAC hθ
  dsimp only at hc ⊢
  rw [woodinDirect_stage_cardinal hΩ hAC hθ h0 hlim hinac] at hc
  rw [hc.1, hc.2]
  exact woodinSupport_actual_successor_isomorphism hΩ hAC hθ h0 hlim hinac

end ZFVP
