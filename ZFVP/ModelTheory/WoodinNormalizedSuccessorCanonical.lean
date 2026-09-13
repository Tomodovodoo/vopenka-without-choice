import ZFVP.ModelTheory.NormalizedRetractionCanonical
import ZFVP.ModelTheory.WoodinNormalizedCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω k s K m : V} [IsOrdinal k]
local notation "P" => (forcingCodeP s) ‘ k
local notation "R" => (forcingCodeR s) ‘ k
local notation "o" => (forcingCodet s) ‘ k
local notation "κ" => K ‘ k
local notation "N" => forcingMapFixedPoints P (m ‘ k)
local notation "T" => forcingOrderRestriction N R
local notation "d" => woodinPrefixCutoff N T o κ
local notation "Q" => saturatedWoodinPrefixPosetName N T o κ d
local notation "S" => saturatedWoodinPrefixOrderName N T o κ d
local notation "s'" => woodinIterationSuccessor k s K
local notation "m'" => woodinNormalizationSuccessor k s K m
local notation "C" => forcingNormalizedCode (succ (succ k)) s' m'

theorem woodinNormalizedSuccessor_carrier_order
    (hΩ : IsWoodinSupercompact Ω) (hs : IsWoodinIteration Ω (succ k) s K)
    (hm : IsForcingNormalizationFamily (succ k) s m) :
    (forcingCodeP C) ‘ (succ k) = normalizedNameTwoStep N T o d Q ∧
      (forcingCodeR C) ‘ (succ k) = nameTwoStepOrderOn N T S (normalizedNameTwoStep N T o d Q) := by
  have hr := hm.retraction k (mem_succ_self k)
  obtain ⟨hR, ht, hc, hP, hκc, hκ⟩ := hs.normalizationSuccessor_inputs hΩ
  have hT := forcingOrderRestriction_preorder hR hr.inclusion
  have ho : o ∈ N := mem_sep_iff.mpr ⟨ht.1, hm.fixesTop k (mem_succ_self k)⟩
  have he := hm.equivalent k (mem_succ_self k)
  have hd := hr.prefix_cutoff hR hT he ho κ
  rw [← hd]
  have hrnew := hs.normalizationSuccessor_retraction hΩ hr hT ho he
  have hI := saturatedWoodinPrefix_iterand hR ht hc hP hκc hκ
  have hI' := hr.iterand_nameAction hR hT he hI
  have hpre := normalizedNameTwoStep_preorder (δ := woodinPrefixCutoff P R o κ)
    hT (hr.top_of_mem ht ho) hI'.posetName hI'.orderName hI'.preorder
  rw [hr.normalized_prefix_order hR hT he ht ho hc hP hκc,
    hr.normalized_prefix_carrier hR hT he ht ho hc hP hκc] at hrnew hpre
  simp only [forcingNormalizedCode, forcingCodeP_code, forcingCodeR_code,
    forcingNormalizationOrders_value (mem_succ_self (succ k)),
    forcingNormalizationCarriers_value (mem_succ_self (succ k)), woodinNormalizationSuccessor_new]
  constructor
  · exact hrnew.fixedPoints_eq
  · rw [hrnew.fixedPoints_eq]
    exact hrnew.orderRestriction_eq hpre

theorem woodinNormalizationHistory_successor (k : V) [IsOrdinal k] :
    woodinNormalizationHistory (succ (succ k)) =
      woodinNormalizationSuccessor k (woodinIterationPrefix (succ k))
        (woodinIterationCardinalPrefix (succ k)) (woodinNormalizationHistory (succ k)) := by
  rw [woodinNormalizationHistory_next, woodinNormalizationRec_rule]
  have hn : succ k ≠ (∅ : V) := by
    intro he
    have hh := mem_succ_self k
    rw [he] at hh
    exact not_mem_empty hh
  simp only [woodinNormalizationRule, ite_eq_right hn, sUnion_succ_of_transitive,
    ite_true, woodinNormalizationSuccessor]

theorem woodinNormalizedStage_successor_carrier_order
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω) :
    let s := woodinIterationPrefix (succ k)
    let K := woodinIterationCardinalPrefix (succ k)
    let m := woodinNormalizationHistory (succ k)
    let base := forcingMapFixedPoints ((forcingCodeP s) ‘ k) (m ‘ k)
    let rel := forcingOrderRestriction base ((forcingCodeR s) ‘ k)
    let one := (forcingCodet s) ‘ k
    let δ := woodinPrefixCutoff base rel one (K ‘ k)
    let iter := saturatedWoodinPrefixPosetName base rel one (K ‘ k) δ
    let ord := saturatedWoodinPrefixOrderName base rel one (K ‘ k) δ
    (forcingCodeP (woodinNormalizedStageCode (succ k))) ‘ (succ k) = normalizedNameTwoStep base rel one δ iter ∧
      (forcingCodeR (woodinNormalizedStageCode (succ k))) ‘ (succ k) =
        nameTwoStepOrderOn base rel ord (normalizedNameTwoStep base rel one δ iter) := by
  let := hΩ.inaccessible.1
  have hsub : succ k ⊆ Ω := by
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hk
    · exact IsOrdinal.toIsTransitive.mem_trans hi hk
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hsub i hi)).1)
  have hm := woodinNormalizationHistory_actual_prefix hΩ hAC hsub
  have hh := woodinNormalizedSuccessor_carrier_order hΩ hs hm
  simpa only [woodinNormalizedStageCode, woodinIterationRec_successor, kpair.π₁_kpair,
    woodinNormalizationHistory_successor] using hh

theorem woodinNormalizedStage_successor_eq
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω) :
    let base := (forcingCodeP (woodinNormalizedStageCode k)) ‘ k
    let rel := (forcingCodeR (woodinNormalizedStageCode k)) ‘ k
    let one := (forcingCodet (woodinNormalizedStageCode k)) ‘ k
    let card := (kpair.π₂ (woodinIterationRec k)) ‘ k
    let cut := woodinPrefixCutoff base rel one card
    let iter := saturatedWoodinPrefixPosetName base rel one card cut
    let ord := saturatedWoodinPrefixOrderName base rel one card cut
    (forcingCodeP (woodinNormalizedStageCode (succ k))) ‘ (succ k) = normalizedNameTwoStep base rel one cut iter ∧
      (forcingCodeR (woodinNormalizedStageCode (succ k))) ‘ (succ k) =
        nameTwoStepOrderOn base rel ord (normalizedNameTwoStep base rel one cut iter) := by
  let := hΩ.inaccessible.1
  have hsub : succ k ⊆ Ω := by
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hk
    · exact IsOrdinal.toIsTransitive.mem_trans hi hk
  have hx := woodinIterationExit hΩ hAC
  have hh := woodinNormalizedStage_successor_carrier_order hΩ hAC hk
  have hpref := woodinIterationPrefix_successor
    (woodinIterationHistory_of_stages (fun i hi ↦ (hx.2.1 i (hsub i hi)).1))
  dsimp only at hh ⊢
  rw [hpref.1, hpref.2, woodinNormalizationHistory_value (mem_succ_self k)] at hh
  simpa only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeP_code,
    forcingCodeR_code, forcingCodet_code, forcingNormalizationCarriers_value (mem_succ_self k),
    forcingNormalizationOrders_value (mem_succ_self k), woodinNormalizationHistory_value (mem_succ_self k)] using hh

end ZFVP
