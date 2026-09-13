import ZFVP.ModelTheory.RankDCForcingAgreement
import ZFVP.ModelTheory.RankWoodinRestoration
import ZFVP.ModelTheory.SuccessorRankWoodinCollapse
import ZFVP.SetTheory.WoodinSupercompactStarCorrect

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.eventually_rank_localRestoration_iff {δ κ γ : V}
    (hδ : IsWoodinSupercompact δ) (hκ : IsRegularCardinal κ) (hκδ : κ ∈ δ) (hγδ : γ ∈ δ) :
    ∃ η ∈ δ, κ ∈ η ∧ γ ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ k d : SetDomain (hierarchy ξ), k.val = κ → d.val = γ →
        (IsWoodinLocalRestoration k d ↔ IsWoodinLocalRestoration κ γ) := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hκδ
  let := IsOrdinal.of_mem hγδ
  have hP := woodinCollapse_mem_hierarchy hδ.cn_one (show IsOrdinal γ from inferInstance)
    (ordinal_mem_hierarchy_iff.mpr hκδ) (ordinal_mem_hierarchy_iff.mpr hγδ)
  have htop := woodinCollapse_top (hκ.2.1 ∅ (by simp)) γ
  obtain ⟨β, hβδ, hγβ, hall⟩ := eventually_rankDCBelow_forcing_eq hδ hP hγδ
    (woodinCollapse_poset κ γ).1 htop
  let := IsOrdinal.of_mem hβδ
  let := ordinal_union_ordinal β κ
  let η := succ (β ∪ κ)
  have hηδ : η ∈ δ := regularCardinal_succ_closed hδ.inaccessible.regular (ordinal_union_mem hβδ hκδ)
  have hβη : β ∈ η := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (subset_union_left β κ))
  have hκη : κ ∈ η := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (subset_union_right β κ))
  refine ⟨η, hηδ, hκη, IsOrdinal.toIsTransitive.mem_trans hγβ hβη, ?_⟩
  intro ξ hηξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  intro k d hk hd
  have hdOrd : IsOrdinal d := (TransitiveZF.ordinal_iff (hierarchy ξ) d).mpr (hd ▸ inferInstance)
  have hs : ∀ b ∈ ξ, succ b ∈ ξ := fun _ hb ↦ regularCardinal_succ_closed hξ.regular hb
  have hPval := rank_woodinCollapse_val hs k d hdOrd
  rw [hk, hd] at hPval
  have hPξ : woodinCollapse κ γ ∈ hierarchy ξ := hPval ▸ (woodinCollapse k d).property
  have hnval : (checkName (∅ : SetDomain (hierarchy ξ)) d).val = checkName (∅ : V) γ := by
    rw [TransitiveZF.checkName_val, TransitiveZF.empty_val, hd]
  have hn : checkName (∅ : V) γ ∈ hierarchy ξ := hnval ▸ (checkName (∅ : SetDomain (hierarchy ξ)) d).property
  have he := hall ξ (IsOrdinal.toIsTransitive.mem_trans hβη hηξ) hξ hPξ hn
  have hl := rank_woodinLocalRestoration_iff hs k d hdOrd
  rw [hk, hd] at hl
  change IsWoodinLocalRestoration k d ↔ ∀ p ∈ woodinCollapse κ γ,
    p ∈ classForcingFormula (woodinCollapse κ γ) (woodinCollapseOrder κ γ)
      (IsLowRankForcingName (woodinCollapse κ γ) ξ) (by definability)
      dependentChoiceBelowFormula (standardTuple ![checkName ∅ γ]) at hl
  rw [he] at hl
  exact hl.trans (and_iff_right (show IsOrdinal γ from inferInstance)).symm

end ZFVP
