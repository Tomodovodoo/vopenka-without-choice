import ZFVP.ModelTheory.PrefixCollapseRankForcingAgreement
import ZFVP.ModelTheory.RankWoodinRestoration

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eventually_prefix_rank_localRestoration_iff_countable [Countable V]
    {δ κ γ P R one : V} (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ)
    (hκδ : κ ∈ δ) (hγδ : γ ∈ δ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![checkName one κ])) :
    ∃ β ∈ δ, γ ∈ β ∧ ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
      ∀ ξ : A.Model, A.check β ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
        letI := hξ.1
        letI := rankDomain_nonempty hξ.2.1
        letI := hξ.rankCriterion.models_zf
        ∀ k d : SetDomain (hierarchy ξ), k.val = A.check κ → d.val = A.check γ →
          (IsWoodinLocalRestoration k d ↔ IsWoodinLocalRestoration (A.check κ) (A.check γ)) := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hγδ
  obtain ⟨β, hβ, hγβ, hall⟩ := eventually_prefixCollapse_rankDCBelow_forcing_eq_countable
    hδ hP hκδ hγδ hR ht hκ
  refine ⟨β, hβ, hγβ, ?_⟩
  intro G hG
  dsimp only
  intro ξ hβξ hξ
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  intro k d hk hd
  have hdOrd : IsOrdinal d := (TransitiveZF.ordinal_iff (hierarchy ξ) d).mpr (hd ▸ inferInstance)
  have hs : ∀ b ∈ ξ, succ b ∈ ξ := fun _ hb ↦ regularCardinal_succ_closed hξ.regular hb
  have hPval := rank_woodinCollapse_val hs k d hdOrd
  rw [hk, hd] at hPval
  have hPξ : woodinCollapse (A.check κ) (A.check γ) ∈ hierarchy ξ :=
    hPval ▸ (woodinCollapse k d).property
  have hnval : (checkName (∅ : SetDomain (hierarchy ξ)) d).val =
      checkName (∅ : A.Model) (A.check γ) := by
    rw [TransitiveZF.checkName_val, TransitiveZF.empty_val, hd]
  have hn : checkName (∅ : A.Model) (A.check γ) ∈ hierarchy ξ :=
    hnval ▸ (checkName (∅ : SetDomain (hierarchy ξ)) d).property
  have he := hall G hG ξ hβξ hξ hPξ hn
  have hl := rank_woodinLocalRestoration_iff hs k d hdOrd
  rw [hk, hd] at hl
  change IsWoodinLocalRestoration k d ↔ ∀ p ∈ woodinCollapse (A.check κ) (A.check γ),
    p ∈ classForcingFormula (woodinCollapse (A.check κ) (A.check γ))
      (woodinCollapseOrder (A.check κ) (A.check γ))
      (IsLowRankForcingName (woodinCollapse (A.check κ) (A.check γ)) ξ) (by definability)
      dependentChoiceBelowFormula (standardTuple ![checkName ∅ (A.check γ)]) at hl
  rw [he] at hl
  exact hl.trans (and_iff_right (show IsOrdinal (A.check γ) from inferInstance)).symm

end ZFVP
