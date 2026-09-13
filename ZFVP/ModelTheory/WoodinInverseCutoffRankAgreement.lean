import ZFVP.ModelTheory.HartogsLeastPrefixCutoffRankAgreement
import ZFVP.ModelTheory.RankInverseCodeParameters
import ZFVP.ModelTheory.WoodinInverseSourceCutoff
import ZFVP.ModelTheory.WoodinInverseStageBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinIteration.eventually_rank_inverseSourceCutoff_eq {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ) (h0 : ∅ ∈ θ)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hγ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (regularCardinalFormula.or limitOfRegularCardinalsFormula)
        (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)]))
    (hDC : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        dependentChoiceAtFormula (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)])) :
    ∃ η ∈ δ, woodinLimitCardinal K ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ t u C : SetDomain (hierarchy ξ), t.val = θ → u.val = s → C.val = K →
        (forcingInverseSourceCutoff t u (woodinLimitCardinal C)).val =
          forcingInverseSourceCutoff θ s (woodinLimitCardinal K) := by
  let := hδ.inaccessible.1
  let := h.limitCardinal_ordinal
  have hs := h.inverse_small hδ.inaccessible hθ h.bounded
  have hb := h.limitCardinal_below hδ.inaccessible.regular hθ
  have c := h.code.system.inverseColumn h0 h.code.subset_universe
  have ht : IsForcingTop (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) := c.tops.top
  let τ : ForcingName (forcingInverseCodePoset θ s) :=
    ⟨checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K), checkName_isName ht.1 _⟩
  obtain ⟨η, hηδ, hκη, hall⟩ := hδ.eventually_rank_hartogsPrefixCutoff_eq c.order.preorder ht
    hs.1 hs.2 hb (fun γ hg hκg ↦ (h.inverse_small_above_limit hlim hg hκg).1)
    (fun p hp ↦ hartogsNumberName_forces_regular c.order.preorder ht hp τ (hγ p hp) (hDC p hp))
    (fun p hp ↦ hartogsNumberName_forces_dependentChoiceBelow c.order.preorder ht hp τ
      (forces_checked_ordinal c.order.preorder ht inferInstance hp) (hDC p hp))
  refine ⟨η, hηδ, hκη, ?_⟩
  intro ξ hηξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  intro t u C htθ hus hCK
  have hclosed : ∀ β ∈ ξ, succ β ∈ ξ := fun _ hb ↦ regularCardinal_succ_closed hξ.regular hb
  have hp : (forcingInverseCodePoset t u).val = forcingInverseCodePoset θ s := by
    rw [rank_forcingInverseCodePoset_val hclosed, htθ, hus]
  have hr : (forcingInverseCodeOrder t u).val = forcingInverseCodeOrder θ s := by
    rw [rank_forcingInverseCodeOrder_val hclosed, htθ, hus]
  have ho : (forcingInverseCodeTop t u).val = forcingInverseCodeTop θ s := by
    rw [TransitiveZF.forcingInverseCodeTop_val, htθ, hus]
  have hk : (woodinLimitCardinal C).val = woodinLimitCardinal K := by
    rw [TransitiveZF.woodinLimitCardinal_val, hCK]
  exact hall ξ hηξ hξ (forcingInverseCodePoset t u) (forcingInverseCodeOrder t u)
    (forcingInverseCodeTop t u) (woodinLimitCardinal C) hp hr ho hk

theorem TransitiveZF.woodinInverseCardinalNext_val (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (θ s K : SetDomain U)
    (hcut : (forcingInverseSourceCutoff θ s (woodinLimitCardinal K)).val =
      forcingInverseSourceCutoff θ.val s.val (woodinLimitCardinal K.val)) :
    (woodinInverseCardinalNext θ s K).val = woodinInverseCardinalNext θ.val s.val K.val := by
  simp only [woodinInverseCardinalNext, forcingFamilyNext_val U, hcut]

end ZFVP
