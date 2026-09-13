import ZFVP.ModelTheory.WoodinSuccessorAtRankAgreement
import ZFVP.ModelTheory.WoodinLeastPrefixCutoffRankAgreement
import ZFVP.ModelTheory.TransitiveZFWoodinStage
import ZFVP.ModelTheory.WoodinSuccessorBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.eventually_rank_woodinSuccessorStep_eq {δ X : V}
    (hδ : IsWoodinSupercompact δ) (hX : IsWoodinStage X) (hsmall : IsWoodinStageSmall X)
    (hκδ : woodinStageCardinal X ∈ δ) :
    ∃ η ∈ δ, woodinStageCardinal X ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ x : SetDomain (hierarchy ξ), x.val = X → (woodinSuccessorStep x).val = woodinSuccessorStep X := by
  let := hδ.1.1
  have hP := hsmall δ hδ.inaccessible hκδ
  have hR := hX.order_mem_hierarchy hδ.inaccessible.rankCriterion.2.2.1 hP
  obtain ⟨η, hηδ, hκη, hall⟩ := hδ.eventually_rank_woodinPrefixCutoff_eq hX.1 hX.2.1
    hP hR hκδ hX.2.2.2.1 hX.2.2.2.2
  obtain ⟨c, _, hc⟩ := hδ.strictPrefixCutoff hX.1 hX.2.1 hP hR hκδ hX.2.2.2.1 hX.2.2.2.2
  have hcord := (woodinPrefixCutoff_spec hc).1
  refine ⟨η, hηδ, hκη, ?_⟩
  intro ξ hηξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  intro x hx
  let p := woodinStagePoset x
  let r := woodinStageOrder x
  let o := woodinStageTop x
  let k := woodinStageCardinal x
  have hp : p.val = woodinStagePoset X := by rw [TransitiveZF.woodinStagePoset_val, hx]
  have hr : r.val = woodinStageOrder X := by rw [TransitiveZF.woodinStageOrder_val, hx]
  have ho : o.val = woodinStageTop X := by rw [TransitiveZF.woodinStageTop_val, hx]
  have hk : k.val = woodinStageCardinal X := by rw [TransitiveZF.woodinStageCardinal_val, hx]
  have hcut := hall ξ hηξ hξ p r o k hp hr ho hk
  have hord : IsForcingPreorder p r := (TransitiveZF.forcingPreorder_iff (hierarchy ξ) p r).mpr
    (by simpa only [hp, hr] using hX.1)
  have htop : IsForcingTop p r o := (TransitiveZF.forcingTop_iff (hierarchy ξ) p r o).mpr
    (by simpa only [hp, hr, ho] using hX.2.1)
  have hcutord : IsOrdinal (woodinPrefixCutoff p r o k) :=
    (TransitiveZF.ordinal_iff (hierarchy ξ) _).mpr (hcut ▸ hcord)
  have he := rank_woodinSuccessorAt_val hξ p r o k (woodinPrefixCutoff p r o k) hord htop hcutord
  rw [hp, hr, ho, hk, hcut] at he
  exact he

end ZFVP
