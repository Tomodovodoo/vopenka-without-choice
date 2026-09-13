import ZFVP.ModelTheory.WoodinSuccessorInvariant
import ZFVP.ModelTheory.WoodinPrefixRankTransfer
import ZFVP.SetTheory.TwoStepRankBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsWoodinStageSmall (x : V) : Prop :=
  ∀ θ : V, IsChoicelessInaccessible θ → woodinStageCardinal x ∈ θ → woodinStagePoset x ∈ hierarchy θ

instance isWoodinStageSmall_definable : ℒₛₑₜ-predicate[V] IsWoodinStageSmall := by
  unfold IsWoodinStageSmall
  definability

theorem woodinSuccessorAt_mem_hierarchy {P R one κ δ θ : V}
    (_hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (_hκ : κ ⊆ δ)
    (hθ : IsChoicelessInaccessible θ) (hδθ : δ ∈ θ) :
    woodinSuccessorAt P R one κ δ ∈ hierarchy θ := by
  let := hδ.1
  let := hθ.1
  have hs := hθ.rankCriterion.2.2.1
  have hQ := saturatedWoodinPrefixPosetName_mem_hierarchy (R := R) (one := one) (κ := κ) hθ
    (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hδθ) P hP) hδθ
  have ht : (∅ : V) ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr (hθ.regular.2.1 ∅ (by simp))
  have hPθ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hδθ) P hP
  have hC := twoStepConditions_mem_hierarchy_limit (R := R) hs hPθ hQ ht
  have hS := twoStepOrder_mem_hierarchy_limit (R := R) (S := saturatedWoodinPrefixOrderName P R one κ δ) hs hPθ hQ ht
  exact kpair_mem_hierarchy_limit hs hC (kpair_mem_hierarchy_limit hs hS
    (kpair_mem_hierarchy_limit hs (kpair_mem_hierarchy_limit hs
      ((hierarchy_transitive θ).mem_trans htop.1 hPθ) ht) (ordinal_mem_hierarchy_iff.mpr hδθ)))

theorem woodinSuccessorAt_small {P R one κ δ : V}
    (_hR : IsForcingPreorder P R) (_htop : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (_hκ : κ ⊆ δ) :
    IsWoodinStageSmall (woodinSuccessorAt P R one κ δ) := by
  intro θ hθ hδθ
  simp only [woodinSuccessorAt, woodinStageCardinal_code] at hδθ
  let := hδ.1
  let := hθ.1
  have hQ := saturatedWoodinPrefixPosetName_mem_hierarchy (R := R) (one := one) (κ := κ) hθ
    (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hδθ) P hP) hδθ
  have ht : (∅ : V) ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr (hθ.regular.2.1 ∅ (by simp))
  simp only [woodinSuccessorAt, woodinStagePoset_code]
  exact twoStepConditions_mem_hierarchy_limit hθ.rankCriterion.2.2.1
    (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hδθ) P hP) hQ ht

theorem IsWoodinStage.order_mem_hierarchy {x θ : V} (hx : IsWoodinStage x) [IsOrdinal θ]
    (hs : ∀ α ∈ θ, succ α ∈ θ) (hP : woodinStagePoset x ∈ hierarchy θ) :
    woodinStageOrder x ∈ hierarchy θ :=
  subset_mem_hierarchy_limit hs (prod_mem_hierarchy_limit hs hP hP) hx.1.1

theorem woodinSuccessorStep_preserves_below_supercompact {x δ : V}
    (hx : IsWoodinStage x) (hsmall : IsWoodinStageSmall x)
    (hδ : IsWoodinSupercompact δ) (hκδ : woodinStageCardinal x ∈ δ) :
    IsWoodinStage (woodinSuccessorStep x) ∧ IsWoodinStageSmall (woodinSuccessorStep x) ∧
      IsChoicelessInaccessible (woodinStageCardinal (woodinSuccessorStep x)) ∧
      woodinStageCardinal x ∈ woodinStageCardinal (woodinSuccessorStep x) ∧
      woodinStageCardinal (woodinSuccessorStep x) ∈ δ := by
  let := hδ.inaccessible.1
  have hP := hsmall δ hδ.inaccessible hκδ
  have hR := hx.order_mem_hierarchy hδ.inaccessible.rankCriterion.2.2.1 hP
  obtain ⟨c, _, hc⟩ := hδ.strictPrefixCutoff hx.1 hx.2.1 hP hR hκδ hx.2.2.2.1 hx.2.2.2.2
  have hl := (woodinPrefixCutoff_spec hc).2.1
  have hPl := hsmall _ hl.2.1 hl.1
  let := hl.2.1.1
  refine ⟨woodinSuccessorStep_stage hx hc hPl, ?_, woodinSuccessorStep_cardinal_inaccessible hc,
    woodinSuccessorStep_cardinal_gt hc, woodinSuccessorStep_cardinal_lt_supercompact hx hδ hP hR hκδ⟩
  exact woodinSuccessorAt_small hx.1 hx.2.1 hl.2.1 hPl (IsOrdinal.toIsTransitive.transitive _ hl.1)

end ZFVP
