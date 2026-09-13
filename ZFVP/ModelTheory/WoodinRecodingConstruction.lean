import ZFVP.ModelTheory.WoodinRecodingHistory
import ZFVP.ModelTheory.WoodinRecodedRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsWoodinRecodedRow (θ r : V) : Prop :=
  IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ)
    ((forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ) (kpair.π₁ r)
    (kpair.π₁ (kpair.π₂ r)) (kpair.π₂ (kpair.π₂ r)) ∧
  IsForcingPreorder (kpair.π₁ r) (kpair.π₁ (kpair.π₂ r)) ∧
  ∀ ξ : V, IsChoicelessInaccessible ξ → (kpair.π₂ (woodinIterationRec θ)) ‘ θ ∈ ξ →
    kpair.π₁ r ∈ hierarchy ξ

instance isWoodinRecodedRow_definable : ℒₛₑₜ-relation[V] IsWoodinRecodedRow := by
  unfold IsWoodinRecodedRow
  definability

theorem woodinRecodingRec_step {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (ih : ∀ i ∈ θ, IsWoodinRecodedRow i (woodinRecodingRec i)) :
    IsWoodinRecodedRow θ (woodinRecodingRec θ) := by
  classical
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  let Q := woodinRecodingCarriers (woodinRecodingHistory θ)
  let T := woodinRecodingOrders (woodinRecodingHistory θ)
  let m := woodinRecodingMaps (woodinRecodingHistory θ)
  let c := forcingRecodedCode θ (woodinNormalizedPrefixCode θ) Q T m
  have hQt : IsIterationTable θ Q := (woodinRecodingHistory_tables θ).1
  have hTt : IsIterationTable θ T := (woodinRecodingHistory_tables θ).2.1
  have hm := woodinRecodingHistory_family_of_rows hΩ hAC hsub (fun i hi ↦ (ih i hi).1)
  have hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i) := by
    intro i hi
    change IsForcingPreorder ((woodinRecodingCarriers (woodinRecodingHistory θ)) ‘ i)
      ((woodinRecodingOrders (woodinRecodingHistory θ)) ‘ i)
    rw [(woodinRecodingHistory_values hi).1, (woodinRecodingHistory_values hi).2.1]
    exact (ih i hi).2.1
  have hsmall : ∀ i ∈ θ, ∀ ξ : V, IsChoicelessInaccessible ξ →
      (kpair.π₂ (woodinIterationRec i)) ‘ i ∈ ξ → Q ‘ i ∈ hierarchy ξ := by
    intro i hi ξ hξ hcard
    change (woodinRecodingCarriers (woodinRecodingHistory θ)) ‘ i ∈ hierarchy ξ
    rw [(woodinRecodingHistory_values hi).1]
    exact (ih i hi).2.2 ξ hξ hcard
  have hR := (woodinNormalizedStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)
  rw [woodinRecodingRec_rule]
  change IsWoodinRecodedRow θ (woodinRecodingRowRule θ c m)
  by_cases hz : θ = ∅
  · subst θ
    simp only [woodinRecodingRowRule, ite_true, IsWoodinRecodedRow,
      woodinRecodingInitialRow, kpair.π₁_kpair, kpair.π₂_kpair]
    refine ⟨?_, woodinRecodedInitialOrder_preorder hΩ, ?_⟩
    · rw [(woodinNormalizedStage_initial_dictionary hΩ).1, (woodinNormalizedStage_initial_dictionary hΩ).2]
      exact forcingAutomorphism_identity _ _
    · intro ξ hξ hc
      exact woodinRecodedInitial_small hΩ hAC hξ hc
  by_cases hsucc : θ = succ (⋃ˢ θ)
  · generalize hk : ⋃ˢ θ = k at hsucc
    subst θ
    let : IsOrdinal k := IsOrdinal.of_mem (mem_succ_self k)
    have hkΩ := hsub k (mem_succ_self k)
    obtain ⟨hd, _⟩ := woodinNormalizedSuccessorCutoff_bounds hΩ hAC hkΩ
    have he := woodinNormalizedSuccessorCutoff_actualCardinal hΩ hAC hkΩ
    have hQrank : Q ‘ k ∈ hierarchy (woodinNormalizedSuccessorCutoff k) := by
      apply hsmall k (mem_succ_self k) _ hd
      rw [he]
      exact woodinIterationActualCardinal_increasing hΩ hAC hθ (mem_succ_self k)
    have hf := woodinRecodedSuccessorMap_isomorphism hΩ hAC hkΩ hm hT hQt hTt hQrank
    change IsForcingIsomorphism _ _ (woodinRecodedSuccessorCarrier k c)
      (woodinRecodedSuccessorOrder k c) (woodinRecodedSuccessorMap k c m) at hf
    simp only [woodinRecodingRowRule, ite_eq_right hz, sUnion_succ_of_transitive,
      ite_true, IsWoodinRecodedRow, woodinRecodingSuccessorRow, kpair.π₁_kpair, kpair.π₂_kpair]
    refine ⟨hf, hf.target_preorder hR ?_, ?_⟩
    · unfold woodinRecodedSuccessorOrder nameTwoStepOrderOn
      exact sep_subset
    intro ξ hξ hcξ
    apply woodinRecodedSuccessorCarrier_small hΩ hAC hkΩ hm hT hQt hTt hQrank hξ
    exact he.symm ▸ hcξ
  by_cases hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))
  · have hf := woodinRecodedDirectMap_isomorphism hΩ hAC hsub hz hsucc hinac hm hT hQt hTt
    simp only [woodinRecodingRowRule, ite_eq_right hz, ite_eq_right hsucc, ite_eq_left hinac,
      IsWoodinRecodedRow, woodinRecodingDirectRow, kpair.π₁_kpair, kpair.π₂_kpair]
    refine ⟨hf, hf.target_preorder hR ?_, ?_⟩
    · unfold forcingSparseOrder forcingPullbackOrder
      exact sep_subset
    intro ξ hξ hcξ
    let := hξ.1
    have hcard := woodinDirect_stage_cardinal hΩ hAC hθ hz hsucc hinac
    have hs := woodinIterationPrefix_of_stages (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (hsub i hi)).1)
    have hθeq := hs.index_eq_regular_limit (ordinal_limit_of_not_successor hsucc) hinac.regular
    have hθinac : IsChoicelessInaccessible θ := hθeq.symm ▸ hinac
    have hQθ : ∀ i ∈ θ, (forcingCodeP c) ‘ i ∈ hierarchy θ := by
      intro i hi
      simp only [c, forcingRecodedCode, forcingCodeP_code]
      apply hsmall i hi θ hθinac
      rw [← hcard]
      exact woodinIterationActualCardinal_increasing hΩ hAC hθ hi
    have hb := forcingSparseCodes_subset_hierarchy (U := forcingCodeUniverse c)
      (ordinal_limit_of_not_successor hsucc) hQθ
    apply subset_mem_hierarchy_limit hξ.rankCriterion.2.2.1 ?_ hb
    rw [mem_hierarchy_iff_rank_mem, rank_hierarchy]
    exact hcard ▸ hcξ
  · obtain ⟨_, hd, _, _⟩ := woodinNormalizedInverseCutoff_bounds hΩ hAC hθ hz hsucc hinac
    have he := woodinNormalizedInverseCutoff_actualCardinal hΩ hAC hsub hz hsucc hinac
    have hQrank : ∀ i ∈ θ, Q ‘ i ∈ hierarchy (woodinNormalizedInverseCutoff θ) := by
      intro i hi
      apply hsmall i hi _ hd
      rw [he]
      exact woodinIterationActualCardinal_increasing hΩ hAC hθ hi
    have hf := woodinRecodedInverseMap_isomorphism hΩ hAC hθ hz hsucc hinac hm hT hQt hTt hQrank
    change IsForcingIsomorphism _ _ (woodinRecodedInverseCarrier θ c)
      (woodinRecodedInverseOrder θ c) (woodinRecodedInverseMap θ c m) at hf
    simp only [woodinRecodingRowRule, ite_eq_right hz, ite_eq_right hsucc, ite_eq_right hinac,
      IsWoodinRecodedRow, woodinRecodingInverseRow, kpair.π₁_kpair, kpair.π₂_kpair]
    refine ⟨hf, hf.target_preorder hR ?_, ?_⟩
    · unfold woodinRecodedInverseOrder nameTwoStepOrderOn
      exact sep_subset
    intro ξ hξ hcξ
    apply woodinRecodedInverseCarrier_small hΩ hAC hθ hz hsucc hinac hm hT hQt hTt hQrank hξ
    exact he.symm ▸ hcξ

theorem woodinRecodingRec_correct {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ∀ θ ∈ Ω, IsWoodinRecodedRow θ (woodinRecodingRec θ) := by
  let := hΩ.inaccessible.1
  have hall := transfinite_induction
    (fun ξ : V ↦ ξ ∈ Ω → IsWoodinRecodedRow ξ (woodinRecodingRec ξ)) (by definability) ?_
  · intro θ hθ
    let := IsOrdinal.of_mem hθ
    exact hall (IsOrdinal.toOrdinal θ) hθ
  intro θ ih hθ
  apply woodinRecodingRec_step hΩ hAC hθ
  intro i hi
  let := IsOrdinal.of_mem hi
  exact ih (IsOrdinal.toOrdinal i) hi (IsOrdinal.toIsTransitive.mem_trans hi hθ)

end ZFVP
