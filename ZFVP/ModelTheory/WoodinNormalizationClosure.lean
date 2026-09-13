import ZFVP.ModelTheory.WoodinNormalizationConstruction
import ZFVP.ModelTheory.WoodinNormalizationSuccessorClosure
import ZFVP.ModelTheory.WoodinNormalizationInverseClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinNormalizationHistory_prefix_carriers {Ω θ j i : V} [IsOrdinal θ]
    (hs : ∀ j ∈ θ, IsWoodinIteration Ω (succ j) (kpair.π₁ (woodinIterationRec j))
      (kpair.π₂ (woodinIterationRec j))) (hj : j ∈ θ) (hi : i ∈ θ) (hij : i ∈ succ j) :
    (forcingNormalizationCarriers θ (woodinIterationPrefix θ) (woodinNormalizationHistory θ)) ‘ i =
      (forcingNormalizationCarriers (succ j) (kpair.π₁ (woodinIterationRec j))
        (woodinNormalizationHistory (succ j))) ‘ i := by
  rw [forcingNormalizationCarriers_value hi, forcingNormalizationCarriers_value hij,
    woodinIterationPrefix_poset_value hs hj hij, woodinNormalizationHistory_value hi,
    woodinNormalizationHistory_value hij]

theorem woodinNormalizationHistory_prefix_liftClosed {Ω θ : V} [IsOrdinal θ]
    (hs : ∀ j ∈ θ, IsWoodinIteration Ω (succ j) (kpair.π₁ (woodinIterationRec j))
      (kpair.π₂ (woodinIterationRec j)))
    (hL : ∀ j ∈ θ, IsForcingNormalizationLiftClosed (succ j) (kpair.π₁ (woodinIterationRec j))
      (woodinNormalizationHistory (succ j))) :
    IsForcingNormalizationLiftClosed θ (woodinIterationPrefix θ) (woodinNormalizationHistory θ) := by
  intro i hi j hj hij a ha b hb hle
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  have hij' : i ∈ succ j := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hij)
  rw [woodinNormalizationHistory_prefix_carriers hs hj hj (mem_succ_self j)] at ha ⊢
  rw [woodinNormalizationHistory_prefix_carriers hs hj hi hij'] at hb
  rw [woodinIterationPrefix_projection_value hs hj hij' (mem_succ_self j),
    woodinIterationPrefix_order_value hs hj hij'] at hle
  rw [woodinIterationPrefix_lift_value hs hj hij' (mem_succ_self j)]
  exact hL j hj i hij' j (mem_succ_self j) hij a ha b hb hle

theorem woodinNormalizationHistory_step_liftClosed {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (hL : IsForcingNormalizationLiftClosed θ (woodinIterationPrefix θ) (woodinNormalizationHistory θ)) :
    IsForcingNormalizationLiftClosed (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (woodinNormalizationHistory (succ θ)) := by
  let := hΩ.inaccessible.1
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ (hx.2.1 i (IsOrdinal.toIsTransitive.mem_trans hi hθ)).1)
  have h := woodinNormalizationHistory_actual_prefix hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ)
  classical
  by_cases hz : θ = ∅
  · subst θ
    rw [woodinIterationRec_initial, kpair.π₁_kpair, woodinNormalizationHistory_next,
      woodinNormalizationRec_rule]
    simpa only [woodinNormalizationRule, ite_eq_left rfl, ite_true, woodinNormalizationHistory_empty,
      woodinNormalizationInitial] using forcingNormalization_singleton_liftClosed
        (woodinNormalizationInitial_family hΩ) (woodinInitialCode_iteration hΩ).code
  by_cases hsucc : θ = succ (⋃ˢ θ)
  · generalize hk : ⋃ˢ θ = k at hsucc
    subst θ
    let : IsOrdinal k := IsOrdinal.of_mem (mem_succ_self k)
    have hn : succ k ≠ (∅ : V) := by
      intro he
      have hm := mem_succ_self k
      rw [he] at hm
      exact not_mem_empty hm
    rw [woodinIterationRec_successor, kpair.π₁_kpair, woodinNormalizationHistory_next,
      woodinNormalizationRec_rule]
    simpa only [woodinNormalizationRule, ite_eq_right hn, sUnion_succ_of_transitive, ite_eq_left rfl, ite_true,
      woodinNormalizationSuccessor] using woodinNormalizationSuccessor_liftClosed hΩ hs h hL
  have h0 : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ hz he.symm)
  by_cases hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))
  · rw [woodinIterationRec_direct hz hsucc hinac, kpair.π₁_kpair, woodinNormalizationHistory_next,
      woodinNormalizationRec_rule]
    simpa only [woodinNormalizationRule, ite_eq_right hz, ite_eq_right hsucc, ite_eq_left hinac,
      forcingNormalizationDirect] using forcingNormalizationDirect_liftClosed hs.code h hL h0
  · rw [woodinIterationRec_inverse hz hsucc hinac, kpair.π₁_kpair, woodinNormalizationHistory_next,
      woodinNormalizationRec_rule]
    simpa only [woodinNormalizationRule, ite_eq_right hz, ite_eq_right hsucc, ite_eq_right hinac,
      woodinNormalizationInverse] using woodinNormalizationInverse_actual_liftClosed hΩ hAC hθ h0
        (ordinal_limit_of_not_successor hsucc) hinac h hL

/-- Closure is derived along the actual source recursion, with no closure premise. -/
theorem woodinNormalizationHistory_liftClosed {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ∀ θ ∈ Ω, IsForcingNormalizationLiftClosed (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (woodinNormalizationHistory (succ θ)) := by
  let := hΩ.inaccessible.1
  have hx := woodinIterationExit hΩ hAC
  have hall := transfinite_induction
    (fun ξ : V ↦ ξ ∈ Ω → IsForcingNormalizationLiftClosed (succ ξ) (kpair.π₁ (woodinIterationRec ξ))
      (woodinNormalizationHistory (succ ξ))) (by definability) ?_
  · intro θ hθ
    let := IsOrdinal.of_mem hθ
    exact hall (IsOrdinal.toOrdinal θ) hθ
  intro θ ih hθ
  apply woodinNormalizationHistory_step_liftClosed hΩ hAC hθ
  apply woodinNormalizationHistory_prefix_liftClosed
    (fun i hi ↦ (hx.2.1 i (IsOrdinal.toIsTransitive.mem_trans hi hθ)).1)
  intro i hi
  let := IsOrdinal.of_mem hi
  exact ih (IsOrdinal.toOrdinal i) hi (IsOrdinal.toIsTransitive.mem_trans hi hθ)

theorem woodinNormalizationHistory_actual_prefix_liftClosed {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingNormalizationLiftClosed θ (woodinIterationPrefix θ) (woodinNormalizationHistory θ) := by
  have hx := woodinIterationExit hΩ hAC
  exact woodinNormalizationHistory_prefix_liftClosed
    (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)
    (fun i hi ↦ woodinNormalizationHistory_liftClosed hΩ hAC i (hθ i hi))

end ZFVP
