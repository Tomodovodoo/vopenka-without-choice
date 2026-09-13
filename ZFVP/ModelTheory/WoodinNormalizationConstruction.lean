import ZFVP.ModelTheory.WoodinNormalizationHistory
import ZFVP.ModelTheory.ForcingNormalizationDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinNormalizationHistory_step {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h : IsForcingNormalizationFamily θ (woodinIterationPrefix θ) (woodinNormalizationHistory θ)) :
    IsForcingNormalizationFamily (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (woodinNormalizationHistory (succ θ)) := by
  let := hΩ.inaccessible.1
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ (hx.2.1 i (IsOrdinal.toIsTransitive.mem_trans hi hθ)).1)
  classical
  by_cases hz : θ = ∅
  · subst θ
    rw [woodinIterationRec_initial, kpair.π₁_kpair, woodinNormalizationHistory_next,
      woodinNormalizationRec_rule]
    simpa only [woodinNormalizationRule, ite_eq_left rfl, ite_true, woodinNormalizationHistory_empty,
      woodinNormalizationInitial] using woodinNormalizationInitial_family hΩ
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
      woodinNormalizationSuccessor] using woodinNormalizationSuccessor_family hΩ hs h
  have h0 : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ hz he.symm)
  by_cases hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))
  · rw [woodinIterationRec_direct hz hsucc hinac, kpair.π₁_kpair, woodinNormalizationHistory_next,
      woodinNormalizationRec_rule]
    simpa only [woodinNormalizationRule, ite_eq_right hz, ite_eq_right hsucc, ite_eq_left hinac, forcingNormalizationDirect] using
      forcingNormalizationDirect_family hs.code h h0
  · rw [woodinIterationRec_inverse hz hsucc hinac, kpair.π₁_kpair, woodinNormalizationHistory_next,
      woodinNormalizationRec_rule]
    simpa only [woodinNormalizationRule, ite_eq_right hz, ite_eq_right hsucc, ite_eq_right hinac, woodinNormalizationInverse] using
      woodinNormalizationInverse_actual_family hΩ hAC hθ h0 (ordinal_limit_of_not_successor hsucc) hinac h

/-- The specified internal recursion normalizes every completed stage below Ω. -/
theorem woodinNormalizationHistory_family {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ∀ θ ∈ Ω, IsForcingNormalizationFamily (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (woodinNormalizationHistory (succ θ)) := by
  let := hΩ.inaccessible.1
  have hx := woodinIterationExit hΩ hAC
  have hall := transfinite_induction
    (fun ξ : V ↦ ξ ∈ Ω → IsForcingNormalizationFamily (succ ξ) (kpair.π₁ (woodinIterationRec ξ))
      (woodinNormalizationHistory (succ ξ))) (by definability) ?_
  · intro θ hθ
    let := IsOrdinal.of_mem hθ
    exact hall (IsOrdinal.toOrdinal θ) hθ
  intro θ ih hθ
  have hs : ∀ i ∈ (θ : V), IsWoodinIteration Ω (succ i) (kpair.π₁ (woodinIterationRec i))
      (kpair.π₂ (woodinIterationRec i)) :=
    fun i hi ↦ (hx.2.1 i (IsOrdinal.toIsTransitive.mem_trans hi hθ)).1
  apply woodinNormalizationHistory_step hΩ hAC hθ
  apply woodinNormalizationHistory_prefix_family hs
  intro i hi
  let := IsOrdinal.of_mem hi
  exact ih (IsOrdinal.toOrdinal i) hi (IsOrdinal.toIsTransitive.mem_trans hi hθ)

theorem woodinNormalizationHistory_actual_prefix {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingNormalizationFamily θ (woodinIterationPrefix θ) (woodinNormalizationHistory θ) := by
  have hx := woodinIterationExit hΩ hAC
  exact woodinNormalizationHistory_prefix_family
    (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)
    (fun i hi ↦ woodinNormalizationHistory_family hΩ hAC i (hθ i hi))

theorem woodinNormalizationRec_retraction {Ω θ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) :
    let P := (forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ
    let R := (forcingCodeR (kpair.π₁ (woodinIterationRec θ))) ‘ θ
    let N := forcingMapFixedPoints P (woodinNormalizationRec θ)
    IsForcingRetraction N (forcingOrderRestriction N R) P R (woodinNormalizationRec θ) := by
  have h := woodinNormalizationHistory_family hΩ hAC θ hθ
  simpa only [woodinNormalizationHistory_value (mem_succ_self θ)] using h.retraction θ (mem_succ_self θ)

theorem woodinNormalizationRec_equivalent {Ω θ p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ) :
    ⟨(woodinNormalizationRec θ) ‘ p, p⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec θ))) ‘ θ ∧
      ⟨p, (woodinNormalizationRec θ) ‘ p⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec θ))) ‘ θ := by
  have h := woodinNormalizationHistory_family hΩ hAC θ hθ
  simpa only [woodinNormalizationHistory_value (mem_succ_self θ)] using h.equivalent θ (mem_succ_self θ) p hp

theorem woodinNormalizationRec_top {Ω θ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) :
    (woodinNormalizationRec θ) ‘ ((forcingCodet (kpair.π₁ (woodinIterationRec θ))) ‘ θ) =
      (forcingCodet (kpair.π₁ (woodinIterationRec θ))) ‘ θ := by
  have h := woodinNormalizationHistory_family hΩ hAC θ hθ
  simpa only [woodinNormalizationHistory_value (mem_succ_self θ)] using h.fixesTop θ (mem_succ_self θ)

end ZFVP
