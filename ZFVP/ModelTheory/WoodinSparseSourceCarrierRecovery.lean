import ZFVP.ModelTheory.WoodinSparseCarrierRecovery

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
local notation "C" => woodinSparseSourceStageCode θ
local notation "P" => (forcingCodeP C) ‘ (woodinSourceIndex θ)

theorem woodinSparseStageCode_seed_cut
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    sparseCarrierCut ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) (succ (∅ : V)) = {∅} := by
  apply mem_ext
  intro p
  rw [mem_sparseCarrierCut_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hp, hd⟩
    have hs := woodinSparseStageCode_sparse hΩ hAC hθ hp
    let := hs.1
    have hn := woodinSparseStageCode_no_zero hΩ hAC hθ hp
    have hz : domain p ⊆ (∅ : V) := by
      intro x hx
      rcases mem_succ_iff.mp (hd x hx) with he | he
      · subst x
        exact False.elim (hn hx)
      · exact he
    simpa only [restrict_empty_domain] using (IsFunction.restrict_eq_self p ∅ hz).symm
  · intro he
    subst p
    have ht := (woodinSparseStageCode_valid hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)
    rw [woodinSparseStageCode_top hΩ hAC hθ] at ht
    exact ⟨ht.1, by simp⟩

theorem woodinSparseSourceStageCode_carrier_recovery
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ (woodinSourceIndex θ)) :
    (forcingCodeP C) ‘ i = sparseCarrierCut P (succ i) := by
  have hi' : i ∈ woodinSourceIndex (succ θ) := by simpa only [woodinSourceIndex_successor] using hi
  rw [(woodinSparseSourceStageCode_row (mem_succ_self θ)).1]
  rcases woodinSourceIndex_cases hi' with he | ⟨j, hj, rfl⟩
  · subst i
    rw [(woodinSparseSourceStageCode_seed (θ := θ)).1, woodinSparseStageCode_seed_cut hΩ hAC hθ]
  · rw [(woodinSparseSourceStageCode_row hj).1, (woodinSparseStage_old_row hj).1]
    exact woodinSparseStageCode_carrier_recovery hΩ hAC hθ hj

theorem woodinSparseSourceStageCode_order_restriction
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i p q : V} (hi : i ∈ succ (woodinSourceIndex θ))
    (hp : p ∈ (forcingCodeP C) ‘ i) (hq : q ∈ (forcingCodeP C) ‘ i) :
    ⟨p, q⟩ₖ ∈ (forcingCodeR C) ‘ (woodinSourceIndex θ) ↔ ⟨p, q⟩ₖ ∈ (forcingCodeR C) ‘ i := by
  have hi' : i ∈ woodinSourceIndex (succ θ) := by simpa only [woodinSourceIndex_successor] using hi
  rcases woodinSourceIndex_cases hi' with he | ⟨j, hj, rfl⟩
  · subst i
    rw [(woodinSparseSourceStageCode_seed (θ := θ)).1] at hp hq
    have hp0 := mem_singleton_iff.mp hp
    have hq0 := mem_singleton_iff.mp hq
    subst p
    subst q
    have ht := (woodinSparseStageCode_valid hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)
    rw [woodinSparseStageCode_top hΩ hAC hθ] at ht
    rw [(woodinSparseSourceStageCode_row (mem_succ_self θ)).2,
      (woodinSparseSourceStageCode_seed (θ := θ)).2.1]
    exact iff_of_true (ht.2 ∅ ht.1) (kpair_mem_iff.mpr ⟨by simp, by simp⟩)
  · rw [(woodinSparseSourceStageCode_row hj).1, (woodinSparseStage_old_row hj).1] at hp hq
    rw [(woodinSparseSourceStageCode_row (mem_succ_self θ)).2,
      (woodinSparseSourceStageCode_row hj).2, (woodinSparseStage_old_row hj).2]
    exact woodinSparseStageCode_order_restriction hΩ hAC hθ hj hp hq

end ZFVP
