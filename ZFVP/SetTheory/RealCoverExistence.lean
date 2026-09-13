import ZFVP.SetTheory.RealCoverInfimum

/-! The interval-cover space of every actual real set is nonempty. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def widerUnitCode (q : V) : V :=
  ⟨rationalAdd q (rationalNeg (rationalOne V)),
    rationalAdd (rationalAdd q (rationalOne V)) (rationalOne V)⟩ₖ

instance widerUnitCode_definable : ℒₛₑₜ-function₁[V] widerUnitCode := by
  unfold widerUnitCode
  definability

theorem widerUnitCode_mem {q : V} (hq : q ∈ internalRationals V) :
    widerUnitCode q ∈ realBasicCodes V := by
  let r : InternalRational V := ⟨q, hq⟩
  apply (pair_mem_realBasicCodes_iff _ _).mpr
  refine ⟨(r - 1).property, (r + 1 + 1).property, ?_⟩
  exact (lt_trans (sub_lt_self r zero_lt_one) (lt_trans (lt_add_one r) (lt_add_one (r + 1))) :
    r - 1 < r + 1 + 1)

theorem real_mem_widerUnit {x q : V} (hx : IsDedekindCut x) (hq : q ∈ internalRationals V)
    (hqx : rationalCut q ⊆ x) (hxq : x ⊆ rationalCut (rationalAdd q (rationalOne V))) :
    x ∈ realInterval (kpair.π₁ (widerUnitCode q)) (kpair.π₂ (widerUnitCode q)) := by
  let r : InternalRational V := ⟨q, hq⟩
  simp only [widerUnitCode, kpair.π₁_kpair, kpair.π₂_kpair]
  refine (mem_realInterval_iff _ _ _).mpr ⟨hx, ?_, ?_⟩
  · apply dedekindLT_of_lt_of_subset ?_ hqx
    exact (rationalCut_lt_iff (r - 1).property r.property).mpr (sub_lt_self r zero_lt_one)
  · apply dedekindLT_of_subset_of_lt hxq
    exact (rationalCut_lt_iff (r + 1).property (r + 1 + 1).property).mpr (lt_add_one (r + 1))

theorem exists_realLine_intervalCover : ∃ d : V, IsRealIntervalCover d (dedekindReals V) := by
  obtain ⟨e, he, her⟩ := surjection_of_injection (internalRationals_countable (V := V))
    (show IsNonempty (internalRationals V) from ⟨rationalZero V, rationalZero_mem⟩)
  have : IsFunction e := IsFunction.of_mem he
  let F : V → V := fun n ↦ widerUnitCode (e ‘ n)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  refine ⟨definableGraph (ω : V) F hF,
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun n hn ↦ widerUnitCode_mem (function_value_mem he hn)), ?_⟩
  intro x hx
  have hxcut := (mem_dedekindReals_iff _).mp hx
  obtain ⟨q, hq, hqx, hxq⟩ := real_in_rational_unit_interval hxcut
  have hqr : q ∈ range e := by rwa [her]
  obtain ⟨n, hnq⟩ := mem_range_iff.mp hqr
  have hn : n ∈ (ω : V) := domain_eq_of_mem_function he ▸ mem_domain_of_kpair_mem hnq
  refine ⟨n, hn, ?_⟩
  rw [value_definableGraph _ _ _ hn]
  simpa only [F, value_eq_of_kpair_mem hnq] using real_mem_widerUnit hxcut hq hqx hxq

theorem exists_realIntervalCover {A : V} (hA : A ⊆ dedekindReals V) :
    ∃ d, IsRealIntervalCover d A := by
  obtain ⟨d, hd⟩ := exists_realLine_intervalCover (V := V)
  exact ⟨d, hd.1, fun x hx ↦ hd.2 x (hA x hx)⟩

end ZFVP
