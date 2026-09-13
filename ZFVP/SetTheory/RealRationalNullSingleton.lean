import ZFVP.SetTheory.RealHalfLineMeasurable

/-! Genuine geometric covers of rational points on the real line. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def realRationalPointCover (q m : V) : V :=
  definableGraph (ω : V) (fun n ↦
    ⟨rationalAdd q (rationalNeg (dyadicUnit (succ (succ (ordinalAdd m n))))),
      rationalAdd q (dyadicUnit (succ (succ (ordinalAdd m n))))⟩ₖ) (by definability)

theorem realRationalPointCover_value (q m : V) {n : V} (hn : n ∈ (ω : V)) :
    (realRationalPointCover q m) ‘ n =
      ⟨rationalAdd q (rationalNeg (dyadicUnit (succ (succ (ordinalAdd m n))))),
        rationalAdd q (dyadicUnit (succ (succ (ordinalAdd m n))))⟩ₖ :=
  value_definableGraph _ _ _ hn

theorem realRationalPointCover_mem (q : InternalRational V) {m : V} (hm : m ∈ (ω : V)) :
    realRationalPointCover q.val m ∈ (realBasicCodes V) ^ (ω : V) := by
  apply definableGraph_mem_function_of_mapsTo
  intro n hn
  let e : InternalRational V := ⟨_, dyadicUnit_mem (ω_succ_closed (ω_succ_closed (ordinalAdd_natural hm hn)))⟩
  have he : 0 < e := dyadicUnit_positive (ω_succ_closed (ω_succ_closed (ordinalAdd_natural hm hn)))
  exact (pair_mem_realBasicCodes_iff _ _).mpr ⟨(q - e).property, (q + e).property,
    (show q - e < q + e from lt_trans (sub_lt_self q he) (lt_add_of_pos_right q he))⟩

theorem realRationalPointCover_cost (q : InternalRational V) {m : V} (hm : m ∈ (ω : V)) :
    ∀ n ∈ (ω : V), realCoverCost (realRationalPointCover q.val m) n = realCoverCost (realNullPadding m) n := by
  apply rationalPartialSum_congr
  intro n hn
  rw [realCoverLengths, value_definableGraph _ _ _ hn,
    realCoverLengths, value_definableGraph _ _ _ hn,
    realRationalPointCover_value _ _ hn, realNullPadding_length hm hn]
  let e : InternalRational V := ⟨_, dyadicUnit_mem (ω_succ_closed (ω_succ_closed (ordinalAdd_natural hm hn)))⟩
  have heq : realIntervalLength
      (⟨rationalAdd q.val (rationalNeg e.val), rationalAdd q.val e.val⟩ₖ : V) = rationalAdd e.val e.val := by
    simp only [realIntervalLength, kpair.π₁_kpair, kpair.π₂_kpair]
    exact congrArg Subtype.val (show (q + e) - (q - e) = e + e from by ring)
  exact heq.trans (dyadicUnit_halves (ω_succ_closed (ordinalAdd_natural hm hn)))

theorem realNull_rationalSingleton (q : InternalRational V) : IsRealNull ({rationalCut q.val} : V) := by
  intro m hm
  refine ⟨realRationalPointCover q.val m, ⟨realRationalPointCover_mem q hm, ?_⟩, ?_⟩
  · intro x hx
    have heqx := mem_singleton_iff.mp hx
    subst x
    refine ⟨0, by simp, ?_⟩
    rw [realRationalPointCover_value _ _ (show (0 : V) ∈ (ω : V) by simp)]
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    have h0 : (0 : V) ∈ (ω : V) := by simp
    let e : InternalRational V := ⟨_, dyadicUnit_mem (ω_succ_closed (ω_succ_closed (ordinalAdd_natural hm h0)))⟩
    have he : 0 < e := dyadicUnit_positive (ω_succ_closed (ω_succ_closed (ordinalAdd_natural hm h0)))
    exact (mem_realInterval_iff _ _ _).mpr ⟨rationalCut_isCut q.property,
      (rationalCut_lt_iff (q - e).property q.property).mpr (sub_lt_self q he),
      (rationalCut_lt_iff q.property (q + e).property).mpr (lt_add_of_pos_right q he)⟩
  · intro n hn
    rw [realRationalPointCover_cost q hm n hn]
    exact realNullPadding_cost_bound hm hn

end ZFVP
