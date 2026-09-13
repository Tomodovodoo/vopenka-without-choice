import ZFVP.SetTheory.FinitePartialFunctions
import ZFVP.SetTheory.FiniteNaturalSets

/-! Finite-support Cohen forcing over an internal index set. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def cohenConditions (I : V) : V :=
  finitePartialFunctions (I ×ˢ (ω : V)) 2

noncomputable def cohenOrder (I : V) : V := reverseInclusionOrder (cohenConditions I)

instance cohenConditions_definable : ℒₛₑₜ-function₁[V] cohenConditions := by
  unfold cohenConditions
  definability

instance cohenOrder_definable : ℒₛₑₜ-function₁[V] cohenOrder := by
  unfold cohenOrder
  definability

theorem cohen_poset (I : V) : IsForcingPoset (cohenConditions I) (cohenOrder I) :=
  reverseInclusionOrder_poset _

theorem cohen_top (I : V) : IsForcingTop (cohenConditions I) (cohenOrder I) ∅ :=
  finitePartialFunctions_top _ _

theorem pair_mem_cohenOrder (I p q : V) :
    ⟨p, q⟩ₖ ∈ cohenOrder I ↔ p ∈ cohenConditions I ∧ q ∈ cohenConditions I ∧ q ⊆ p :=
  pair_mem_reverseInclusionOrder _ _ _

/-- The indices of rows on which a condition has specified a bit. -/
noncomputable def cohenSupport (p : V) : V := domain (domain p)

instance cohenSupport_definable : ℒₛₑₜ-function₁[V] cohenSupport := by
  unfold cohenSupport
  definability

theorem mem_cohenSupport (p i : V) :
    i ∈ cohenSupport p ↔ ∃ n b, ⟨⟨i, n⟩ₖ, b⟩ₖ ∈ p := by
  simp only [cohenSupport, mem_domain_iff]

theorem cohenSupport_finite {I p : V} (hp : p ∈ cohenConditions I) :
    IsInternallyFinite (cohenSupport p) :=
  internallyFinite_domain ((mem_finitePartialFunctions _ _ _).mp hp).2.2

theorem cohenSupport_subset {I p : V} (hp : p ∈ cohenConditions I) : cohenSupport p ⊆ I := by
  intro i hi
  obtain ⟨n, b, hb⟩ := (mem_cohenSupport p i).mp hi
  exact (kpair_mem_iff.mp (finitePartialFunction_domain hp _ (mem_domain_of_kpair_mem hb))).1

theorem cohen_fresh_column {I p : V} (hp : p ∈ cohenConditions I) :
    ∃ n ∈ (ω : V), ∀ i, ⟨i, n⟩ₖ ∉ domain p := by
  obtain ⟨n, hn, hnf⟩ := internallyFinite_fresh_natural
    (internallyFinite_range ((mem_finitePartialFunctions _ _ _).mp hp).2.2)
  exact ⟨n, hn, fun i hi ↦ hnf (mem_range_of_kpair_mem hi)⟩

theorem cohen_insert {I p i n b : V} (hp : p ∈ cohenConditions I)
    (hi : i ∈ I) (hn : n ∈ (ω : V)) (hb : b ∈ (2 : V))
    (hfresh : ⟨i, n⟩ₖ ∉ domain p) : insert ⟨⟨i, n⟩ₖ, b⟩ₖ p ∈ cohenConditions I :=
  finitePartialFunction_insert hp (kpair_mem_iff.mpr ⟨hi, hn⟩) hb hfresh

theorem cohen_coordinate_dense {I i n : V} (hi : i ∈ I) (hn : n ∈ (ω : V)) :
    ForcingDense (cohenConditions I) (cohenOrder I)
      {p ∈ cohenConditions I ; ⟨i, n⟩ₖ ∈ domain p} :=
  finitePartialFunctions_domain_dense (kpair_mem_iff.mpr ⟨hi, hn⟩)
    (show (0 : V) ∈ 2 by simp)

/-- Any two distinct rows can be extended to disagree on a fresh column. -/
theorem cohen_separate_rows {I p i j : V} (hp : p ∈ cohenConditions I)
    (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) :
    ∃ q ∈ cohenConditions I, ⟨q, p⟩ₖ ∈ cohenOrder I ∧
      ∃ n ∈ (ω : V), ⟨⟨i, n⟩ₖ, 0⟩ₖ ∈ q ∧ ⟨⟨j, n⟩ₖ, 1⟩ₖ ∈ q := by
  obtain ⟨n, hn, hfresh⟩ := cohen_fresh_column hp
  let r := insert ⟨⟨i, n⟩ₖ, (0 : V)⟩ₖ p
  have hr : r ∈ cohenConditions I := cohen_insert hp hi hn (by simp) (hfresh i)
  have hjfresh : ⟨j, n⟩ₖ ∉ domain r := by
    intro hh
    have hh' : ⟨j, n⟩ₖ = ⟨i, n⟩ₖ ∨ ⟨j, n⟩ₖ ∈ domain p := by
      simpa only [r, domain_insert, mem_insert] using hh
    rcases hh' with he | hh'
    · exact hij (kpair_iff.mp he).1.symm
    · exact hfresh j hh'
  let q := insert ⟨⟨j, n⟩ₖ, (1 : V)⟩ₖ r
  have hq : q ∈ cohenConditions I := cohen_insert hr hj hn (by simp) hjfresh
  refine ⟨q, hq, (pair_mem_cohenOrder I q p).mpr ⟨hq, hp, ?_⟩, n, hn, ?_, ?_⟩
  · intro z hz
    exact mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inr hz)))
  · exact mem_insert.mpr (Or.inr (by simp [r]))
  · simp [q]

theorem cohen_separate_rows_dense {I i j : V} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) :
    ForcingDense (cohenConditions I) (cohenOrder I)
      {p ∈ cohenConditions I ; ∃ n ∈ (ω : V),
        ⟨⟨i, n⟩ₖ, 0⟩ₖ ∈ p ∧ ⟨⟨j, n⟩ₖ, 1⟩ₖ ∈ p} := by
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, fun p hp ↦ ?_⟩
  obtain ⟨q, hq, hqp, hn⟩ := cohen_separate_rows hp hi hj hij
  exact ⟨q, mem_sep_iff.mpr ⟨hq, hn⟩, hqp⟩

end ZFVP
