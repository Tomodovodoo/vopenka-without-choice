import ZFVP.SetTheory.RealOuterMeasure

/-! Total genuine interval covers with arbitrarily small cost, including empty sets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def realNullPadding (m : V) : V :=
  definableGraph (ω : V) (fun n ↦ ⟨rationalZero V, dyadicUnit (succ (ordinalAdd m n))⟩ₖ) (by definability)

instance realNullPadding_definable : ℒₛₑₜ-function₁[V] realNullPadding := by
  have h : ℒₛₑₜ-relation (fun d m : V ↦ ∀ p, p ∈ d ↔
      ∃ n ∈ (ω : V), p = ⟨n, ⟨rationalZero V, dyadicUnit (succ (ordinalAdd m n))⟩ₖ⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [realNullPadding, mem_definableGraph_iff]

theorem realNullPadding_value (m : V) {n : V} (hn : n ∈ (ω : V)) :
    (realNullPadding m) ‘ n = ⟨rationalZero V, dyadicUnit (succ (ordinalAdd m n))⟩ₖ :=
  value_definableGraph _ _ _ hn

theorem realNullPadding_mem {m : V} (hm : m ∈ (ω : V)) :
    realNullPadding m ∈ (realBasicCodes V) ^ (ω : V) := by
  apply definableGraph_mem_function_of_mapsTo
  intro n hn
  exact (pair_mem_realBasicCodes_iff _ _).mpr ⟨rationalZero_mem,
    dyadicUnit_mem (ω_succ_closed (ordinalAdd_natural hm hn)),
    dyadicUnit_positive (ω_succ_closed (ordinalAdd_natural hm hn))⟩

theorem realNullPadding_length {m n : V} (hm : m ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    realIntervalLength ((realNullPadding m) ‘ n) = dyadicUnit (succ (ordinalAdd m n)) := by
  rw [realNullPadding_value _ hn]
  simp only [realIntervalLength, kpair.π₁_kpair, kpair.π₂_kpair]
  have h0 : rationalNeg (rationalZero V) = rationalZero V :=
    congrArg Subtype.val (show -(0 : InternalRational V) = 0 from neg_zero)
  rw [h0]
  exact rationalAdd_zero (dyadicUnit_mem (ω_succ_closed (ordinalAdd_natural hm hn)))

theorem realNullPadding_cost_identity {m : V} (hm : m ∈ (ω : V)) :
    ∀ n ∈ (ω : V), rationalAdd (realCoverCost (realNullPadding m) n)
      (dyadicUnit (ordinalAdd m n)) = dyadicUnit m := by
  apply naturalNumber_induction
    (fun n ↦ rationalAdd (realCoverCost (realNullPadding m) n)
      (dyadicUnit (ordinalAdd m n)) = dyadicUnit m) (by definability)
  · rw [realCoverCost_zero, show (0 : V) = ∅ from rfl, ordinalAdd_zero,
      rationalAdd_comm rationalZero_mem (dyadicUnit_mem hm), rationalAdd_zero (dyadicUnit_mem hm)]
  · intro n hn ih
    have : IsOrdinal m := IsOrdinal.of_mem hm
    have : IsOrdinal n := IsOrdinal.of_mem hn
    rw [realCoverCost_succ _ hn, realNullPadding_length hm hn, ordinalAdd_succ,
      rationalAdd_assoc (realCoverCost_mem (realNullPadding_mem hm) n hn)
        (dyadicUnit_mem (ω_succ_closed (ordinalAdd_natural hm hn)))
        (dyadicUnit_mem (ω_succ_closed (ordinalAdd_natural hm hn))),
      dyadicUnit_halves (ordinalAdd_natural hm hn)]
    exact ih

theorem realNullPadding_cost_bound {m n : V} (hm : m ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    ¬ InternalRationalLT (dyadicUnit m) (realCoverCost (realNullPadding m) n) := by
  let s : InternalRational V := ⟨realCoverCost (realNullPadding m) n,
    realCoverCost_mem (realNullPadding_mem hm) n hn⟩
  let t : InternalRational V := ⟨dyadicUnit (ordinalAdd m n), dyadicUnit_mem (ordinalAdd_natural hm hn)⟩
  have he : s + t = ⟨dyadicUnit m, dyadicUnit_mem hm⟩ := Subtype.ext (realNullPadding_cost_identity hm n hn)
  have hle : s ≤ s + t := le_add_of_nonneg_right (le_of_lt (show 0 < t from
    dyadicUnit_positive (ordinalAdd_natural hm hn)))
  rw [he] at hle
  exact hle

theorem realNull_empty : IsRealNull (∅ : V) := by
  intro m hm
  exact ⟨realNullPadding m, ⟨realNullPadding_mem hm, fun x hx ↦ (not_mem_empty hx).elim⟩,
    fun n hn ↦ realNullPadding_cost_bound hm hn⟩

theorem realOuterMeasure_empty : realOuterMeasure (∅ : V) = rationalCut (rationalZero V) :=
  realNull_outerMeasure_zero realNull_empty

end ZFVP
