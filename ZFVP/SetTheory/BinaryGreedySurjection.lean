import ZFVP.SetTheory.BinaryGreedyConstruction

/-! Every internal Dedekind real in the closed unit interval has a definable binary expansion. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def unitRealsFormula : SetTheorySemisentence 1 :=
  f“U. ∀ x, x ∈ U ↔ !isDedekindCutFormula x ∧
    !rationalCutFormula (!rationalZeroFormula) ⊆ x ∧ x ⊆ !rationalCutFormula (!rationalOneFormula)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem dyadicUnit_zero : dyadicUnit (0 : V) = rationalOne V :=
  congrArg Subtype.val (InternalRational.dyadic_zero (V := V))

theorem dyadicUnit_halves {n : V} (hn : n ∈ (ω : V)) :
    rationalAdd (dyadicUnit (succ n)) (dyadicUnit (succ n)) = dyadicUnit n := by
  have h := congrArg Subtype.val (InternalRational.dyadic_halves (⟨n, hn⟩ : InternalNatural V))
  change rationalAdd (dyadicUnit (ordinalAdd n 1)) (dyadicUnit (ordinalAdd n 1)) = dyadicUnit n at h
  rwa [ordinalAdd_one_natural hn] at h

theorem binaryGreedyMid_state (x : V) {n : V} (hn : n ∈ (ω : V)) :
    binaryGreedyMid (binaryGreedyState x n) =
      rationalAdd (binaryGreedyValue x n) (dyadicUnit (succ n)) := by
  simp only [binaryGreedyMid, binaryGreedyState_index _ hn, binaryGreedyValue]

theorem binaryGreedyMid_mem (x : V) {n : V} (hn : n ∈ (ω : V)) :
    binaryGreedyMid (binaryGreedyState x n) ∈ internalRationals V := by
  rw [binaryGreedyMid_state _ hn]
  exact rationalAdd_mem (binaryGreedyValue_mem x hn) (dyadicUnit_mem (ω_succ_closed hn))

theorem binaryGreedyValue_succ_of_le {x n : V} (hn : n ∈ (ω : V))
    (h : rationalCut (binaryGreedyMid (binaryGreedyState x n)) ⊆ x) :
    binaryGreedyValue x (succ n) = binaryGreedyMid (binaryGreedyState x n) := by
  rw [binaryGreedyValue_succ _ hn, binaryGreedyDigitAt, binaryGreedyDigit_eq_one h,
    rationalNatural_one, rationalMul_comm rationalOne_mem (dyadicUnit_mem (ω_succ_closed hn)),
    rationalMul_one (dyadicUnit_mem (ω_succ_closed hn)), binaryGreedyMid_state _ hn]

theorem binaryGreedyValue_succ_of_not_le {x n : V} (hn : n ∈ (ω : V))
    (h : ¬rationalCut (binaryGreedyMid (binaryGreedyState x n)) ⊆ x) :
    binaryGreedyValue x (succ n) = binaryGreedyValue x n := by
  rw [binaryGreedyValue_succ _ hn, binaryGreedyDigitAt, binaryGreedyDigit_eq_zero h,
    rationalNatural_zero, rationalMul_comm rationalZero_mem (dyadicUnit_mem (ω_succ_closed hn)),
    rationalMul_zero (dyadicUnit_mem (ω_succ_closed hn)), rationalAdd_zero (binaryGreedyValue_mem x hn)]

theorem binaryGreedy_intervals {x : V} (hx : IsDedekindCut x)
    (hx0 : rationalCut (rationalZero V) ⊆ x) (hx1 : x ⊆ rationalCut (rationalOne V)) :
    ∀ n ∈ (ω : V), rationalCut (binaryGreedyValue x n) ⊆ x ∧
      x ⊆ rationalCut (rationalAdd (binaryGreedyValue x n) (dyadicUnit n)) := by
  apply naturalNumber_induction
    (fun n ↦ rationalCut (binaryGreedyValue x n) ⊆ x ∧
      x ⊆ rationalCut (rationalAdd (binaryGreedyValue x n) (dyadicUnit n)))
    (by definability)
  · rw [binaryGreedyValue_zero, dyadicUnit_zero,
      rationalAdd_comm rationalZero_mem rationalOne_mem, rationalAdd_zero rationalOne_mem]
    exact ⟨hx0, hx1⟩
  · intro n hn ih
    by_cases h : rationalCut (binaryGreedyMid (binaryGreedyState x n)) ⊆ x
    · rw [binaryGreedyValue_succ_of_le hn h]
      refine ⟨h, ?_⟩
      rw [binaryGreedyMid_state _ hn,
        rationalAdd_assoc (binaryGreedyValue_mem x hn) (dyadicUnit_mem (ω_succ_closed hn))
          (dyadicUnit_mem (ω_succ_closed hn)), dyadicUnit_halves hn]
      exact ih.2
    · rw [binaryGreedyValue_succ_of_not_le hn h]
      refine ⟨ih.1, ?_⟩
      rw [← binaryGreedyMid_state _ hn]
      exact (dedekindCuts_comparable hx (rationalCut_isCut (binaryGreedyMid_mem x hn))).resolve_right h

theorem binaryReal_greedy {x : V} (hx : IsDedekindCut x)
    (hx0 : rationalCut (rationalZero V) ⊆ x) (hx1 : x ⊆ rationalCut (rationalOne V)) :
    binaryReal (binaryGreedy x) = x := by
  symm
  apply binaryReal_unique (binaryGreedy_mem x) hx
  · intro n hn
    rw [← binaryGreedyValue_eq_binaryValue _ hn]
    exact (binaryGreedy_intervals hx hx0 hx1 n hn).1
  · intro n hn
    rw [binaryUpper, ← binaryGreedyValue_eq_binaryValue _ hn]
    exact (binaryGreedy_intervals hx hx0 hx1 n hn).2

noncomputable def unitReals (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  {x ∈ dedekindReals V ; rationalCut (rationalZero V) ⊆ x ∧ x ⊆ rationalCut (rationalOne V)}

theorem mem_unitReals_iff (x : V) : x ∈ unitReals V ↔ IsDedekindCut x ∧
    rationalCut (rationalZero V) ⊆ x ∧ x ⊆ rationalCut (rationalOne V) := by
  simp [unitReals, mem_dedekindReals_iff]

instance unitRealsFormula_defined : ℒₛₑₜ-function₀[V] (unitReals V) via unitRealsFormula :=
  ⟨fun v ↦ by simp [unitRealsFormula, mem_ext_iff (y := unitReals V), mem_unitReals_iff]⟩

theorem binaryReal_mem_unitReals {c : V} (hc : c ∈ cantorSpace V) : binaryReal c ∈ unitReals V :=
  (mem_unitReals_iff _).mpr ⟨binaryReal_isCut hc, binaryReal_unitInterval hc⟩

theorem binaryReal_greedy_of_mem {x : V} (hx : x ∈ unitReals V) : binaryReal (binaryGreedy x) = x := by
  obtain ⟨hcut, hx0, hx1⟩ := (mem_unitReals_iff x).mp hx
  exact binaryReal_greedy hcut hx0 hx1

theorem binaryReal_surjective {x : V} (hx : x ∈ unitReals V) :
    ∃ c ∈ cantorSpace V, binaryReal c = x :=
  ⟨binaryGreedy x, binaryGreedy_mem x, binaryReal_greedy_of_mem hx⟩

noncomputable def binaryRealGraph (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V := definableGraph (cantorSpace V) binaryReal binaryReal_definable

theorem binaryRealGraph_mem : binaryRealGraph V ∈ (unitReals V) ^ (cantorSpace V) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hc ↦ binaryReal_mem_unitReals hc)

theorem binaryRealGraph_range : range (binaryRealGraph V) = unitReals V := by
  apply SetTheory.subset_antisymm (range_subset_of_mem_function binaryRealGraph_mem)
  intro x hx
  obtain ⟨c, hc, hcx⟩ := binaryReal_surjective hx
  apply mem_range_of_kpair_mem (x := c)
  exact (pair_mem_definableGraph_iff _ _ _ c x).mpr ⟨hc, hcx.symm⟩

noncomputable def binaryGreedyGraph (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V := definableGraph (unitReals V) binaryGreedy binaryGreedy_definable

theorem binaryGreedyGraph_mem : binaryGreedyGraph V ∈ (cantorSpace V) ^ (unitReals V) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun x _ ↦ binaryGreedy_mem x)

theorem binaryGreedyGraph_injective : Injective (binaryGreedyGraph V) := by
  intro x y c hx hy
  obtain ⟨hxU, hcx⟩ := (pair_mem_definableGraph_iff _ _ _ x c).mp hx
  obtain ⟨hyU, hcy⟩ := (pair_mem_definableGraph_iff _ _ _ y c).mp hy
  have he : binaryGreedy x = binaryGreedy y := hcx.symm.trans hcy
  have hb := congrArg binaryReal he
  rwa [binaryReal_greedy_of_mem hxU, binaryReal_greedy_of_mem hyU] at hb

end ZFVP
