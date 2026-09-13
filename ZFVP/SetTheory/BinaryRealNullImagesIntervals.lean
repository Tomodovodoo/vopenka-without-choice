import ZFVP.SetTheory.PrefixFreeNullCoverPadding
import ZFVP.SetTheory.RealNullPadding
import ZFVP.SetTheory.BinaryClosedImages
import ZFVP.SetTheory.CantorInfiniteOnes

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem binaryFiniteValue_eq_tail {s : V} (hs : s ∈ binarySequences V) :
    binaryValue s (domain s) = binaryValue (cantorOneTail s) (domain s) := by
  have : IsFunction s := binarySequence_isFunction hs
  have : IsFunction (cantorOneTail s) := IsFunction.of_mem (cantorOneTail_mem s)
  apply binaryValue_eq_of_agree _ _ (binarySequence_domain_mem hs)
  intro i hi
  exact (value_eq_of_subset_function (cantorOneTail_extends hs) hi).symm

theorem binaryFiniteValue_mem {s : V} (hs : s ∈ binarySequences V) :
    binaryValue s (domain s) ∈ internalRationals V := by
  rw [binaryFiniteValue_eq_tail hs]
  exact binaryValue_mem (cantorOneTail_mem s) (binarySequence_domain_mem hs)

noncomputable def binaryNullLeft (g i : V) : V := by
  classical
  exact if i ∈ domain g then binaryValue (g ‘ i) (domain (g ‘ i)) else rationalZero V

def binaryNullLeftFormula : SetTheorySemisentence 3 :=
  f“q g i. (i ∈ !domain.dfn g ∧ q = !binaryValueFormula (!value.dfn g i) (!domain.dfn (!value.dfn g i))) ∨
    (i ∉ !domain.dfn g ∧ q = !rationalZeroFormula)”
instance binaryNullLeftFormula_defined : ℒₛₑₜ-function₂[V] binaryNullLeft via binaryNullLeftFormula :=
  ⟨fun v ↦ by
    by_cases h : v 2 ∈ domain (v 1)
    · simp [binaryNullLeftFormula, binaryNullLeft, h]
    · simp [binaryNullLeftFormula, binaryNullLeft, h]⟩
instance binaryNullLeft_definable : ℒₛₑₜ-function₂[V] binaryNullLeft := binaryNullLeftFormula_defined.to_definable

noncomputable def binaryNullRadius (p i : V) : V := dyadicUnit (succ (succ (ordinalAdd p i)))
instance binaryNullRadius_definable : ℒₛₑₜ-function₂[V] binaryNullRadius := by unfold binaryNullRadius; definability

noncomputable def binaryNullInterval (g p i : V) : V :=
  ⟨rationalAdd (binaryNullLeft g i) (rationalNeg (binaryNullRadius p i)),
    rationalAdd (rationalAdd (binaryNullLeft g i) (prefixPaddedTerm g i)) (binaryNullRadius p i)⟩ₖ
instance binaryNullInterval_definable : ℒₛₑₜ-function₃[V] binaryNullInterval := by
  unfold binaryNullInterval
  definability

theorem binaryNullLeft_mem {g n E i : V} (hg : g ∈ E ^ n) (hE : E ⊆ binarySequences V) :
    binaryNullLeft g i ∈ internalRationals V := by
  by_cases hi : i ∈ domain g
  · simp only [binaryNullLeft, hi, ↓reduceIte]
    exact binaryFiniteValue_mem (hE _ (function_value_mem hg (by simpa only [domain_eq_of_mem_function hg] using hi)))
  · simp only [binaryNullLeft, hi, ↓reduceIte]
    exact rationalZero_mem

theorem binaryNullRadius_mem {p i : V} (hp : p ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    binaryNullRadius p i ∈ internalRationals V := dyadicUnit_mem (ω_succ_closed (ω_succ_closed (ordinalAdd_natural hp hi)))

theorem binaryNullRadius_pos {p i : V} (hp : p ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    InternalRationalLT (rationalZero V) (binaryNullRadius p i) :=
  dyadicUnit_positive (ω_succ_closed (ω_succ_closed (ordinalAdd_natural hp hi)))

theorem binaryNullWeight_mem {g n E i : V} (hg : g ∈ E ^ n) (hE : E ⊆ binarySequences V) (hi : i ∈ (ω : V)) :
    prefixPaddedTerm g i ∈ internalRationals V := by
  rw [← prefixPaddedWeights_value _ hi]
  exact prefixPaddedWeights_mem hg hE i hi

theorem binaryNullWeight_nonnegative {g n E i : V} (hg : g ∈ E ^ n) (hE : E ⊆ binarySequences V) :
    ¬InternalRationalLT (prefixPaddedTerm g i) (rationalZero V) := by
  by_cases hi : i ∈ domain g
  · simp only [prefixPaddedTerm, hi, ↓reduceIte]
    have hs := hE _ (function_value_mem hg (by simpa only [domain_eq_of_mem_function hg] using hi))
    exact le_of_lt (InternalRational.dyadic_pos (⟨domain (g ‘ i), binarySequence_domain_mem hs⟩ : InternalNatural V))
  · simp only [prefixPaddedTerm, hi, ↓reduceIte]
    exact internalRationalLT_irrefl rationalZero_mem

theorem binaryNullInterval_mem {g n E p i : V} (hg : g ∈ E ^ n)
    (hE : E ⊆ binarySequences V) (hp : p ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    binaryNullInterval g p i ∈ realBasicCodes V := by
  let l : InternalRational V := ⟨binaryNullLeft g i, binaryNullLeft_mem hg hE⟩
  let w : InternalRational V := ⟨prefixPaddedTerm g i, binaryNullWeight_mem hg hE hi⟩
  let r : InternalRational V := ⟨binaryNullRadius p i, binaryNullRadius_mem hp hi⟩
  have hr : 0 < r := binaryNullRadius_pos hp hi
  have hw : 0 ≤ w := binaryNullWeight_nonnegative hg hE
  apply (pair_mem_realBasicCodes_iff _ _).mpr
  refine ⟨rationalAdd_mem l.property (rationalNeg_mem r.property),
    rationalAdd_mem (rationalAdd_mem l.property w.property) r.property, ?_⟩
  exact (lt_trans (sub_lt_self l hr) (lt_of_le_of_lt (le_add_of_nonneg_right hw) (lt_add_of_pos_right _ hr)) :
    l - r < l + w + r)

theorem binaryNullInterval_length {g n E p i : V} (hg : g ∈ E ^ n)
    (hE : E ⊆ binarySequences V) (hp : p ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    realIntervalLength (binaryNullInterval g p i) =
      rationalAdd (prefixPaddedTerm g i) (realIntervalLength ((realNullPadding p) ‘ i)) := by
  rw [realNullPadding_length hp hi]
  let l : InternalRational V := ⟨binaryNullLeft g i, binaryNullLeft_mem hg hE⟩
  let w : InternalRational V := ⟨prefixPaddedTerm g i, binaryNullWeight_mem hg hE hi⟩
  let r : InternalRational V := ⟨binaryNullRadius p i, binaryNullRadius_mem hp hi⟩
  have he : (l + w + r) - (l - r) = w + (r + r) := by ring
  have hv := congrArg Subtype.val he
  simp only [realIntervalLength, binaryNullInterval, kpair.π₁_kpair, kpair.π₂_kpair]
  rw [← dyadicUnit_halves (ω_succ_closed (ordinalAdd_natural hp hi))]
  exact hv

theorem binaryNullInterval_covers {g n E p i c : V} (hg : g ∈ E ^ n)
    (hE : E ⊆ binarySequences V) (hp : p ∈ (ω : V)) (hi : i ∈ (ω : V))
    (hin : i ∈ n) (hc : c ∈ cantorSpace V) (hsc : (g ‘ i) ⊆ c) :
    binaryReal c ∈ realInterval (kpair.π₁ (binaryNullInterval g p i)) (kpair.π₂ (binaryNullInterval g p i)) := by
  have hs := hE _ (function_value_mem hg hin)
  have hid : i ∈ domain g := by rwa [domain_eq_of_mem_function hg]
  have hl : binaryNullLeft g i = binaryValue (cantorOneTail (g ‘ i)) (domain (g ‘ i)) := by
    simp only [binaryNullLeft, hid, ↓reduceIte]
    exact binaryFiniteValue_eq_tail hs
  have hw : prefixPaddedTerm g i = dyadicUnit (domain (g ‘ i)) := by simp [prefixPaddedTerm, hid]
  have hcode := (pair_mem_realBasicCodes_iff _ _).mp (binaryNullInterval_mem hg hE hp hi)
  let l : InternalRational V := ⟨binaryNullLeft g i, binaryNullLeft_mem hg hE⟩
  let w : InternalRational V := ⟨prefixPaddedTerm g i, binaryNullWeight_mem hg hE hi⟩
  let r : InternalRational V := ⟨binaryNullRadius p i, binaryNullRadius_mem hp hi⟩
  have hr : 0 < r := binaryNullRadius_pos hp hi
  unfold binaryNullInterval
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  apply binaryReal_interval_of_prefix (cantorOneTail_mem (g ‘ i)) hc (binarySequence_domain_mem hs)
    hcode.1 hcode.2.1 ?_ ?_ ?_
  · rw [← hl]
    exact (sub_lt_self l hr : l - r < l)
  · rw [binaryUpper, ← hl, ← hw]
    exact (lt_add_of_pos_right (l + w) hr : l + w < l + w + r)
  · rw [(subset_iff_restrict_eq (cantorOneTail_mem (g ‘ i)) hs).mp (cantorOneTail_extends hs)]
    exact hsc

end ZFVP
