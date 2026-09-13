import ZFVP.SetTheory.BinaryRealNullImagesIntervals

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def binaryNullCover (g p : V) : V :=
  definableGraph (ω : V) (binaryNullInterval g p) (by definability)

instance binaryNullCover_definable : ℒₛₑₜ-function₂[V] binaryNullCover := by
  have h : ℒₛₑₜ-relation₃[V] (fun d g p ↦ ∀ z, z ∈ d ↔
      ∃ i ∈ (ω : V), z = ⟨i, binaryNullInterval g p i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [binaryNullCover, mem_definableGraph_iff]

theorem binaryNullCover_value (g p : V) {i : V} (hi : i ∈ (ω : V)) :
    (binaryNullCover g p) ‘ i = binaryNullInterval g p i := value_definableGraph _ _ _ hi

theorem binaryNullCover_mem {g n E p : V} (hg : g ∈ E ^ n)
    (hE : E ⊆ binarySequences V) (hp : p ∈ (ω : V)) :
    binaryNullCover g p ∈ (realBasicCodes V) ^ (ω : V) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦ binaryNullInterval_mem hg hE hp hi)

/-- Widening each closed cylinder image adds exactly one geometric padding cost.
Unused finite-enumeration positions are genuine intervals with the same padding cost. -/
theorem binaryNullCover_cost {g n E p : V} (hg : g ∈ E ^ n)
    (hE : E ⊆ binarySequences V) (hp : p ∈ (ω : V)) :
    ∀ k ∈ (ω : V), realCoverCost (binaryNullCover g p) k =
      rationalAdd (rationalPartialSum (prefixPaddedWeights g) k) (realCoverCost (realNullPadding p) k) := by
  apply rationalPartialSum_add (prefixPaddedWeights_mem hg hE)
    (fun i hi ↦ realCoverLengths_mem (realNullPadding_mem hp) hi)
  intro i hi
  rw [realCoverLengths, value_definableGraph _ _ _ hi, binaryNullCover_value _ _ hi,
    binaryNullInterval_length hg hE hp hi, prefixPaddedWeights_value _ hi,
    realCoverLengths, value_definableGraph _ _ _ hi]

/-- The actual binary image of a Cantor-null set is null on the internal real line,
using rational open interval covers and internally finite rational length sums. -/
theorem binaryImage_realNull {A : V} (hA : A ⊆ cantorSpace V) (hnull : IsNull A) :
    IsRealNull (binaryImage A) := by
  intro m hm
  obtain ⟨E, hE, hpref, n, hn, g, hg, hgi, hgr, hcover, hweights⟩ :=
    isNull_prefixFree_padded_cover hA hnull (ω_succ_closed hm)
  have hnsub : n ⊆ (ω : V) := by
    rcases hn with hn | rfl
    · exact IsOrdinal.toIsTransitive.transitive n hn
    · exact subset_refl _
  have hcode := binaryNullCover_mem hg hE (ω_succ_closed hm)
  refine ⟨binaryNullCover g (succ m), ⟨hcode, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := (mem_binaryImage_iff _ _).mp hx
    obtain ⟨i, hi, hci⟩ := hcover c hc
    refine ⟨i, hnsub i hi, ?_⟩
    rw [binaryNullCover_value _ _ (hnsub i hi)]
    exact binaryNullInterval_covers hg hE (ω_succ_closed hm) (hnsub i hi) hi (hA c hc) hci
  · intro k hk
    rw [binaryNullCover_cost hg hE (ω_succ_closed hm) k hk]
    let s : InternalRational V := ⟨rationalPartialSum (prefixPaddedWeights g) k,
      rationalPartialSum_mem (prefixPaddedWeights_mem hg hE) k hk⟩
    let t : InternalRational V := ⟨realCoverCost (realNullPadding (succ m)) k,
      realCoverCost_mem (realNullPadding_mem (ω_succ_closed hm)) k hk⟩
    let d : InternalRational V := ⟨dyadicUnit (succ m), dyadicUnit_mem (ω_succ_closed hm)⟩
    have hs : s ≤ d := hweights k hk
    have ht : t ≤ d := realNullPadding_cost_bound (ω_succ_closed hm) hk
    have he : d + d = (⟨dyadicUnit m, dyadicUnit_mem hm⟩ : InternalRational V) :=
      Subtype.ext (dyadicUnit_halves hm)
    have hb : s + t ≤ d + d := add_le_add hs ht
    rw [he] at hb
    exact hb

end ZFVP
