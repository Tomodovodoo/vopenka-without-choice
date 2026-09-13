import ZFVP.SetTheory.RationalPartialSums

/-! Shift decomposition and monotonicity for nonnegative internal rational sums. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def rationalSequenceShift (f n : V) : V :=
  definableGraph (ω : V) (fun k ↦ f ‘ (ordinalAdd n k)) (by definability)

instance rationalSequenceShift_definable : ℒₛₑₜ-function₂[V] rationalSequenceShift := by
  have h : ℒₛₑₜ-relation₃ (fun g f n : V ↦ ∀ p, p ∈ g ↔
      ∃ k ∈ (ω : V), p = ⟨k, f ‘ (ordinalAdd n k)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [rationalSequenceShift, mem_definableGraph_iff]

theorem rationalSequenceShift_value (f n : V) {k : V} (hk : k ∈ (ω : V)) :
    (rationalSequenceShift f n) ‘ k = f ‘ (ordinalAdd n k) := value_definableGraph _ _ _ hk

theorem rationalPartialSum_shift {f n : V}
    (hf : ∀ k ∈ (ω : V), f ‘ k ∈ internalRationals V) (hn : n ∈ (ω : V)) :
    ∀ m ∈ (ω : V), rationalPartialSum f (ordinalAdd n m) =
      rationalAdd (rationalPartialSum f n) (rationalPartialSum (rationalSequenceShift f n) m) := by
  have hshift : ∀ k ∈ (ω : V), (rationalSequenceShift f n) ‘ k ∈ internalRationals V := by
    intro k hk
    rw [rationalSequenceShift_value _ _ hk]
    exact hf _ (ordinalAdd_natural hn hk)
  apply naturalNumber_induction
    (fun m ↦ rationalPartialSum f (ordinalAdd n m) =
      rationalAdd (rationalPartialSum f n) (rationalPartialSum (rationalSequenceShift f n) m))
    (by definability)
  · rw [rationalPartialSum_zero, rationalAdd_zero (rationalPartialSum_mem hf n hn),
      show (0 : V) = ∅ from rfl, ordinalAdd_zero]
  · intro m hm ih
    have : IsOrdinal n := IsOrdinal.of_mem hn
    have : IsOrdinal m := IsOrdinal.of_mem hm
    rw [ordinalAdd_succ, rationalPartialSum_succ _ (ordinalAdd_natural hn hm),
      rationalPartialSum_succ _ hm, rationalSequenceShift_value _ _ hm, ih,
      rationalAdd_assoc (rationalPartialSum_mem hf n hn)
        (rationalPartialSum_mem hshift m hm) (hf _ (ordinalAdd_natural hn hm))]

theorem rationalPartialSum_monotone {f n m : V}
    (hf : ∀ k ∈ (ω : V), f ‘ k ∈ internalRationals V)
    (hpos : ∀ k ∈ (ω : V), ¬ InternalRationalLT (f ‘ k) (rationalZero V))
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hnm : n ⊆ m) :
    ¬ InternalRationalLT (rationalPartialSum f m) (rationalPartialSum f n) := by
  obtain ⟨k, hk, he⟩ := ordinalAdd_difference_natural hn hm hnm
  have hshift : ∀ i ∈ (ω : V), (rationalSequenceShift f n) ‘ i ∈ internalRationals V := by
    intro i hi
    rw [rationalSequenceShift_value _ _ hi]
    exact hf _ (ordinalAdd_natural hn hi)
  have hshiftpos : ∀ i ∈ (ω : V), ¬ InternalRationalLT
      ((rationalSequenceShift f n) ‘ i) (rationalZero V) := by
    intro i hi
    rw [rationalSequenceShift_value _ _ hi]
    exact hpos _ (ordinalAdd_natural hn hi)
  rw [← he, rationalPartialSum_shift hf hn k hk]
  exact (le_add_of_nonneg_right (show (0 : InternalRational V) ≤
      ⟨rationalPartialSum (rationalSequenceShift f n) k, rationalPartialSum_mem hshift k hk⟩ from
      rationalPartialSum_nonnegative hshift hshiftpos k hk) :
    (⟨rationalPartialSum f n, rationalPartialSum_mem hf n hn⟩ : InternalRational V) ≤
      ⟨rationalPartialSum f n, rationalPartialSum_mem hf n hn⟩ +
      ⟨rationalPartialSum (rationalSequenceShift f n) k, rationalPartialSum_mem hshift k hk⟩)

end ZFVP
