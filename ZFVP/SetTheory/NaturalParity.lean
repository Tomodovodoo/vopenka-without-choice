import ZFVP.SetTheory.BinaryPrefixSeparation

/-! Even and odd decomposition throughout the internal omega. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem natural_double_succ {n : V} (hn : n ∈ (ω : V)) :
    ordinalAdd (succ n) (succ n) = succ (succ (ordinalAdd n n)) := by
  let := IsOrdinal.of_mem hn
  rw [ordinalAdd_succ_left_natural hn (ω_succ_closed hn), ordinalAdd_succ]

theorem natural_even_or_odd : ∀ n ∈ (ω : V),
    ∃ k ∈ (ω : V), n = ordinalAdd k k ∨ n = succ (ordinalAdd k k) := by
  apply naturalNumber_induction (fun n ↦ ∃ k ∈ (ω : V),
    n = ordinalAdd k k ∨ n = succ (ordinalAdd k k)) (by definability)
  · exact ⟨0, by simp, Or.inl (ordinalAdd_zero (∅ : V)).symm⟩
  · intro n hn ih
    obtain ⟨k, hk, he | ho⟩ := ih
    · exact ⟨k, hk, Or.inr (congrArg succ he)⟩
    · exact ⟨succ k, ω_succ_closed hk, Or.inl ((congrArg succ ho).trans (natural_double_succ hk).symm)⟩

theorem natural_double_injective {n k : V} (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V))
    (h : ordinalAdd n n = ordinalAdd k k) : n = k := by
  have he : (⟨n, hn⟩ : InternalNatural V) + ⟨n, hn⟩ + 0 =
      (⟨k, hk⟩ : InternalNatural V) + ⟨k, hk⟩ + 0 := by
    simp only [add_zero]
    exact Subtype.ext h
  exact congrArg Subtype.val (InternalNatural.double_add_bit_injective (by norm_num) (by norm_num) he).1

theorem natural_double_ne_succ_double {n k : V} (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) :
    ordinalAdd n n ≠ succ (ordinalAdd k k) := by
  intro h
  have he : (⟨n, hn⟩ : InternalNatural V) + ⟨n, hn⟩ + 0 =
      (⟨k, hk⟩ : InternalNatural V) + ⟨k, hk⟩ + 1 := by
    apply Subtype.ext
    simpa only [InternalNatural.val_add, InternalNatural.val_zero, InternalNatural.val_one,
      ordinalAdd_one_natural (ordinalAdd_natural hk hk), zero_def, ordinalAdd_zero] using h
  exact zero_ne_one (InternalNatural.double_add_bit_injective (by norm_num) (by norm_num) he).2

end ZFVP
