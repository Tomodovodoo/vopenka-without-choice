import ZFVP.SetTheory.BinaryExpansionValues

/-! Distinct equal-length binary prefixes have separated dyadic intervals. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace InternalNatural

theorem double_add_bit_injective {a b i j : InternalNatural V} (hi : i < 2) (hj : j < 2)
    (he : a + a + i = b + b + j) : a = b ∧ i = j := by
  have hab : a = b := by
    rcases lt_trichotomy a b with h | h | h
    · have hlt := lt_of_lt_of_le (double_add_bit_lt h hi)
        (le_add_of_nonneg_right (nonneg j))
      exact (ne_of_lt hlt he).elim
    · exact h
    · have hlt := lt_of_lt_of_le (double_add_bit_lt h hj)
        (le_add_of_nonneg_right (nonneg i))
      exact (ne_of_lt hlt he.symm).elim
  refine ⟨hab, ?_⟩
  rw [hab] at he
  exact add_left_cancel he

end InternalNatural

theorem binaryNumerator_agree_of_eq {c d n : V} (hc : c ∈ cantorSpace V)
    (hd : d ∈ cantorSpace V) (hn : n ∈ (ω : V))
    (he : binaryNumerator c n = binaryNumerator d n) : ∀ i ∈ n, c ‘ i = d ‘ i := by
  apply naturalNumber_induction
    (fun n ↦ binaryNumerator c n = binaryNumerator d n → ∀ i ∈ n, c ‘ i = d ‘ i)
    (by definability) ?_ ?_ n hn he
  · intro _ i hi
    exact (not_mem_empty hi).elim
  · intro n hn ih he
    rw [binaryNumerator_succ _ hn, binaryNumerator_succ _ hn] at he
    let N : InternalNatural V := ⟨n, hn⟩
    have he' : InternalNatural.binaryNumeratorOf c hc N + InternalNatural.binaryNumeratorOf c hc N +
        InternalNatural.binaryDigitOf c hc N =
      InternalNatural.binaryNumeratorOf d hd N + InternalNatural.binaryNumeratorOf d hd N +
        InternalNatural.binaryDigitOf d hd N := Subtype.ext he
    obtain ⟨hnumer, hbit⟩ := InternalNatural.double_add_bit_injective
      (InternalNatural.binaryDigitOf_lt_two c hc N) (InternalNatural.binaryDigitOf_lt_two d hd N) he'
    have hprior := ih (congrArg Subtype.val hnumer)
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact congrArg Subtype.val hbit
    · exact hprior i hi

theorem binaryPrefix_eq_of_numerator_eq {c d n : V} (hc : c ∈ cantorSpace V)
    (hd : d ∈ cantorSpace V) (hn : n ∈ (ω : V))
    (he : binaryNumerator c n = binaryNumerator d n) : c ↾ n = d ↾ n := by
  have hcf := function_restrict_mem hc (IsTransitive.ω.transitive _ hn)
  have hdf := function_restrict_mem hd (IsTransitive.ω.transitive _ hn)
  have : IsFunction c := IsFunction.of_mem hc
  have : IsFunction d := IsFunction.of_mem hd
  have : IsFunction (c ↾ n) := IsFunction.of_mem hcf
  have : IsFunction (d ↾ n) := IsFunction.of_mem hdf
  apply functions_eq_of_domain_values (by rw [domain_eq_of_mem_function hcf, domain_eq_of_mem_function hdf])
  intro i hi
  rw [domain_eq_of_mem_function hcf] at hi
  rw [value_restrict (by rw [domain_eq_of_mem_function hc]; exact IsTransitive.ω.transitive _ hn _ hi) hi,
    value_restrict (by rw [domain_eq_of_mem_function hd]; exact IsTransitive.ω.transitive _ hn _ hi) hi]
  exact binaryNumerator_agree_of_eq hc hd hn he i hi

namespace InternalRational

theorem binaryApprox_gap {c d : V} (hc : c ∈ cantorSpace V) (hd : d ∈ cantorSpace V)
    (n : InternalNatural V)
    (hlt : InternalNatural.binaryNumeratorOf c hc n < InternalNatural.binaryNumeratorOf d hd n) :
    binaryApprox c hc n + dyadic n ≤ binaryApprox d hd n := by
  have h := (ofNatural_le_iff _ _).mpr (InternalNatural.add_one_le_of_lt hlt)
  rw [ofNatural_add, ofNatural_one] at h
  have hm := mul_le_mul_of_nonneg_right h (le_of_lt (dyadic_pos n))
  simpa only [add_mul, one_mul, binaryApprox] using hm

end InternalRational

end ZFVP
