import ZFVP.SetTheory.BinaryExpansionValues

/-! Nesting of binary prefix intervals, including all nonstandard indices. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem naturalNumber_chain (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (hrefl : ∀ n ∈ (ω : V), R n n)
    (htrans : ∀ a ∈ (ω : V), ∀ b ∈ (ω : V), ∀ c ∈ (ω : V), R a b → R b c → R a c)
    (hstep : ∀ n ∈ (ω : V), R n (succ n)) :
    ∀ n ∈ (ω : V), ∀ m ∈ (ω : V), m ⊆ n → R m n := by
  apply naturalNumber_induction (fun n ↦ ∀ m ∈ (ω : V), m ⊆ n → R m n) (by definability)
  · intro m _ hm
    have he : m = (0 : V) := subset_antisymm hm (empty_subset m)
    rw [he]
    exact hrefl 0 (by simp)
  · intro n hn ih m hm hmn
    let := IsOrdinal.of_mem hn
    let := IsOrdinal.of_mem hm
    rcases IsOrdinal.subset_iff.mp hmn with he | hlt
    · rw [he]
      exact hrefl _ (ω_succ_closed hn)
    · have hmle : m ⊆ n := by
        rcases mem_succ_iff.mp hlt with rfl | hlt
        · exact subset_refl _
        · exact IsOrdinal.toIsTransitive.transitive _ hlt
      exact htrans m hm n hn (succ n) (ω_succ_closed hn) (ih m hm hmle) (hstep n hn)

theorem binaryIntervals_nested {c n m : V} (hc : c ∈ cantorSpace V)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hnm : n ⊆ m) :
    ¬ InternalRationalLT (binaryValue c m) (binaryValue c n) ∧
      ¬ InternalRationalLT (binaryUpper c n) (binaryUpper c m) := by
  apply naturalNumber_chain
    (fun a b ↦ ¬ InternalRationalLT (binaryValue c b) (binaryValue c a) ∧
      ¬ InternalRationalLT (binaryUpper c a) (binaryUpper c b)) (by definability)
    ?_ ?_ (fun k hk ↦ binaryValues_step hc hk) m hm n hn hnm
  · intro k hk
    exact ⟨internalRationalLT_irrefl (binaryValue_mem hc hk),
      internalRationalLT_irrefl (binaryUpper_mem hc hk)⟩
  · intro a ha b hb d hd hab hbd
    have hlo : InternalRational.binaryApprox c hc (⟨a, ha⟩ : InternalNatural V) ≤
        InternalRational.binaryApprox c hc (⟨d, hd⟩ : InternalNatural V) :=
      le_trans (show InternalRational.binaryApprox c hc (⟨a, ha⟩ : InternalNatural V) ≤
        InternalRational.binaryApprox c hc (⟨b, hb⟩ : InternalNatural V) from hab.1) hbd.1
    have hup : (⟨binaryUpper c d, binaryUpper_mem hc hd⟩ : InternalRational V) ≤
        (⟨binaryUpper c a, binaryUpper_mem hc ha⟩ : InternalRational V) :=
      le_trans (show (⟨binaryUpper c d, binaryUpper_mem hc hd⟩ : InternalRational V) ≤
        (⟨binaryUpper c b, binaryUpper_mem hc hb⟩ : InternalRational V) from hbd.2) hab.2
    exact ⟨hlo, hup⟩

namespace InternalRational

theorem binaryApprox_mono (c : V) (hc : c ∈ cantorSpace V) {n m : InternalNatural V} (hnm : n ≤ m) :
    binaryApprox c hc n ≤ binaryApprox c hc m :=
  (binaryIntervals_nested hc n.property m.property hnm).1

theorem binaryApprox_upper_antitone (c : V) (hc : c ∈ cantorSpace V)
    {n m : InternalNatural V} (hnm : n ≤ m) :
    binaryApprox c hc m + dyadic m ≤ binaryApprox c hc n + dyadic n :=
  (binaryIntervals_nested hc n.property m.property hnm).2

theorem binaryApprox_lt_upper (c : V) (hc : c ∈ cantorSpace V) (n m : InternalNatural V) :
    binaryApprox c hc n < binaryApprox c hc m + dyadic m := by
  rcases le_total n m with hnm | hmn
  · exact lt_of_le_of_lt (binaryApprox_mono c hc hnm) (lt_add_of_pos_right _ (dyadic_pos m))
  · exact lt_of_lt_of_le (lt_add_of_pos_right _ (dyadic_pos n)) (binaryApprox_upper_antitone c hc hmn)

end InternalRational

theorem binaryValue_lt_upper {c n m : V} (hc : c ∈ cantorSpace V)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) :
    InternalRationalLT (binaryValue c n) (binaryUpper c m) :=
  InternalRational.binaryApprox_lt_upper c hc (⟨n, hn⟩ : InternalNatural V) (⟨m, hm⟩ : InternalNatural V)

theorem binaryValue_eq_of_agree (c d : V) {n : V} (hn : n ∈ (ω : V))
    (h : ∀ i ∈ n, c ‘ i = d ‘ i) : binaryValue c n = binaryValue d n := by
  rw [binaryValue, binaryValue, binaryNumerator_eq_of_agree c d hn h]

theorem binaryUpper_eq_of_agree (c d : V) {n : V} (hn : n ∈ (ω : V))
    (h : ∀ i ∈ n, c ‘ i = d ‘ i) : binaryUpper c n = binaryUpper d n := by
  rw [binaryUpper, binaryUpper, binaryValue_eq_of_agree c d hn h]

end ZFVP
