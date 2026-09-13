import ZFVP.Syntax.MembershipRenaming

/-! Swapping the first two bound variables preserves every internal formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem compose_assignmentPrepend {n m r b A i : V} (hn : n ∈ (ω : V))
    (hr : r ∈ m ^ n) (hb : b ∈ A ^ m) (hi : i ∈ m) :
    compose (assignmentPrepend n r i) b = assignmentPrepend n (compose r b) (b ‘ i) := by
  have hp := assignmentPrepend_mem_function hn hr hi
  apply function_eq_of_values (compose_function hp hb)
    (assignmentPrepend_mem_function hn (compose_function hr hb) (function_value_mem hb hi))
  intro j hj
  have hjω : j ∈ (ω : V) := IsOrdinal.toIsTransitive.mem_trans hj (ω_succ_closed hn)
  rcases internalNatural_cases hjω with rfl | ⟨k, hk, rfl⟩
  · rw [value_compose_of_mem_function hp hb hj, assignmentPrepend_zero hn,
      assignmentPrepend_zero hn]
  · let := IsOrdinal.of_mem hk
    have hne : succ k ≠ (0 : V) := by
      intro he
      have hmem : k ∈ succ k := by simp
      rw [he] at hmem
      exact not_mem_empty hmem
    have hkn : k ∈ n := by
      simpa [sUnion_succ_of_transitive] using natural_predecessor_mem hn hj hne
    rw [value_compose_of_mem_function hp hb hj, assignmentPrepend_succ hn hkn,
      assignmentPrepend_succ hn hkn, value_compose_of_mem_function hr hb hkn]

noncomputable def shiftTwoIndices (n : V) : V :=
  definableGraph n (fun i ↦ succ (succ i)) (by definability)

theorem shiftTwoIndices_mem {n : V} (hn : n ∈ (ω : V)) :
    shiftTwoIndices n ∈ succ (succ n) ^ n := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  exact succ_mem_succ_of_natural_mem (ω_succ_closed hn) (succ_mem_succ_of_natural_mem hn hi)

noncomputable def swapFirstTwoIndices (n : V) : V :=
  assignmentPrepend (succ n) (assignmentPrepend n (shiftTwoIndices n) 0) (succ 0)

theorem swapFirstTwoIndices_mem {n : V} (hn : n ∈ (ω : V)) :
    swapFirstTwoIndices n ∈ succ (succ n) ^ succ (succ n) :=
  assignmentPrepend_mem_function (ω_succ_closed hn)
    (assignmentPrepend_mem_function hn (shiftTwoIndices_mem hn) (zero_mem_succ_natural (ω_succ_closed hn)))
    (succ_mem_succ_of_natural_mem (ω_succ_closed hn) (zero_mem_succ_natural hn))

theorem compose_swapFirstTwo {A n b x y : V} (hn : n ∈ (ω : V))
    (hb : b ∈ A ^ n) (hx : x ∈ A) (hy : y ∈ A) :
    compose (swapFirstTwoIndices n) (assignmentPrepend (succ n) (assignmentPrepend n b x) y) =
      assignmentPrepend (succ n) (assignmentPrepend n b y) x := by
  have hb1 := assignmentPrepend_mem_function hn hb hx
  have hb2 := assignmentPrepend_mem_function (ω_succ_closed hn) hb1 hy
  have h0 := zero_mem_succ_natural (ω_succ_closed hn)
  have h1 := succ_mem_succ_of_natural_mem (ω_succ_closed hn) (zero_mem_succ_natural hn)
  have htail : compose (shiftTwoIndices n)
      (assignmentPrepend (succ n) (assignmentPrepend n b x) y) = b := by
    apply function_eq_of_values (compose_function (shiftTwoIndices_mem hn) hb2) hb
    intro i hi
    rw [value_compose_of_mem_function (shiftTwoIndices_mem hn) hb2 hi,
      show (shiftTwoIndices n) ‘ i = succ (succ i) from value_definableGraph _ _ _ hi,
      assignmentPrepend_succ (ω_succ_closed hn) (succ_mem_succ_of_natural_mem hn hi),
      assignmentPrepend_succ hn hi]
  rw [swapFirstTwoIndices, compose_assignmentPrepend (ω_succ_closed hn)
    (assignmentPrepend_mem_function hn (shiftTwoIndices_mem hn) h0) hb2 h1,
    compose_assignmentPrepend hn (shiftTwoIndices_mem hn) hb2 h0, htail,
    assignmentPrepend_zero (ω_succ_closed hn),
    assignmentPrepend_succ (ω_succ_closed hn) (zero_mem_succ_natural hn), assignmentPrepend_zero hn]

noncomputable def swapMembershipFormula (n φ : V) : V :=
  renameMembershipFormula (succ (succ n)) (succ (succ n)) (swapFirstTwoIndices n) φ

theorem swapMembershipFormula_mem {n φ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ (succ n))) :
    swapMembershipFormula n φ ∈ formulaSet membershipLanguageCode ∅ (succ (succ n)) :=
  renameMembershipFormula_mem (ω_succ_closed (ω_succ_closed hn)) (ω_succ_closed (ω_succ_closed hn))
    (swapFirstTwoIndices_mem hn) hφ

theorem membershipSatisfies_swap {A n φ b x y : V} (hA : IsNonempty A) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ (succ n)))
    (hb : b ∈ A ^ n) (hx : x ∈ A) (hy : y ∈ A) :
    MembershipSatisfies A (succ (succ n)) (swapMembershipFormula n φ)
      (assignmentPrepend (succ n) (assignmentPrepend n b x) y) ↔
    MembershipSatisfies A (succ (succ n)) φ
      (assignmentPrepend (succ n) (assignmentPrepend n b y) x) := by
  have he := membershipSatisfies_rename hA (ω_succ_closed (ω_succ_closed hn))
    (ω_succ_closed (ω_succ_closed hn)) (swapFirstTwoIndices_mem hn) hφ
    (assignmentPrepend_mem_function (ω_succ_closed hn) (assignmentPrepend_mem_function hn hb hx) hy)
  rw [compose_swapFirstTwo hn hb hx hy] at he
  exact he

end ZFVP
