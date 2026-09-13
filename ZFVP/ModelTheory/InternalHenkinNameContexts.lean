import ZFVP.ModelTheory.InternalHenkinBooleanClosure
import ZFVP.Syntax.NaturalReverseIndices

/-! Finite context enlargement preserves the natural names assigned by reverse
indexing, and preserves acceptance of each renamed formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem tailShiftIndices_zero {n : V} (hn : n ∈ (ω : V)) :
    tailShiftIndices n 0 = SetTheory.identity n := by
  have he : ordinalAdd n (0 : V) = n := ordinalAdd_zero n
  have hf := tailShiftIndices_function hn (show (0 : V) ∈ (ω : V) by simp)
  rw [he] at hf
  apply function_eq_of_values hf (identity_mem_function n)
  intro i hi
  rw [tailShiftIndices_value hi, identity_value hi, zero_def, ordinalAdd_zero]

theorem tailShiftIndices_compose_successor {n k : V} (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) :
    compose (tailShiftIndices n k) (successorIndices (ordinalAdd n k)) = tailShiftIndices n (succ k) := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have : IsOrdinal k := IsOrdinal.of_mem hk
  have ht := tailShiftIndices_function hn hk
  have hs := successorIndices_function (ordinalAdd_natural hn hk)
  have hf := tailShiftIndices_function hn (ω_succ_closed hk)
  rw [ordinalAdd_succ] at hf
  apply function_eq_of_values (compose_function ht hs) hf
  intro i hi
  have : IsOrdinal i := IsOrdinal.of_mem hi
  rw [value_compose_of_mem_function ht hs hi,
    show (successorIndices (ordinalAdd n k)) ‘ ((tailShiftIndices n k) ‘ i) =
      succ ((tailShiftIndices n k) ‘ i) from value_definableGraph _ _ _ (function_value_mem ht hi),
    tailShiftIndices_value hi, tailShiftIndices_value hi, ordinalAdd_succ]

theorem henkinLiftCode_eq_rename {n φ k : V} (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hk : k ∈ (ω : V)) : henkinLiftCode ⟨n, φ⟩ₖ k =
      ⟨ordinalAdd n k, renameMembershipFormula n (ordinalAdd n k) (tailShiftIndices n k) φ⟩ₖ := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  have hR : ℒₛₑₜ-function₁[V] (fun k ↦
      renameMembershipFormula n (ordinalAdd n k) (tailShiftIndices n k) φ) :=
    Language.DefinableFunction₄.comp (by definability) (by definability) (by definability) (by definability)
  apply naturalNumber_induction (fun k ↦ henkinLiftCode ⟨n, φ⟩ₖ k =
    ⟨ordinalAdd n k, renameMembershipFormula n (ordinalAdd n k) (tailShiftIndices n k) φ⟩ₖ)
    (by definability) ?_ ?_ k hk
  · rw [henkinLiftCode_zero, tailShiftIndices_zero hn,
      show ordinalAdd n (0 : V) = n from ordinalAdd_zero n, renameMembershipFormula_identity hn hφ]
  · intro k hk ih
    have : IsOrdinal n := IsOrdinal.of_mem hn
    have : IsOrdinal k := IsOrdinal.of_mem hk
    rw [henkinLiftCode_succ _ hk, ih]
    simp only [henkinShiftCode, kpair.π₁_kpair, kpair.π₂_kpair, henkinShiftFormula]
    rw [renameMembershipFormula_compose hn (ordinalAdd_natural hn hk)
      (ω_succ_closed (ordinalAdd_natural hn hk)) (tailShiftIndices_function hn hk)
      (successorIndices_function (ordinalAdd_natural hn hk)) hφ, tailShiftIndices_compose_successor hn hk,
      ordinalAdd_succ]

theorem IsCompleteHenkinSequence.tail_rename_iff (hω : Schmerl.HasStandardOmega V) {T s n φ k : V}
    (hs : IsCompleteHenkinSequence T s) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hk : k ∈ (ω : V)) :
    HenkinAccepted T s ⟨ordinalAdd n k, renameMembershipFormula n (ordinalAdd n k) (tailShiftIndices n k) φ⟩ₖ ↔
      HenkinAccepted T s ⟨n, φ⟩ₖ := by
  rw [← henkinLiftCode_eq_rename hφ hk]
  exact hs.lift_iff hω hφ hk

theorem reverseIndices_omega_function {n : V} (hn : n ∈ (ω : V)) :
    reverseIndices n ∈ (ω : V) ^ n :=
  mem_function_of_mem_function_of_subset (reverseIndices_function hn) (IsOrdinal.toIsTransitive.transitive n hn)

theorem tailShiftIndices_compose_reverse {n k : V} (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) :
    compose (tailShiftIndices n k) (reverseIndices (ordinalAdd n k)) = reverseIndices n := by
  have ht := tailShiftIndices_function hn hk
  have hR := reverseIndices_omega_function (ordinalAdd_natural hn hk)
  apply function_eq_of_values (compose_function ht hR) (reverseIndices_omega_function hn)
  intro i hi
  rw [value_compose_of_mem_function ht hR hi, tailShiftIndices_value hi, reverseIndices_add hn hk hi]

theorem reverseNameAssignment_extend {m r k : V} (hm : m ∈ (ω : V)) (hk : k ∈ (ω : V)) :
    compose (compose r (tailShiftIndices m k)) (reverseIndices (ordinalAdd m k)) =
      compose r (reverseIndices m) := by
  rw [graph_compose_assoc, tailShiftIndices_compose_reverse hm hk]

theorem IsCompleteHenkinSequence.named_rename_extend (hω : Schmerl.HasStandardOmega V)
    {T s n m r φ k : V} (hs : IsCompleteHenkinSequence T s)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hk : k ∈ (ω : V)) :
    HenkinAccepted T s ⟨ordinalAdd m k,
      renameMembershipFormula n (ordinalAdd m k) (compose r (tailShiftIndices m k)) φ⟩ₖ ↔
      HenkinAccepted T s ⟨m, renameMembershipFormula n m r φ⟩ₖ := by
  rw [← renameMembershipFormula_compose hn hm (ordinalAdd_natural hm hk) hr (tailShiftIndices_function hm hk) hφ]
  exact hs.tail_rename_iff hω (renameMembershipFormula_mem hn hm hr hφ) hk

end ZFVP
