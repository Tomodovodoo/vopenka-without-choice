import ZFVP.Syntax.MembershipAtomicSemantics

/-! Atomic membership syntax described without the term-family predicate. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def boundPairArguments (i j : V) : V := standardTuple ![boundVarCode i, boundVarCode j]

instance boundPairArguments_definable : ℒₛₑₜ-function₂[V] boundPairArguments := by
  unfold boundPairArguments standardTuple
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
  definability

def IsMembershipAtomicArguments (n r args : V) : Prop :=
  (r = equalityToken ∨ r = relationToken (0 : V) ∨ r = relationToken (1 : V)) ∧
    ∃ i ∈ n, ∃ j ∈ n, args = boundPairArguments i j

instance isMembershipAtomicArguments_definable : ℒₛₑₜ-relation₃[V] IsMembershipAtomicArguments := by
  unfold IsMembershipAtomicArguments equalityToken
  definability

theorem boundPairArguments_valid {n i j : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) (hj : j ∈ n) :
    boundPairArguments i j ∈ termSet membershipLanguageCode ∅ n ^ (2 : V) := by
  apply standardTuple_mem_function
  intro a
  have hc := (termSet_closed (membershipLanguageCode_valid (V := V)) hn ∅).1
  refine Fin.cases ?_ (fun a ↦ Fin.cases ?_ (fun b ↦ Fin.elim0 b) a) a
  · exact hc i hi
  · exact hc j hj

theorem membershipArguments_pair {n args : V} (hn : n ∈ (ω : V))
    (ha : args ∈ termSet membershipLanguageCode ∅ n ^ (2 : V)) :
    ∃ i ∈ n, ∃ j ∈ n, args = boundPairArguments i j := by
  obtain ⟨i, hi, h0⟩ := membershipTerm_cases hn (function_value_mem ha (show (0 : V) ∈ (2 : V) by simp))
  obtain ⟨j, hj, h1⟩ := membershipTerm_cases hn (function_value_mem ha (show (1 : V) ∈ (2 : V) by simp))
  refine ⟨i, hi, j, hj, ?_⟩
  have : IsFunction args := IsFunction.of_mem ha
  have : IsFunction (boundPairArguments i j) := standardTuple_isFunction _
  apply functions_eq_of_domain_values (by simpa [boundPairArguments] using domain_eq_of_mem_function ha)
  intro a harg
  rw [domain_eq_of_mem_function ha] at harg
  obtain ⟨k, rfl⟩ := (mem_natCast_iff a 2).mp harg
  change args ‘ (k.val : V) = (standardTuple ![boundVarCode i, boundVarCode j]) ‘ (k.val : V)
  rw [value_standardTuple]
  refine Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ Fin.elim0 l) k) k
  · exact h0
  · exact h1

theorem membershipAtomicArguments_iff {n r args : V} (hn : n ∈ (ω : V)) :
    IsAtomicArguments membershipLanguageCode ∅ n r args ↔ IsMembershipAtomicArguments n r args := by
  constructor
  · rintro (⟨hr, ha⟩ | ⟨s, hs, hr, ha⟩)
    · exact ⟨Or.inl hr, membershipArguments_pair hn ha⟩
    · have hs2 : s ∈ (2 : V) := by simpa [membershipLanguageCode] using hs
      have har : (relationArities (membershipLanguageCode : V)) ‘ s = (2 : V) := by
        simp only [membershipLanguageCode, relationArities_code]
        exact value_constantGraph _ _ hs2
      rw [har] at ha
      refine ⟨Or.inr ?_, membershipArguments_pair hn ha⟩
      obtain ⟨k, rfl⟩ := (mem_natCast_iff s 2).mp hs2
      revert hr
      refine Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ Fin.elim0 l) k) k
      · intro hr; exact Or.inl hr
      · intro hr; exact Or.inr hr
  · rintro ⟨hr, i, hi, j, hj, rfl⟩
    have ha := boundPairArguments_valid hn hi hj
    rcases hr with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, ha⟩
    · have hr := membershipSymbol_valid (V := V) Language.Set.Rel.eq
      refine Or.inr ⟨0, hr.1, rfl, ?_⟩
      change boundPairArguments i j ∈ termSet membershipLanguageCode ∅ n ^
        ((relationArities membershipLanguageCode) ‘ (membershipSymbol Language.Set.Rel.eq))
      rw [hr.2]
      exact ha
    · have hr := membershipSymbol_valid (V := V) Language.Set.Rel.mem
      refine Or.inr ⟨1, hr.1, rfl, ?_⟩
      change boundPairArguments i j ∈ termSet membershipLanguageCode ∅ n ^
        ((relationArities membershipLanguageCode) ‘ (membershipSymbol Language.Set.Rel.mem))
      rw [hr.2]
      exact ha

end ZFVP
