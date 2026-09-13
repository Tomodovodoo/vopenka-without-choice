import ZFVP.ModelTheory.InternalHenkinTruthTable
import ZFVP.ModelTheory.InternalBinaryQuotientSemantics

/-! Standard formulas in the accepted table evaluate in the name prestructure.
The equality basis therefore supplies its internal setoid and congruence laws. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem membershipSemiterm_index {n : ℕ} (t : Semiterm ℒₛₑₜ Empty n) :
    ∃ i : Fin n, t = .bvar i := by
  cases t with
  | bvar i => exact ⟨i, rfl⟩
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

private theorem membershipTermPair_indices {n : ℕ} (ts : Fin 2 → Semiterm ℒₛₑₜ Empty n) :
    ∃ i j : Fin n, ts = ![.bvar i, .bvar j] := by
  obtain ⟨i, hi⟩ := membershipSemiterm_index (ts 0)
  obtain ⟨j, hj⟩ := membershipSemiterm_index (ts 1)
  refine ⟨i, j, funext fun k ↦ ?_⟩
  exact Fin.cases hi (fun k ↦ Fin.cases hj (fun l ↦ Fin.elim0 l) k) k

theorem IsCompleteHenkinSequence.name_encode_rel (hω : Schmerl.HasStandardOmega V) {T s : V}
    (hs : IsCompleteHenkinSequence T s) {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) (b : Fin n → SetDomain (ω : V)) :
    HenkinNameHolds T s (n : V) (encodeMembershipFormula (.rel r ts)) (standardTuple (fun i ↦ (b i).val)) ↔
      (.rel r ts : SetTheorySemisentence n).Evalb (s := internalNameStructure (ω : V)
        (henkinNameRelation T s (relationToken 0)) (henkinNameRelation T s (relationToken 1))) b := by
  have hb := standardTuple_mem_function (fun i ↦ (b i).val) (fun i ↦ (b i).property)
  cases r with
  | eq =>
    obtain ⟨i, j, rfl⟩ := membershipTermPair_indices ts
    change HenkinNameHolds T s (n : V) (atomCode (relationToken 0)
      (boundPairArguments (i.val : V) (j.val : V))) (standardTuple (fun l ↦ (b l).val)) ↔
      ⟨(b i).val, (b j).val⟩ₖ ∈ henkinNameRelation T s (relationToken 0)
    rw [hs.name_atom_pair_iff hω (by simp) hb (Or.inr (Or.inl rfl))
      (natCast_mem_of_lt i.isLt) (natCast_mem_of_lt j.isLt), value_standardTuple, value_standardTuple]
  | mem =>
    obtain ⟨i, j, rfl⟩ := membershipTermPair_indices ts
    change HenkinNameHolds T s (n : V) (atomCode (relationToken 1)
      (boundPairArguments (i.val : V) (j.val : V))) (standardTuple (fun l ↦ (b l).val)) ↔
      ⟨(b i).val, (b j).val⟩ₖ ∈ henkinNameRelation T s (relationToken 1)
    rw [hs.name_atom_pair_iff hω (by simp) hb (Or.inr (Or.inr rfl))
      (natCast_mem_of_lt i.isLt) (natCast_mem_of_lt j.isLt), value_standardTuple, value_standardTuple]

theorem henkinStages_name_encode_iff (hω : Schmerl.HasStandardOmega V) {T e : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V))
    (hrange : range e = formulaFamily (membershipLanguageCode : V) ∅)
    {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → SetDomain (ω : V)) :
    HenkinNameHolds T (henkinStages T e) (n : V) (encodeMembershipFormula φ) (standardTuple (fun i ↦ (b i).val)) ↔
      φ.Evalb (s := internalNameStructure (ω : V) (henkinNameRelation T (henkinStages T e) (relationToken 0))
        (henkinNameRelation T (henkinStages T e) (relationToken 1))) b := by
  have hs := henkinStages_complete hω hT he hrange
  let : Structure ℒₛₑₜ (SetDomain (ω : V)) := internalNameStructure (ω : V)
    (henkinNameRelation T (henkinStages T e) (relationToken 0)) (henkinNameRelation T (henkinStages T e) (relationToken 1))
  induction φ with
  | verum =>
    exact iff_of_true (hs.name_truth hω (by simp) (standardTuple_mem_function _ (fun i ↦ (b i).property))) trivial
  | falsum =>
    exact iff_of_false (hs.name_not_falsity hω (by simp) (standardTuple_mem_function _ (fun i ↦ (b i).property))) id
  | rel r ts => exact hs.name_encode_rel hω r ts b
  | @nrel n k r ts =>
    have hneg := hs.name_negate_iff hω (encodeMembershipFormula_mem (.rel r ts))
      (standardTuple_mem_function _ (fun i ↦ (b i).property))
    rw [← encodeMembershipFormula_neg] at hneg
    exact hneg.trans (not_congr (hs.name_encode_rel hω r ts b))
  | and φ ψ ihφ ihψ =>
    exact (hs.name_and_iff hω (encodeMembershipFormula_mem φ) (encodeMembershipFormula_mem ψ)
      (standardTuple_mem_function _ (fun i ↦ (b i).property))).trans (and_congr (ihφ b) (ihψ b))
  | or φ ψ ihφ ihψ =>
    exact (hs.name_or_iff hω (encodeMembershipFormula_mem φ) (encodeMembershipFormula_mem ψ)
      (standardTuple_mem_function _ (fun i ↦ (b i).property))).trans (or_congr (ihφ b) (ihψ b))
  | @all n φ ih =>
    have hφ : encodeMembershipFormula (V := V) φ ∈ formulaSet membershipLanguageCode ∅ (succ (n : V)) := by
      simpa only [num_succ_def] using encodeMembershipFormula_mem (V := V) φ
    change HenkinNameHolds T (henkinStages T e) (n : V) (allCode (encodeMembershipFormula φ))
      (standardTuple (fun i ↦ (b i).val)) ↔ _
    rw [henkinStages_name_all_iff hω hT he hrange (by simp) hφ
      (standardTuple_mem_function _ (fun i ↦ (b i).property))]
    change (∀ x ∈ (ω : V), _) ↔ ∀ x : SetDomain (ω : V), φ.Evalb _
    constructor
    · intro hh x
      apply (ih (x :> b)).mp
      simpa [standardTuple, num_succ_def] using hh x.val x.property
    · intro hh x hx
      let x' : SetDomain (ω : V) := ⟨x, hx⟩
      have hh' := (ih (x' :> b)).mpr (hh x')
      change HenkinNameHolds T (henkinStages T e) (succ (n : V)) (encodeMembershipFormula φ)
        (assignmentPrepend (n : V) (standardTuple (fun i ↦ (b i).val)) x'.val)
      simpa [standardTuple, num_succ_def] using hh'
  | @exs n φ ih =>
    have hφ : encodeMembershipFormula (V := V) φ ∈ formulaSet membershipLanguageCode ∅ (succ (n : V)) := by
      simpa only [num_succ_def] using encodeMembershipFormula_mem (V := V) φ
    change HenkinNameHolds T (henkinStages T e) (n : V) (existsCode (encodeMembershipFormula φ))
      (standardTuple (fun i ↦ (b i).val)) ↔ _
    rw [henkinStages_name_exists_iff hω hT he hrange (by simp) hφ
      (standardTuple_mem_function _ (fun i ↦ (b i).property))]
    change (∃ x ∈ (ω : V), _) ↔ ∃ x : SetDomain (ω : V), φ.Evalb _
    constructor
    · rintro ⟨x, hx, hh⟩
      let x' : SetDomain (ω : V) := ⟨x, hx⟩
      refine ⟨x', (ih (x' :> b)).mp ?_⟩
      change HenkinNameHolds T (henkinStages T e) (succ (n : V)) (encodeMembershipFormula φ)
        (assignmentPrepend (n : V) (standardTuple (fun i ↦ (b i).val)) x'.val) at hh
      simpa [standardTuple, num_succ_def] using hh
    · rintro ⟨x, hh⟩
      refine ⟨x.val, x.property, ?_⟩
      have hh' := (ih (x :> b)).mpr hh
      simpa [standardTuple, num_succ_def] using hh'

end ZFVP
