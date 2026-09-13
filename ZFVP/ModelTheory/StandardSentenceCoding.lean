import ZFVP.ModelTheory.FoundationDerivationCoding

/-! Closing parameter contexts and importing sentence axioms into finite coded proofs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem shiftCodedSequent_empty (n : V) : shiftCodedSequent n (∅ : V) = ∅ := by
  apply mem_ext
  intro φ
  simp [shiftCodedSequent, mem_renameCodedSequent_iff]

theorem StandardCodedProvable.lift_sentence {T : V} {φ : SetTheorySentence}
    (h : StandardCodedProvable T 0 {encodeMembershipFormula φ}) (k : ℕ) :
    StandardCodedProvable T (((k + 1 : ℕ) : V))
      {encodeMembershipFormula (finiteVariableClosure k (φ : SetTheoryProposition))} := by
  let σ : Rew ℒₛₑₜ Empty 0 Empty (k + 1) := Rew.bind Fin.elim0 Empty.elim
  have hzero : ((0 : ℕ) : V) = (0 : V) := rfl
  have hr : (∅ : V) ∈ ((k + 1 : ℕ) : V) ^ ((0 : ℕ) : V) := by simp [mem_function_iff, zero_def]
  have he := encodeClosedSequent_rename hr Fin.elim0 (fun i ↦ Fin.elim0 i) σ (fun i ↦ Fin.elim0 i) [φ]
  have he' : renameCodedSequent (0 : V) (((k + 1 : ℕ) : V)) ∅ {encodeMembershipFormula φ} =
      encodeClosedSequent [σ ▹ φ] := by
    simpa only [List.map_cons, List.map_nil, encodeClosedSequent_cons, encodeClosedSequent_nil,
      SetTheory.insert_empty_eq, hzero] using he
  have hv : IsCodedSequent (((k + 1 : ℕ) : V))
      (renameCodedSequent 0 (((k + 1 : ℕ) : V)) ∅ {encodeMembershipFormula φ}) := by
    rw [he']
    exact encodeClosedSequent_valid _
  have hp := h.rename hv hr
  rw [he'] at hp
  simpa only [encodeClosedSequent_cons, encodeClosedSequent_nil, SetTheory.insert_empty_eq,
    finiteVariableClosure_embed k φ σ] using hp

theorem StandardCodedProvable.allClosure {T : V} {n : ℕ} {φ : SetTheorySemisentence n}
    (h : StandardCodedProvable T (n : V) {encodeMembershipFormula φ}) :
    StandardCodedProvable T 0 {encodeMembershipFormula (∀¹* φ)} := by
  induction n with
  | zero => exact h
  | succ n ih =>
    apply ih (φ := ∀¹ φ)
    have hp : StandardCodedProvable T (succ (n : V))
        (insert (encodeMembershipFormula φ) (shiftCodedSequent (n : V) ∅)) := by
      simpa only [shiftCodedSequent_empty, SetTheory.insert_empty_eq, num_succ_def] using h
    have hv := encodeClosedSequent_valid (V := V) [∀¹ φ]
    have ho := hp.all (by simpa only [encodeClosedSequent_cons, encodeClosedSequent_nil,
      encodeMembershipFormula_all] using hv) (by simp) (by
        simpa only [num_succ_def] using encodeMembershipFormula_mem (V := V) φ)
    simpa only [encodeMembershipFormula_all, SetTheory.insert_empty_eq] using ho

theorem StandardCodedProvable.refutation_zero {T : V} {φ : SetTheorySemisentence 1}
    (h : StandardCodedProvable T 1 ∅)
    (hax : StandardCodedProvable T 0 {encodeMembershipFormula (∃¹ φ)}) :
    StandardCodedProvable T 0 ∅ := by
  have hone : ((1 : ℕ) : V) = (1 : V) := rfl
  have hzero : ((0 : ℕ) : V) = (0 : V) := rfl
  have hp : StandardCodedProvable T 1 {encodeMembershipFormula (∼φ)} :=
    h.weaken (by simpa only [encodeClosedSequent_cons, encodeClosedSequent_nil, SetTheory.insert_empty_eq, hone]
      using encodeClosedSequent_valid (V := V) [∼φ]) (by simp)
  have hn := hp.allClosure
  have hn' : StandardCodedProvable T 0
      (insert (negateFormula membershipLanguageCode ∅ 0 (encodeMembershipFormula (∃¹ φ))) ∅) := by
    have he : encodeMembershipFormula (V := V) (∼(∃¹ φ)) =
        negateFormula membershipLanguageCode ∅ 0 (encodeMembershipFormula (∃¹ φ)) := by
      simpa only [hzero] using encodeMembershipFormula_neg (V := V) (∃¹ φ)
    rw [SetTheory.insert_empty_eq, ← he]
    exact hn
  have hv : IsCodedSequent (0 : V) (∅ ∪ ∅ : V) := by
    simpa using encodeClosedSequent_valid (V := V) ([] : List SetTheorySentence)
  have hp' : StandardCodedProvable T 0 (insert (encodeMembershipFormula (∃¹ φ)) ∅) := by
    simpa only [SetTheory.insert_empty_eq] using hax
  simpa using hp'.cut hn' hv (encodeMembershipFormula_mem (∃¹ φ))

end ZFVP
