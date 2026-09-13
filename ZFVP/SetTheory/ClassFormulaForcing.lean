import ZFVP.SetTheory.ForcingAtoms

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def classForcingFormulaData (P R : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N) :
    {n : ℕ} → SetTheorySemisentence n → {F : V → V // ℒₛₑₜ-function₁ F}
  | _, .verum => ⟨fun _ ↦ P, by definability⟩
  | _, .falsum => ⟨fun _ ↦ ∅, by definability⟩
  | _, .rel r ts => ⟨forcingAtomic P R r ts, by definability⟩
  | _, .nrel r ts => ⟨fun b ↦ forcingNegation P R (forcingAtomic P R r ts b), by definability⟩
  | _, .and φ ψ => by
      let f := classForcingFormulaData P R N hN φ
      let g := classForcingFormulaData P R N hN ψ
      have hf := f.property
      have hg := g.property
      exact ⟨fun b ↦ f.val b ∩ g.val b, by definability⟩
  | _, .or φ ψ => by
      let f := classForcingFormulaData P R N hN φ
      let g := classForcingFormulaData P R N hN ψ
      have hf := f.property
      have hg := g.property
      exact ⟨fun b ↦ forcingClosure P R (f.val b ∪ g.val b), by definability⟩
  | n, .all φ => by
      let f := classForcingFormulaData P R N hN φ
      have hf := f.property
      refine ⟨fun b ↦ forcingClassIntersection P N hN
        (fun x ↦ f.val (assignmentPrepend (n : V) b x)) (by definability), ?_⟩
      have h : ℒₛₑₜ-relation (fun C b : V ↦ ∀ p, p ∈ C ↔ p ∈ P ∧
          ∀ x, N x → p ∈ f.val (assignmentPrepend (n : V) b x)) := by definability
      apply Language.Definable.of_iff h
      intro v
      change v 0 = forcingClassIntersection P N _ _ _ ↔ _
      rw [mem_ext_iff]
      simp [mem_forcingClassIntersection_iff]
  | n, .exs φ => by
      let f := classForcingFormulaData P R N hN φ
      have hf := f.property
      refine ⟨fun b ↦ forcingExistential P R N hN
        (fun x ↦ f.val (assignmentPrepend (n : V) b x)) (by definability), ?_⟩
      have h : ℒₛₑₜ-function₁ (fun b : V ↦ forcingClassUnion P N hN
          (fun x ↦ f.val (assignmentPrepend (n : V) b x)) (by definability)) := by
        have hh : ℒₛₑₜ-relation (fun C b : V ↦ ∀ p, p ∈ C ↔ p ∈ P ∧
            ∃ x, N x ∧ p ∈ f.val (assignmentPrepend (n : V) b x)) := by definability
        apply Language.Definable.of_iff hh
        intro v
        change v 0 = forcingClassUnion P N _ _ _ ↔ _
        rw [mem_ext_iff]
        simp [mem_forcingClassUnion_iff]
      unfold forcingExistential
      definability

noncomputable def classForcingFormula (P R : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N) {n : ℕ} (φ : SetTheorySemisentence n) : V → V :=
  (classForcingFormulaData P R N hN φ).val

instance classForcingFormula_definable (P R : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N) {n : ℕ} (φ : SetTheorySemisentence n) :
    ℒₛₑₜ-function₁[V] (classForcingFormula P R N hN φ) := (classForcingFormulaData P R N hN φ).property

theorem classForcingFormula_verum (P R b : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N) (n : ℕ) : classForcingFormula P R N hN (.verum : SetTheorySemisentence n) b = P := rfl

theorem classForcingFormula_falsum (P R b : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N) (n : ℕ) : classForcingFormula P R N hN (.falsum : SetTheorySemisentence n) b = ∅ := rfl

theorem classForcingFormula_rel (P R b : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N) {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) : classForcingFormula P R N hN (.rel r ts) b = forcingAtomic P R r ts b := rfl

theorem classForcingFormula_nrel (P R b : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N) {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) :
    classForcingFormula P R N hN (.nrel r ts) b = forcingNegation P R (forcingAtomic P R r ts b) := rfl

theorem classForcingFormula_and (P R b : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N) {n : ℕ} (φ ψ : SetTheorySemisentence n) :
    classForcingFormula P R N hN (.and φ ψ) b = classForcingFormula P R N hN φ b ∩ classForcingFormula P R N hN ψ b := rfl

theorem classForcingFormula_or (P R b : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N) {n : ℕ} (φ ψ : SetTheorySemisentence n) :
    classForcingFormula P R N hN (.or φ ψ) b = forcingClosure P R (classForcingFormula P R N hN φ b ∪ classForcingFormula P R N hN ψ b) := rfl

theorem classForcingFormula_all (P R b : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N) {n : ℕ} (φ : SetTheorySemisentence (n + 1)) :
    classForcingFormula P R N hN (.all φ) b = forcingClassIntersection P N hN
      (fun x ↦ classForcingFormula P R N hN φ (assignmentPrepend (n : V) b x)) (by definability) := rfl

theorem classForcingFormula_exs (P R b : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N) {n : ℕ} (φ : SetTheorySemisentence (n + 1)) :
    classForcingFormula P R N hN (.exs φ) b = forcingExistential P R N hN
      (fun x ↦ classForcingFormula P R N hN φ (assignmentPrepend (n : V) b x)) (by definability) := rfl

theorem classForcingFormula_regular {P R : V} (N : V → Prop) (hN : ℒₛₑₜ-predicate N) (hR : IsForcingPreorder P R) {n : ℕ}
    (φ : SetTheorySemisentence n) (b : V) : IsForcingRegular P R (classForcingFormula P R N hN φ b) := by
  induction φ generalizing b with
  | verum => exact forcingRegular_top P R
  | falsum => exact forcingRegular_empty hR
  | rel r ts => exact forcingAtomic_regular hR r ts b
  | nrel r ts => exact forcingNegation_regular hR (forcingAtomic_regular hR r ts b).2.1
  | and φ ψ ihφ ihψ => exact forcingRegular_inter (ihφ b) (ihψ b)
  | or φ ψ ihφ ihψ =>
    apply forcingClosure_regular hR
    intro p hp
    rcases mem_union_iff.mp hp with hφ | hψ
    · exact (ihφ b).1 p hφ
    · exact (ihψ b).1 p hψ
  | all φ ih =>
    rw [classForcingFormula_all]
    apply forcingClassIntersection_regular
    intro x _
    exact ih _
  | exs φ _ =>
    rw [classForcingFormula_exs]
    apply forcingExistential_regular hR

end ZFVP
