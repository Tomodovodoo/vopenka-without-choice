import ZFVP.SetTheory.CorrectRankComplexity

/-! Correctness expressed directly by the partial-truth predicates and internal codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def CodedSigmaCorrect (k : ℕ) (A : V) : Prop :=
  ∀ n φ, IsLevyFormulaCode .sigma (k + 1) n φ → ∀ b ∈ A ^ n,
    DomainSigmaTruth k n φ b ↔ MembershipSatisfies A n φ b

instance codedSigmaCorrect_definable (k : ℕ) : ℒₛₑₜ-predicate[V] (CodedSigmaCorrect k) := by
  unfold CodedSigmaCorrect
  definability

theorem CorrectDomain.codedSigmaCorrect {k : ℕ} {A : V} (h : CorrectDomain (k + 1) A) : CodedSigmaCorrect k A :=
  fun _ _ hφ _ hb ↦ h.sigmaTruth_iff hφ hb

theorem codedSigmaCorrect_lower {k : ℕ} {A : V} (h : CodedSigmaCorrect (k + 1) A) : CodedSigmaCorrect k A := by
  intro n φ hφ b hb
  exact (domainSigmaTruth_stable (Nat.le_succ k) hφ).trans (h n φ hφ.raise b hb)

theorem correctDomain_iff_codedSigmaCorrect (k : ℕ) {A : V} :
    CorrectDomain (k + 1) A ↔ IsSequenceSupport A ∧ CodedSigmaCorrect k A := by
  constructor
  · intro h
    exact ⟨h.support, h.codedSigmaCorrect⟩
  · rintro ⟨hs, hc⟩
    induction k with
    | zero => exact ⟨hs, fun n _ φ _ b _ hφ hb ↦ (hc n φ hφ b hb).mp⟩
    | succ k ih =>
      exact ⟨ih (codedSigmaCorrect_lower hc), fun n _ φ _ b _ hφ hb ↦ (hc n φ hφ b hb).mp⟩

theorem correctRankStage_codedSigmaCorrect (k : ℕ) (α : V) :
    IsCorrectRankStage (k + 1) α ↔
      IsOrdinal α ∧ IsSequenceSupport (hierarchy α) ∧ CodedSigmaCorrect k (hierarchy α) := by
  simp only [IsCorrectRankStage, correctDomain_iff_codedSigmaCorrect]

theorem correctRankStage_pi_absolute (k : ℕ) {δ : V} (hδ : IsCorrectRankStage (k + 2) δ)
    (α : SetDomain (hierarchy δ)) :
    (piCorrectRankStageFormula (k + 2)).Evalb ![α] ↔ IsCorrectRankStage (k + 2) α.val := by
  have hp := hδ.pi_correct (piCorrectRankStageFormula_pi (k := k + 2) (by omega)) ![α]
  have he : (fun i : Fin 1 ↦ (![α] i).val) = ![α.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [he] at hp
  exact hp.trans (eval_piCorrectRankStageFormula (k + 2) α.val)

end ZFVP
