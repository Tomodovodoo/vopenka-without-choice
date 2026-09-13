import ZFVP.SetTheory.ExactLowTruth
import ZFVP.Syntax.DeltaOneLevyCodes

/-! A recursive family of set domains and the associated partial-truth formulas.
The domain conditions record downward truth preservation at preceding levels. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def domainSigmaTruthFormula (D : SetTheorySemisentence 1) : SetTheorySemisentence 3 :=
  “n φ b. ∃ A, !D A ∧ !boundedFunctionFormula b n A ∧
    !(sigmaOneMembershipModelTruthFormula true) A n φ b”

def domainPiTruthFormula (D : SetTheorySemisentence 1) : SetTheorySemisentence 3 :=
  “n φ b. ∀ A, !D A → !boundedFunctionFormula b n A → !piOneMembershipTruthFormula A n φ b”

def correctDomainFormula : ℕ → SetTheorySemisentence 1
  | 0 => sequenceSupportFormula
  | k + 1 => “A. !(correctDomainFormula k) A ∧ ∀ n ∈ A, ∀ φ ∈ A, ∀ b ∈ A,
      !(sigmaOneLevyCodeFormula .sigma (k + 1)) n φ → !boundedFunctionFormula b n A →
      !(domainSigmaTruthFormula (correctDomainFormula k)) n φ b → !piOneMembershipTruthFormula A n φ b”

theorem domainSigmaTruthFormula_sigma {k : ℕ} {D : SetTheorySemisentence 1}
    (hD : IsLevyFormula .pi k D) : IsLevyFormula .sigma (k + 1) (domainSigmaTruthFormula D) :=
  .exs (.and (.raise (hD.subst _)) (.and (.bounded (boundedFunctionFormula_bounded.subst _))
    (((sigmaOneMembershipModelTruthFormula_sigmaOne true).mono (Nat.succ_le_succ (Nat.zero_le k))).subst _)))

theorem domainPiTruthFormula_pi {k : ℕ} {D : SetTheorySemisentence 1}
    (hD : IsLevyFormula .pi k D) : IsLevyFormula .pi (k + 1) (domainPiTruthFormula D) :=
  .all (.or (.raise (hD.subst _).neg) (.or (.bounded (boundedFunctionFormula_bounded.subst _).neg)
    ((piOneMembershipTruthFormula_piOne.mono (Nat.succ_le_succ (Nat.zero_le k))).subst _)))

theorem correctDomainFormula_pi (k : ℕ) : IsLevyFormula .pi k (correctDomainFormula k) := by
  induction k with
  | zero => exact .bounded sequenceSupportFormula_bounded
  | succ k ih =>
    refine .and (ih.mono (Nat.le_succ k) |>.subst _) (.boundedAll (.bvar 0)
      (.boundedAll (.bvar 1) (.boundedAll (.bvar 2) ?_)))
    exact .or (((sigmaOneLevyCodeFormula_sigmaOne .sigma (k + 1)).mono
      (Nat.succ_le_succ (Nat.zero_le k))).subst _).neg
      (.or (.bounded (boundedFunctionFormula_bounded.subst _).neg)
        (.or ((domainSigmaTruthFormula_sigma ih).subst _).neg
          ((piOneMembershipTruthFormula_piOne.mono (Nat.succ_le_succ (Nat.zero_le k))).subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def CorrectDomain : ℕ → V → Prop
  | 0, A => IsSequenceSupport A
  | k + 1, A => CorrectDomain k A ∧ ∀ n ∈ A, ∀ φ ∈ A, ∀ b ∈ A,
      IsLevyFormulaCode .sigma (k + 1) n φ → b ∈ A ^ n →
      (∃ B, CorrectDomain k B ∧ b ∈ B ^ n ∧ MembershipSatisfies B n φ b) → MembershipSatisfies A n φ b

def DomainSigmaTruth (k : ℕ) (n φ b : V) : Prop :=
  ∃ A, CorrectDomain k A ∧ b ∈ A ^ n ∧ MembershipSatisfies A n φ b

def DomainPiTruth (k : ℕ) (n φ b : V) : Prop :=
  ∀ A, CorrectDomain k A → b ∈ A ^ n → MembershipSatisfies A n φ b

theorem eval_domainSigmaTruthFormula_body (D : SetTheorySemisentence 1) (n φ b : V) :
    (domainSigmaTruthFormula D).Evalb ![n, φ, b] ↔
      ∃ A, D.Evalb ![A] ∧ b ∈ A ^ n ∧ MembershipSatisfies A n φ b := by
  simp [domainSigmaTruthFormula]

theorem eval_correctDomainFormula (k : ℕ) (A : V) :
    (correctDomainFormula k).Evalb ![A] ↔ CorrectDomain k A := by
  induction k generalizing A with
  | zero => simp [correctDomainFormula, CorrectDomain]
  | succ k ih =>
    simp [correctDomainFormula, CorrectDomain, eval_domainSigmaTruthFormula_body, ih,
      Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]

instance correctDomainFormula_defined (k : ℕ) :
    ℒₛₑₜ-predicate[V] (CorrectDomain k) via correctDomainFormula k :=
  ⟨fun (v : Fin 1 → V) ↦ by
    have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    change (correctDomainFormula k).Evalb v ↔ CorrectDomain k (v 0)
    rw [← hv]
    exact eval_correctDomainFormula k (v 0)⟩

instance correctDomain_definable (k : ℕ) : ℒₛₑₜ-predicate[V] (CorrectDomain k) :=
  (correctDomainFormula_defined k).to_definable

theorem eval_domainSigmaTruthFormula (k : ℕ) (n φ b : V) :
    (domainSigmaTruthFormula (correctDomainFormula k)).Evalb ![n, φ, b] ↔ DomainSigmaTruth k n φ b := by
  simp [domainSigmaTruthFormula, DomainSigmaTruth]

theorem eval_domainPiTruthFormula (k : ℕ) (n φ b : V) :
    (domainPiTruthFormula (correctDomainFormula k)).Evalb ![n, φ, b] ↔ DomainPiTruth k n φ b := by
  simp [domainPiTruthFormula, DomainPiTruth]

instance domainSigmaTruth_definable (k : ℕ) : ℒₛₑₜ-relation₃[V] (DomainSigmaTruth k) := by
  unfold DomainSigmaTruth
  definability

instance domainPiTruth_definable (k : ℕ) : ℒₛₑₜ-relation₃[V] (DomainPiTruth k) := by
  unfold DomainPiTruth
  definability

theorem CorrectDomain.lower {k : ℕ} {A : V} (h : CorrectDomain (k + 1) A) : CorrectDomain k A := h.1

theorem CorrectDomain.support {k : ℕ} {A : V} (h : CorrectDomain k A) : IsSequenceSupport A := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih h.1

theorem CorrectDomain.nonempty {k : ℕ} {A : V} (h : CorrectDomain k A) : IsNonempty A :=
  ⟨⟨ω, h.support.omega_mem⟩⟩

theorem CorrectDomain.sigmaTruth_iff {k : ℕ} {A n φ b : V} (hA : CorrectDomain (k + 1) A)
    (hφ : IsLevyFormulaCode .sigma (k + 1) n φ) (hb : b ∈ A ^ n) :
    DomainSigmaTruth k n φ b ↔ MembershipSatisfies A n φ b := by
  let := hA.support
  have hnA : n ∈ A := IsCodingSupport.natural_mem hφ.context
  have hφA := (kpair_components_mem_transitive (levyFormulaFamily_subset_support (k + 1) .sigma A _ hφ)).2
  have hbA := function_mem_sequenceSupport (fun _ h ↦ h) hφ.context hb
  exact ⟨hA.2 n hnA φ hφA b hbA hφ hb, fun hs ↦ ⟨A, hA.1, hb, hs⟩⟩

end ZFVP
