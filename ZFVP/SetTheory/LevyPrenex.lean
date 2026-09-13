import ZFVP.SetTheory.StandardTruthMatrix

/-! Every positive Levy class admits a single leading quantifier over a matrix of the dual lower class. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def supportPiTruthFormula : SetTheorySemisentence 5 :=
  piOneMembershipTruthFormula.subst ![.bvar 1, .bvar 2, .bvar 3, .bvar 4]

def sigmaPrenexMatrix {n : ℕ} (k : ℕ) (φ : SetTheorySemisentence n) : SetTheorySemisentence (n + 1) :=
  match k with
  | 0 => standardTruthMatrix (correctDomainFormula 0) (boundedMembershipTruthCertificate true) φ
  | k + 1 => standardTruthMatrix (correctDomainFormula (k + 1)) supportPiTruthFormula φ

def piPrenexMatrix {n : ℕ} (k : ℕ) (φ : SetTheorySemisentence n) : SetTheorySemisentence (n + 1) :=
  ∼sigmaPrenexMatrix k (∼φ)

theorem sigmaPrenexMatrix_pi {n : ℕ} (k : ℕ) (φ : SetTheorySemisentence n) :
    IsPiFormula k (sigmaPrenexMatrix k φ) := by
  cases k with
  | zero => exact .bounded (standardTruthMatrix_bounded sequenceSupportFormula_bounded
      (boundedMembershipTruthCertificate_bounded true) φ)
  | succ k =>
    exact standardTruthMatrix_levy (correctDomainFormula_pi (k + 1))
      ((piOneMembershipTruthFormula_piOne.subst _).mono (by omega)) φ

theorem piPrenexMatrix_sigma {n : ℕ} (k : ℕ) (φ : SetTheorySemisentence n) :
    IsSigmaFormula k (piPrenexMatrix k φ) := (sigmaPrenexMatrix_pi k (∼φ)).neg

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem eval_supportPiTruthFormula (U A n φ b : V) :
    supportPiTruthFormula.Evalb ![U, A, n, φ, b] ↔ MembershipSatisfies A n φ b := by
  simp [supportPiTruthFormula]

theorem sigmaPrenexMatrix_domainTruth {n : ℕ} (k : ℕ) (φ : SetTheorySemisentence n) (v : Fin n → V) :
    (∃ U : V, (sigmaPrenexMatrix k φ).Evalb (U :> v)) ↔
      DomainSigmaTruth k (n : V) (encodeMembershipFormula φ) (standardTuple v) := by
  cases k with
  | zero =>
    simp only [sigmaPrenexMatrix, eval_standardTruthMatrix]
    constructor
    · rintro ⟨U, _, A, _, hA, hb, hc⟩
      have hs := (boundedMembershipTruthCertificate_exists true A (n : V)
        (encodeMembershipFormula φ) (standardTuple v)).mp ⟨U, hc⟩
      exact ⟨A, (eval_correctDomainFormula 0 A).mp hA, hb, hs.2.2⟩
    · rintro ⟨A, hA, hb, hs⟩
      obtain ⟨U, hc⟩ := (boundedMembershipTruthCertificate_exists true A (n : V)
        (encodeMembershipFormula φ) (standardTuple v)).mpr
          ⟨(membershipSatisfies_valid hs).1, hb, hs⟩
      have hc' := (eval_boundedMembershipTruthCertificate true U A (n : V)
        (encodeMembershipFormula φ) (standardTuple v)).mp hc
      exact ⟨U, hc'.1, A, hc'.2.1, (eval_correctDomainFormula 0 A).mpr hA, hb, hc⟩
  | succ k =>
    simp only [sigmaPrenexMatrix, eval_standardTruthMatrix, eval_correctDomainFormula,
      eval_supportPiTruthFormula]
    constructor
    · rintro ⟨_, _, A, _, hA, hb, hs⟩
      exact ⟨A, hA, hb, hs⟩
    · rintro ⟨A, hA, hb, hs⟩
      obtain ⟨U, hU, hAU⟩ := sequenceSupport_containing A
      exact ⟨U, hU, A, hAU, hA, hb, hs⟩

theorem sigmaPrenexMatrix_correct {n k : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsSigmaFormula (k + 1) φ) (v : Fin n → V) :
    (sigmaPrenexMatrix k φ).exs.Evalb v ↔ φ.Evalb v :=
  (sigmaPrenexMatrix_domainTruth k φ v).trans (domainSigmaTruth_correct k hφ v)

theorem piPrenexMatrix_correct {n k : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsPiFormula (k + 1) φ) (v : Fin n → V) :
    (piPrenexMatrix k φ).all.Evalb v ↔ φ.Evalb v := by
  have h := not_congr (sigmaPrenexMatrix_correct hφ.neg v)
  change (¬∃ U : V, (sigmaPrenexMatrix k (∼φ)).Evalb (U :> v)) ↔ (¬(∼φ).Evalb v) at h
  change (∀ U : V, (∼sigmaPrenexMatrix k (∼φ)).Evalb (U :> v)) ↔ φ.Evalb v
  simpa using h

theorem sigma_prenex_presentation {n k : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsSigmaFormula (k + 1) φ) :
    ∃ ψ : SetTheorySemisentence (n + 1), IsPiFormula k ψ ∧
      ∀ v : Fin n → V, ψ.exs.Evalb v ↔ φ.Evalb v :=
  ⟨sigmaPrenexMatrix k φ, sigmaPrenexMatrix_pi k φ, sigmaPrenexMatrix_correct hφ⟩

theorem pi_prenex_presentation {n k : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsPiFormula (k + 1) φ) :
    ∃ ψ : SetTheorySemisentence (n + 1), IsSigmaFormula k ψ ∧
      ∀ v : Fin n → V, ψ.all.Evalb v ↔ φ.Evalb v :=
  ⟨piPrenexMatrix k φ, piPrenexMatrix_sigma k φ, piPrenexMatrix_correct hφ⟩

end ZFVP
