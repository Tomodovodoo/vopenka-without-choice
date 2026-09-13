import ZFVP.SetTheory.DeltaOneAtomicForcing

/-! Sigma_1 constructors for both answers to bounded forcing tests.
The context is T, P, R, p, followed by the name parameters. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingParameterTerms {n m : ℕ} (k : ℕ) (h : n + k = m) : Fin n → SetTheorySemiterm Empty m :=
  fun i ↦ .bvar ⟨i.val + k, by omega⟩

def forcingContextSubst {n m : ℕ} (φ : SetTheorySemisentence (n + 4))
    (T P R p : SetTheorySemiterm Empty m) (v : Fin n → SetTheorySemiterm Empty m) : SetTheorySemisentence m :=
  φ.subst (T :> P :> R :> p :> v)

def forcingAtomicSigmaStep {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → SetTheorySemiterm Empty n) (answer : Bool) : SetTheorySemisentence (n + 4) :=
  match r with
  | .eq => (sigmaOneAtomicEqualityFormula answer).subst
      ![.bvar 1, .bvar 2, (Rew.subst (forcingParameterTerms 4 rfl) (ts 0)),
        (Rew.subst (forcingParameterTerms 4 rfl) (ts 1)), .bvar 3]
  | .mem => (sigmaOneAtomicMembershipFormula answer).subst
      ![.bvar 1, .bvar 2, (Rew.subst (forcingParameterTerms 4 rfl) (ts 0)),
        (Rew.subst (forcingParameterTerms 4 rfl) (ts 1)), .bvar 3]

def forcingNegationSigmaStep {n : ℕ} (φ : SetTheorySemisentence (n + 4))
    (answer : Bool) : SetTheorySemisentence (n + 4) :=
  if answer then
    (Semiformula.rel Language.Set.Rel.mem ![.bvar 3, .bvar 1]).and
      (boundedSetAll (.bvar 1) ((∼(boundedPairMemberFormula.subst ![.bvar 3, .bvar 0, .bvar 4])).or
        (forcingContextSubst φ (.bvar 1) (.bvar 2) (.bvar 3) (.bvar 0) (forcingParameterTerms 5 rfl))))
  else
    (Semiformula.nrel Language.Set.Rel.mem ![.bvar 3, .bvar 1]).or
      (boundedSetExs (.bvar 1) ((boundedPairMemberFormula.subst ![.bvar 3, .bvar 0, .bvar 4]).and
        (forcingContextSubst φ (.bvar 1) (.bvar 2) (.bvar 3) (.bvar 0) (forcingParameterTerms 5 rfl))))

def forcingAndSigmaStep {n : ℕ} (φ ψ : SetTheorySemisentence (n + 4))
    (answer : Bool) : SetTheorySemisentence (n + 4) :=
  if answer then φ.and ψ else φ.or ψ

def forcingOrSigmaStep {n : ℕ} (φ ψ : SetTheorySemisentence (n + 4))
    (answer : Bool) : SetTheorySemisentence (n + 4) :=
  if answer then
    (Semiformula.rel Language.Set.Rel.mem ![.bvar 3, .bvar 1]).and
      (boundedSetAll (.bvar 1) ((∼(boundedPairMemberFormula.subst ![.bvar 3, .bvar 0, .bvar 4])).or
        (boundedSetExs (.bvar 2) ((boundedPairMemberFormula.subst ![.bvar 4, .bvar 0, .bvar 1]).and
          ((forcingContextSubst φ (.bvar 2) (.bvar 3) (.bvar 4) (.bvar 0) (forcingParameterTerms 6 rfl)).or
            (forcingContextSubst ψ (.bvar 2) (.bvar 3) (.bvar 4) (.bvar 0) (forcingParameterTerms 6 rfl)))))))
  else
    (Semiformula.nrel Language.Set.Rel.mem ![.bvar 3, .bvar 1]).or
      (boundedSetExs (.bvar 1) ((boundedPairMemberFormula.subst ![.bvar 3, .bvar 0, .bvar 4]).and
        (boundedSetAll (.bvar 2) ((∼(boundedPairMemberFormula.subst ![.bvar 4, .bvar 0, .bvar 1])).or
          ((forcingContextSubst φ (.bvar 2) (.bvar 3) (.bvar 4) (.bvar 0) (forcingParameterTerms 6 rfl)).and
            (forcingContextSubst ψ (.bvar 2) (.bvar 3) (.bvar 4) (.bvar 0) (forcingParameterTerms 6 rfl)))))))

def forcingAllSigmaStep {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 1 + 4)) (answer : Bool) : SetTheorySemisentence (n + 4) :=
  if answer then
    (Semiformula.rel Language.Set.Rel.mem ![.bvar 3, .bvar 1]).and
      (boundedSetAll (.bvar 0) (boundedSetAll (.bvar 1)
        ((∼(boundedPairMemberFormula.subst ![(Rew.subst (forcingParameterTerms 6 rfl) t), .bvar 1, .bvar 0])).or
          (boundedSetAll (.bvar 3) ((∼(boundedPairMemberFormula.subst ![.bvar 5, .bvar 0, .bvar 6])).or
            ((∼(boundedPairMemberFormula.subst ![.bvar 5, .bvar 0, .bvar 1])).or
              (forcingContextSubst φ (.bvar 3) (.bvar 4) (.bvar 5) (.bvar 0)
                (.bvar 2 :> forcingParameterTerms 7 rfl))))))))
  else
    (Semiformula.nrel Language.Set.Rel.mem ![.bvar 3, .bvar 1]).or
      (boundedSetExs (.bvar 0) (boundedSetExs (.bvar 1)
        ((boundedPairMemberFormula.subst ![(Rew.subst (forcingParameterTerms 6 rfl) t), .bvar 1, .bvar 0]).and
          (boundedSetExs (.bvar 3) ((boundedPairMemberFormula.subst ![.bvar 5, .bvar 0, .bvar 6]).and
            ((boundedPairMemberFormula.subst ![.bvar 5, .bvar 0, .bvar 1]).and
              (forcingContextSubst φ (.bvar 3) (.bvar 4) (.bvar 5) (.bvar 0)
                (.bvar 2 :> forcingParameterTerms 7 rfl))))))))

def forcingExsSigmaStep {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 1 + 4)) (answer : Bool) : SetTheorySemisentence (n + 4) :=
  if answer then
    (Semiformula.rel Language.Set.Rel.mem ![.bvar 3, .bvar 1]).and
      (boundedSetAll (.bvar 1) ((∼(boundedPairMemberFormula.subst ![.bvar 3, .bvar 0, .bvar 4])).or
        (boundedSetExs (.bvar 2) ((boundedPairMemberFormula.subst ![.bvar 4, .bvar 0, .bvar 1]).and
          (boundedSetExs (.bvar 2) (boundedSetExs (.bvar 3)
            ((boundedPairMemberFormula.subst ![(Rew.subst (forcingParameterTerms 8 rfl) t), .bvar 1, .bvar 0]).and
              ((boundedPairMemberFormula.subst ![.bvar 6, .bvar 2, .bvar 0]).and
                (forcingContextSubst φ (.bvar 4) (.bvar 5) (.bvar 6) (.bvar 2)
                  (.bvar 1 :> forcingParameterTerms 8 rfl))))))))))
  else
    (Semiformula.nrel Language.Set.Rel.mem ![.bvar 3, .bvar 1]).or
      (boundedSetExs (.bvar 1) ((boundedPairMemberFormula.subst ![.bvar 3, .bvar 0, .bvar 4]).and
        (boundedSetAll (.bvar 2) ((∼(boundedPairMemberFormula.subst ![.bvar 4, .bvar 0, .bvar 1])).or
          (boundedSetAll (.bvar 2) (boundedSetAll (.bvar 3)
            ((∼(boundedPairMemberFormula.subst ![(Rew.subst (forcingParameterTerms 8 rfl) t), .bvar 1, .bvar 0])).or
              ((∼(boundedPairMemberFormula.subst ![.bvar 6, .bvar 2, .bvar 0])).or
                (forcingContextSubst φ (.bvar 4) (.bvar 5) (.bvar 6) (.bvar 2)
                  (.bvar 1 :> forcingParameterTerms 8 rfl))))))))))

theorem forcingContextSubst_sigma {n m k : ℕ} {φ : SetTheorySemisentence (n + 4)}
    (h : IsSigmaFormula k φ) (T P R p : SetTheorySemiterm Empty m) (v : Fin n → SetTheorySemiterm Empty m) :
    IsSigmaFormula k (forcingContextSubst φ T P R p v) := h.subst _

theorem forcingAtomicSigmaStep_sigmaOne {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → SetTheorySemiterm Empty n) (answer : Bool) : IsSigmaFormula 1 (forcingAtomicSigmaStep r ts answer) := by
  cases r
  · exact (sigmaOneAtomicEqualityFormula_sigmaOne answer).subst _
  · exact (sigmaOneAtomicMembershipFormula_sigmaOne answer).subst _

theorem forcingNegationSigmaStep_sigmaOne {n : ℕ} {φ : SetTheorySemisentence (n + 4)}
    (hφ : IsSigmaFormula 1 φ) (answer : Bool) : IsSigmaFormula 1 (forcingNegationSigmaStep φ answer) := by
  cases answer <;> simp only [forcingNegationSigmaStep, Bool.false_eq_true, reduceIte]
  all_goals repeat' first
    | exact forcingContextSubst_sigma hφ _ _ _ _ _
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _)
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _).neg
    | exact IsLevyFormula.bounded (.rel _ _)
    | exact IsLevyFormula.bounded (.nrel _ _)
    | apply IsLevyFormula.boundedAll
    | apply IsLevyFormula.boundedExs
    | apply IsLevyFormula.and
    | apply IsLevyFormula.or

theorem forcingAndSigmaStep_sigmaOne {n : ℕ} {φ ψ : SetTheorySemisentence (n + 4)}
    (hφ : IsSigmaFormula 1 φ) (hψ : IsSigmaFormula 1 ψ) (answer : Bool) : IsSigmaFormula 1 (forcingAndSigmaStep φ ψ answer) := by
  cases answer
  · exact .or hφ hψ
  · exact .and hφ hψ

theorem forcingOrSigmaStep_sigmaOne {n : ℕ} {φ ψ : SetTheorySemisentence (n + 4)}
    (hφ : IsSigmaFormula 1 φ) (hψ : IsSigmaFormula 1 ψ) (answer : Bool) : IsSigmaFormula 1 (forcingOrSigmaStep φ ψ answer) := by
  cases answer <;> simp only [forcingOrSigmaStep, Bool.false_eq_true, reduceIte]
  all_goals repeat' first
    | exact forcingContextSubst_sigma hφ _ _ _ _ _
    | exact forcingContextSubst_sigma hψ _ _ _ _ _
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _)
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _).neg
    | exact IsLevyFormula.bounded (.rel _ _)
    | exact IsLevyFormula.bounded (.nrel _ _)
    | apply IsLevyFormula.boundedAll
    | apply IsLevyFormula.boundedExs
    | apply IsLevyFormula.and
    | apply IsLevyFormula.or

theorem forcingAllSigmaStep_sigmaOne {n : ℕ} (t : SetTheorySemiterm Empty n)
    {φ : SetTheorySemisentence (n + 1 + 4)} (hφ : IsSigmaFormula 1 φ) (answer : Bool) :
    IsSigmaFormula 1 (forcingAllSigmaStep t φ answer) := by
  cases answer <;> simp only [forcingAllSigmaStep, Bool.false_eq_true, reduceIte]
  all_goals repeat' first
    | exact forcingContextSubst_sigma hφ _ _ _ _ _
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _)
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _).neg
    | exact IsLevyFormula.bounded (.rel _ _)
    | exact IsLevyFormula.bounded (.nrel _ _)
    | apply IsLevyFormula.boundedAll
    | apply IsLevyFormula.boundedExs
    | apply IsLevyFormula.and
    | apply IsLevyFormula.or

theorem forcingExsSigmaStep_sigmaOne {n : ℕ} (t : SetTheorySemiterm Empty n)
    {φ : SetTheorySemisentence (n + 1 + 4)} (hφ : IsSigmaFormula 1 φ) (answer : Bool) :
    IsSigmaFormula 1 (forcingExsSigmaStep t φ answer) := by
  cases answer <;> simp only [forcingExsSigmaStep, Bool.false_eq_true, reduceIte]
  all_goals repeat' first
    | exact forcingContextSubst_sigma hφ _ _ _ _ _
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _)
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _).neg
    | exact IsLevyFormula.bounded (.rel _ _)
    | exact IsLevyFormula.bounded (.nrel _ _)
    | apply IsLevyFormula.boundedAll
    | apply IsLevyFormula.boundedExs
    | apply IsLevyFormula.and
    | apply IsLevyFormula.or

end ZFVP
