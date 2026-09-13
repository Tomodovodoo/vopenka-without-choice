import ZFVP.SetTheory.ForcingNameClasses

/-! Forcing constructors in the context P, R, Gamma, F, p, followed by names. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingSystemSubst {n m : ℕ} (φ : SetTheorySemisentence (n + 5))
    (P R Γ F p : SetTheorySemiterm Empty m) (v : Fin n → SetTheorySemiterm Empty m) : SetTheorySemisentence m :=
  φ.subst (P :> R :> Γ :> F :> p :> v)

def BoundedFormulaTree.levyForcingBase {n : ℕ} (φ : BoundedFormulaTree n) (pol : LevyPolarity) :
    SetTheorySemisentence (n + 5) :=
  (match pol with | .sigma => φ.forcingCertificate true | .pi => φ.forcingPi).subst
    (.bvar 0 :> .bvar 1 :> .bvar 4 :> forcingParameterTerms 5 rfl)

def levyForcingOrStep {n : ℕ} (φ ψ : SetTheorySemisentence (n + 5)) : SetTheorySemisentence (n + 5) :=
  (Semiformula.rel Language.Set.Rel.mem ![.bvar 4, .bvar 0]).and
    (boundedSetAll (.bvar 0) ((∼(boundedPairMemberFormula.subst ![.bvar 2, .bvar 0, .bvar 5])).or
      (boundedSetExs (.bvar 1) ((boundedPairMemberFormula.subst ![.bvar 3, .bvar 0, .bvar 1]).and
        ((forcingSystemSubst φ (.bvar 2) (.bvar 3) (.bvar 4) (.bvar 5) (.bvar 0) (forcingParameterTerms 7 rfl)).or
          (forcingSystemSubst ψ (.bvar 2) (.bvar 3) (.bvar 4) (.bvar 5) (.bvar 0) (forcingParameterTerms 7 rfl)))))))

def levyForcingAllStep {n : ℕ} (symmetric : Bool) (φ : SetTheorySemisentence (n + 1 + 5)) :
    SetTheorySemisentence (n + 5) :=
  (Semiformula.rel Language.Set.Rel.mem ![.bvar 4, .bvar 0]).and
    (.all ((∼((sigmaOneForcingNameClassFormula symmetric).subst ![.bvar 1, .bvar 3, .bvar 4, .bvar 0])).or
      (forcingSystemSubst φ (.bvar 1) (.bvar 2) (.bvar 3) (.bvar 4) (.bvar 5)
        (.bvar 0 :> forcingParameterTerms 6 rfl))))

def levyForcingExsStep {n : ℕ} (symmetric : Bool) (φ : SetTheorySemisentence (n + 1 + 5)) :
    SetTheorySemisentence (n + 5) :=
  (Semiformula.rel Language.Set.Rel.mem ![.bvar 4, .bvar 0]).and
    (boundedSetAll (.bvar 0) ((∼(boundedPairMemberFormula.subst ![.bvar 2, .bvar 0, .bvar 5])).or
      (boundedSetExs (.bvar 1) ((boundedPairMemberFormula.subst ![.bvar 3, .bvar 0, .bvar 1]).and
        (.exs (((sigmaOneForcingNameClassFormula symmetric).subst ![.bvar 3, .bvar 5, .bvar 6, .bvar 0]).and
          (forcingSystemSubst φ (.bvar 3) (.bvar 4) (.bvar 5) (.bvar 6) (.bvar 1)
            (.bvar 0 :> forcingParameterTerms 8 rfl))))))))

def levyForcingBoundedAllBody {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 1 + 5)) : SetTheorySemisentence (n + 6) :=
  (Semiformula.rel Language.Set.Rel.mem ![.bvar 5, .bvar 1]).and
    (boundedSetAll (.bvar 0) (boundedSetAll (.bvar 1)
      ((∼(boundedPairMemberFormula.subst ![Rew.subst (forcingParameterTerms 8 rfl) t, .bvar 1, .bvar 0])).or
        (boundedSetAll (.bvar 3) ((∼(boundedPairMemberFormula.subst ![.bvar 5, .bvar 0, .bvar 8])).or
          ((∼(boundedPairMemberFormula.subst ![.bvar 5, .bvar 0, .bvar 1])).or
            (forcingSystemSubst φ (.bvar 4) (.bvar 5) (.bvar 6) (.bvar 7) (.bvar 0)
              (.bvar 2 :> forcingParameterTerms 9 rfl))))))))

def levyForcingBoundedExsBody {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 1 + 5)) : SetTheorySemisentence (n + 6) :=
  (Semiformula.rel Language.Set.Rel.mem ![.bvar 5, .bvar 1]).and
    (boundedSetAll (.bvar 1) ((∼(boundedPairMemberFormula.subst ![.bvar 3, .bvar 0, .bvar 6])).or
      (boundedSetExs (.bvar 2) ((boundedPairMemberFormula.subst ![.bvar 4, .bvar 0, .bvar 1]).and
        (boundedSetExs (.bvar 2) (boundedSetExs (.bvar 3)
          ((boundedPairMemberFormula.subst ![Rew.subst (forcingParameterTerms 10 rfl) t, .bvar 1, .bvar 0]).and
            ((boundedPairMemberFormula.subst ![.bvar 6, .bvar 2, .bvar 0]).and
              (forcingSystemSubst φ (.bvar 5) (.bvar 6) (.bvar 7) (.bvar 8) (.bvar 2)
                (.bvar 1 :> forcingParameterTerms 10 rfl))))))))))

def forcingTransitiveGuard (n : ℕ) : SetTheorySemisentence (n + 6) :=
  (IsTransitive.dfn.subst ![.bvar 0]).and
    (finiteConjunction (fun i : Fin n ↦ .rel Language.Set.Rel.mem ![forcingParameterTerms 6 rfl i, .bvar 0]))

def forcingTransitiveBind {n : ℕ} (pol : LevyPolarity) (φ : SetTheorySemisentence (n + 6)) :
    SetTheorySemisentence (n + 5) :=
  match pol with
  | .sigma => .exs ((forcingTransitiveGuard n).and φ)
  | .pi => .all ((∼forcingTransitiveGuard n).or φ)

theorem forcingSystemSubst_levy {n m k : ℕ} {pol : LevyPolarity} {φ : SetTheorySemisentence (n + 5)}
    (h : IsLevyFormula pol k φ) (P R Γ F p : SetTheorySemiterm Empty m) (v : Fin n → SetTheorySemiterm Empty m) :
    IsLevyFormula pol k (forcingSystemSubst φ P R Γ F p v) := h.subst _

theorem BoundedFormulaTree.levyForcingBase_levy {n k : ℕ} (φ : BoundedFormulaTree n) (pol : LevyPolarity)
    (hk : 0 < k) : IsLevyFormula pol k (φ.levyForcingBase pol) := by
  cases pol
  · exact ((φ.forcingCertificate_sigmaOne true).subst _).mono hk
  · exact (φ.forcingPi_piOne.subst _).mono hk

theorem levyForcingOrStep_levy {n k : ℕ} {pol : LevyPolarity} {φ ψ : SetTheorySemisentence (n + 5)}
    (hφ : IsLevyFormula pol k φ) (hψ : IsLevyFormula pol k ψ) : IsLevyFormula pol k (levyForcingOrStep φ ψ) := by
  repeat' first
    | exact forcingSystemSubst_levy hφ _ _ _ _ _ _
    | exact forcingSystemSubst_levy hψ _ _ _ _ _ _
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _)
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _).neg
    | exact IsLevyFormula.bounded (.rel _ _)
    | apply IsLevyFormula.boundedAll
    | apply IsLevyFormula.boundedExs
    | apply IsLevyFormula.and
    | apply IsLevyFormula.or

theorem levyForcingAllStep_pi {n k : ℕ} (symmetric : Bool) {φ : SetTheorySemisentence (n + 1 + 5)}
    (hφ : IsPiFormula (k + 1) φ) : IsPiFormula (k + 1) (levyForcingAllStep symmetric φ) :=
  .and (.bounded (.rel _ _)) (.all (.or
    ((((sigmaOneForcingNameClassFormula_sigmaOne symmetric).subst _).neg).mono (by omega))
    (forcingSystemSubst_levy hφ _ _ _ _ _ _)))

theorem levyForcingExsStep_sigma {n k : ℕ} (symmetric : Bool) {φ : SetTheorySemisentence (n + 1 + 5)}
    (hφ : IsSigmaFormula (k + 1) φ) : IsSigmaFormula (k + 1) (levyForcingExsStep symmetric φ) :=
  .and (.bounded (.rel _ _)) (.boundedAll (.bvar 0)
    (.or (.bounded (boundedPairMemberFormula_bounded.subst _).neg)
      (.boundedExs (.bvar 1) (.and (.bounded (boundedPairMemberFormula_bounded.subst _))
        (.exs (.and (((sigmaOneForcingNameClassFormula_sigmaOne symmetric).subst _).mono (by omega))
          (forcingSystemSubst_levy hφ _ _ _ _ _ _)))))))

theorem levyForcingBoundedAllBody_levy {n k : ℕ} {pol : LevyPolarity} (t : SetTheorySemiterm Empty n)
    {φ : SetTheorySemisentence (n + 1 + 5)} (hφ : IsLevyFormula pol k φ) :
    IsLevyFormula pol k (levyForcingBoundedAllBody t φ) := by
  repeat' first
    | exact forcingSystemSubst_levy hφ _ _ _ _ _ _
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _).neg
    | exact IsLevyFormula.bounded (.rel _ _)
    | apply IsLevyFormula.boundedAll
    | apply IsLevyFormula.and
    | apply IsLevyFormula.or

theorem levyForcingBoundedExsBody_levy {n k : ℕ} {pol : LevyPolarity} (t : SetTheorySemiterm Empty n)
    {φ : SetTheorySemisentence (n + 1 + 5)} (hφ : IsLevyFormula pol k φ) :
    IsLevyFormula pol k (levyForcingBoundedExsBody t φ) := by
  repeat' first
    | exact forcingSystemSubst_levy hφ _ _ _ _ _ _
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _)
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _).neg
    | exact IsLevyFormula.bounded (.rel _ _)
    | apply IsLevyFormula.boundedAll
    | apply IsLevyFormula.boundedExs
    | apply IsLevyFormula.and
    | apply IsLevyFormula.or

theorem forcingTransitiveGuard_bounded (n : ℕ) : IsBoundedSetFormula (forcingTransitiveGuard n) :=
  .and (isTransitiveFormula_bounded.subst _) (finiteConjunction_bounded _ (fun _ ↦ .rel _ _))

theorem forcingTransitiveBind_levy {n k : ℕ} {pol : LevyPolarity} {φ : SetTheorySemisentence (n + 6)}
    (hk : 0 < k) (hφ : IsLevyFormula pol k φ) : IsLevyFormula pol k (forcingTransitiveBind pol φ) := by
  cases k with
  | zero => omega
  | succ k =>
    cases pol
    · exact .exs (.and (.bounded (forcingTransitiveGuard_bounded n)) hφ)
    · exact .all (.or (.bounded (forcingTransitiveGuard_bounded n).neg) hφ)

end ZFVP
