import ZFVP.Syntax.BoundedForcingSteps
import ZFVP.SetTheory.ForcingFormulaWitnesses

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def setForcingSubst {n m : ℕ} (φ : SetTheorySemisentence (n + 6))
    (T P R D H p : SetTheorySemiterm Empty m) (v : Fin n → SetTheorySemiterm Empty m) :
    SetTheorySemisentence m := φ.subst (T :> P :> R :> D :> H :> p :> v)

def setForcingAtomic {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → SetTheorySemiterm Empty n) : SetTheorySemisentence (n + 6) :=
  match r with
  | .eq => boundedAtomicEqualityEntryFormula.subst
      ![.bvar 0, .bvar 1, .bvar 2, .bvar 4,
        Rew.subst (forcingParameterTerms 6 rfl) (ts 0),
        Rew.subst (forcingParameterTerms 6 rfl) (ts 1), .bvar 5]
  | .mem => boundedAtomicMembershipFormula.subst
      ![.bvar 0, .bvar 1, .bvar 2, .bvar 4,
        Rew.subst (forcingParameterTerms 6 rfl) (ts 0),
        Rew.subst (forcingParameterTerms 6 rfl) (ts 1), .bvar 5]

def setForcingNegation {n : ℕ} (φ : SetTheorySemisentence (n + 6)) :
    SetTheorySemisentence (n + 6) :=
  (Semiformula.rel Language.Set.Rel.mem ![.bvar 5, .bvar 1]).and
    (boundedSetAll (.bvar 1) ((∼(boundedPairMemberFormula.subst ![.bvar 3, .bvar 0, .bvar 6])).or
      (∼setForcingSubst φ (.bvar 1) (.bvar 2) (.bvar 3) (.bvar 4) (.bvar 5) (.bvar 0)
        (forcingParameterTerms 7 rfl))))

def setForcingDisjunction {n : ℕ} (φ ψ : SetTheorySemisentence (n + 6)) :
    SetTheorySemisentence (n + 6) :=
  (Semiformula.rel Language.Set.Rel.mem ![.bvar 5, .bvar 1]).and
    (boundedSetAll (.bvar 1) ((∼(boundedPairMemberFormula.subst ![.bvar 3, .bvar 0, .bvar 6])).or
      (boundedSetExs (.bvar 2) ((boundedPairMemberFormula.subst ![.bvar 4, .bvar 0, .bvar 1]).and
        ((setForcingSubst φ (.bvar 2) (.bvar 3) (.bvar 4) (.bvar 5) (.bvar 6) (.bvar 0)
          (forcingParameterTerms 8 rfl)).or
        (setForcingSubst ψ (.bvar 2) (.bvar 3) (.bvar 4) (.bvar 5) (.bvar 6) (.bvar 0)
          (forcingParameterTerms 8 rfl)))))))

def setForcingUniversal {n : ℕ} (φ : SetTheorySemisentence (n + 1 + 6)) :
    SetTheorySemisentence (n + 6) :=
  (Semiformula.rel Language.Set.Rel.mem ![.bvar 5, .bvar 1]).and
    (boundedSetAll (.bvar 3)
      (setForcingSubst φ (.bvar 1) (.bvar 2) (.bvar 3) (.bvar 4) (.bvar 5) (.bvar 6)
        (.bvar 0 :> forcingParameterTerms 7 rfl)))

def setForcingExistential {n : ℕ} (φ : SetTheorySemisentence (n + 1 + 6)) :
    SetTheorySemisentence (n + 6) :=
  (Semiformula.rel Language.Set.Rel.mem ![.bvar 5, .bvar 1]).and
    (boundedSetAll (.bvar 1) ((∼(boundedPairMemberFormula.subst ![.bvar 3, .bvar 0, .bvar 6])).or
      (boundedSetExs (.bvar 2) ((boundedPairMemberFormula.subst ![.bvar 4, .bvar 0, .bvar 1]).and
        (boundedSetExs (.bvar 5)
          (setForcingSubst φ (.bvar 3) (.bvar 4) (.bvar 5) (.bvar 6) (.bvar 7) (.bvar 1)
            (.bvar 0 :> forcingParameterTerms 9 rfl)))))))

def boundedSetForcingTranslation : {n : ℕ} → SetTheorySemisentence n → SetTheorySemisentence (n + 6)
  | _, .verum => .rel Language.Set.Rel.mem ![.bvar 5, .bvar 1]
  | _, .falsum => .falsum
  | _, .rel r ts => setForcingAtomic r ts
  | _, .nrel r ts => setForcingNegation (setForcingAtomic r ts)
  | _, .and φ ψ => (boundedSetForcingTranslation φ).and (boundedSetForcingTranslation ψ)
  | _, .or φ ψ => setForcingDisjunction (boundedSetForcingTranslation φ) (boundedSetForcingTranslation ψ)
  | _, .all φ => setForcingUniversal (boundedSetForcingTranslation φ)
  | _, .exs φ => setForcingExistential (boundedSetForcingTranslation φ)

theorem setForcingAtomic_bounded {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → SetTheorySemiterm Empty n) : IsBoundedSetFormula (setForcingAtomic r ts) := by
  cases r
  · exact boundedAtomicEqualityEntryFormula_bounded.subst _
  · exact boundedAtomicMembershipFormula_bounded.subst _

theorem setForcingNegation_bounded {n : ℕ} {φ : SetTheorySemisentence (n + 6)}
    (hφ : IsBoundedSetFormula φ) : IsBoundedSetFormula (setForcingNegation φ) :=
  .and (.rel _ _) (.all _ (.or (boundedPairMemberFormula_bounded.subst _).neg (hφ.subst _).neg))

theorem setForcingDisjunction_bounded {n : ℕ} {φ ψ : SetTheorySemisentence (n + 6)}
    (hφ : IsBoundedSetFormula φ) (hψ : IsBoundedSetFormula ψ) :
    IsBoundedSetFormula (setForcingDisjunction φ ψ) :=
  .and (.rel _ _) (.all _ (.or (boundedPairMemberFormula_bounded.subst _).neg
    (.exs _ (.and (boundedPairMemberFormula_bounded.subst _) (.or (hφ.subst _) (hψ.subst _))))))

theorem setForcingUniversal_bounded {n : ℕ} {φ : SetTheorySemisentence (n + 1 + 6)}
    (hφ : IsBoundedSetFormula φ) : IsBoundedSetFormula (setForcingUniversal φ) :=
  .and (.rel _ _) (.all _ (hφ.subst _))

theorem setForcingExistential_bounded {n : ℕ} {φ : SetTheorySemisentence (n + 1 + 6)}
    (hφ : IsBoundedSetFormula φ) : IsBoundedSetFormula (setForcingExistential φ) :=
  .and (.rel _ _) (.all _ (.or (boundedPairMemberFormula_bounded.subst _).neg
    (.exs _ (.and (boundedPairMemberFormula_bounded.subst _) (.exs _ (hφ.subst _))))))

theorem boundedSetForcingTranslation_bounded {n : ℕ} (φ : SetTheorySemisentence n) :
    IsBoundedSetFormula (boundedSetForcingTranslation φ) := by
  induction φ with
  | verum => exact .rel _ _
  | falsum => exact .falsum
  | rel r ts => exact setForcingAtomic_bounded r ts
  | nrel r ts => exact setForcingNegation_bounded (setForcingAtomic_bounded r ts)
  | and φ ψ ihφ ihψ => exact .and ihφ ihψ
  | or φ ψ ihφ ihψ => exact setForcingDisjunction_bounded ihφ ihψ
  | all φ ih => exact setForcingUniversal_bounded ih
  | exs φ ih => exact setForcingExistential_bounded ih

end ZFVP
