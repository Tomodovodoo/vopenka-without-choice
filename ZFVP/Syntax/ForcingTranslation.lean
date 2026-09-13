import ZFVP.Syntax.UniformAssignments
import ZFVP.SetTheory.AtomicForcingDictionary
import ZFVP.SetTheory.SymmetryDictionary
import ZFVP.SetTheory.ForcingAtoms

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingTermFormula {n : ℕ} : Semiterm ℒₛₑₜ Empty n → SetTheorySemisentence 2
  | .bvar i => f“x b. x = !value.dfn b (!(numeralFormula i.val))”
  | .fvar x => Empty.elim x
  | .func f _ => Empty.elim f

def forcingAtomicTranslation {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) : SetTheorySemisentence 6 :=
  match r with
  | .eq => f“P R G F p b. p ∈ !atomicEqualityFormula P R (!(forcingTermFormula (ts 0)) b) (!(forcingTermFormula (ts 1)) b)”
  | .mem => f“P R G F p b. p ∈ !atomicMembershipFormula P R (!(forcingTermFormula (ts 0)) b) (!(forcingTermFormula (ts 1)) b)”

def forcingNegationTranslation (φ : SetTheorySemisentence 6) : SetTheorySemisentence 6 :=
  f“P R G F p b. p ∈ P ∧ ∀ q ∈ P, !kpair.dfn q p ∈ R → ¬!φ P R G F q b”

def forcingConjunctionTranslation (φ ψ : SetTheorySemisentence 6) : SetTheorySemisentence 6 :=
  f“P R G F p b. !φ P R G F p b ∧ !ψ P R G F p b”

def forcingDisjunctionTranslation (φ ψ : SetTheorySemisentence 6) : SetTheorySemisentence 6 :=
  f“P R G F p b. p ∈ P ∧ ∀ q ∈ P, !kpair.dfn q p ∈ R →
    ∃ r ∈ P, !kpair.dfn r q ∈ R ∧ (!φ P R G F r b ∨ !ψ P R G F r b)”

def forcingUniversalTranslation (χ : SetTheorySemisentence 4) (n : ℕ)
    (φ : SetTheorySemisentence 6) : SetTheorySemisentence 6 :=
  f“P R G F p b. p ∈ P ∧ ∀ x, !χ P G F x →
    !φ P R G F p (!assignmentPrependFormula (!(numeralFormula n)) b x)”

def forcingExistentialTranslation (χ : SetTheorySemisentence 4) (n : ℕ)
    (φ : SetTheorySemisentence 6) : SetTheorySemisentence 6 :=
  f“P R G F p b. p ∈ P ∧ ∀ q ∈ P, !kpair.dfn q p ∈ R →
    ∃ r ∈ P, !kpair.dfn r q ∈ R ∧ ∃ x, !χ P G F x ∧
      !φ P R G F r (!assignmentPrependFormula (!(numeralFormula n)) b x)”

def forcingTranslation (χ : SetTheorySemisentence 4) : {n : ℕ} → SetTheorySemisentence n → SetTheorySemisentence 6
  | _, .verum => “P R G F p b. p ∈ P”
  | _, .falsum => ⊥
  | _, .rel r ts => forcingAtomicTranslation r ts
  | _, .nrel r ts => forcingNegationTranslation (forcingAtomicTranslation r ts)
  | _, .and φ ψ => forcingConjunctionTranslation (forcingTranslation χ φ) (forcingTranslation χ ψ)
  | _, .or φ ψ => forcingDisjunctionTranslation (forcingTranslation χ φ) (forcingTranslation χ ψ)
  | n, .all φ => forcingUniversalTranslation χ n (forcingTranslation χ φ)
  | n, .exs φ => forcingExistentialTranslation χ n (forcingTranslation χ φ)

def ordinaryNameClassFormula : SetTheorySemisentence 4 := f“P G F t. !forcingNameFormula P t”

def ordinaryForcingTranslation {n : ℕ} (φ : SetTheorySemisentence n) : SetTheorySemisentence 6 :=
  forcingTranslation ordinaryNameClassFormula φ

def symmetricForcingTranslation {n : ℕ} (φ : SetTheorySemisentence n) : SetTheorySemisentence 6 :=
  forcingTranslation hereditarilySymmetricNameFormula φ

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingTermFormula_defined {n : ℕ} (t : Semiterm ℒₛₑₜ Empty n) :
    ℒₛₑₜ-function₁[V] (forcingTermValue t) via forcingTermFormula t := by
  cases t with
  | bvar i => exact ⟨fun v ↦ by simp [forcingTermFormula, forcingTermValue]⟩
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

instance forcingAtomicTranslation_defined {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) :
    Defined (fun v : Fin 6 → V ↦ v 4 ∈ forcingAtomic (v 0) (v 1) r ts (v 5)) (forcingAtomicTranslation r ts) := by
  cases r <;> exact ⟨fun v ↦ by simp [forcingAtomicTranslation, forcingAtomic]⟩

instance ordinaryNameClassFormula_defined :
    Defined (fun v : Fin 4 → V ↦ IsForcingName (v 0) (v 3)) ordinaryNameClassFormula :=
  ⟨fun v ↦ by simp [ordinaryNameClassFormula]⟩

end ZFVP
