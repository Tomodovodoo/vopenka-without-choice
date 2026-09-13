import ZFVP.SetTheory.ElementaryDefined
import ZFVP.Syntax.ForcingTranslationSemantics

/-! Uniform forcing formulas commute with elementary maps between ground models. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace ElementaryMap

variable {V W : Type*} [SetStructure V] [SetStructure W]
variable [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingPreorder_iff (j : ElementaryMap V W) (P R : V) :
    IsForcingPreorder P R ↔ IsForcingPreorder (j P) (j R) :=
  j.map_defined forcingPreorderFormula (fun v ↦ IsForcingPreorder (v 0) (v 1))
    (fun v ↦ IsForcingPreorder (v 0) (v 1)) ![P, R]

theorem forcingName_iff (j : ElementaryMap V W) (P τ : V) :
    IsForcingName P τ ↔ IsForcingName (j P) (j τ) :=
  j.map_defined forcingNameFormula (fun v ↦ IsForcingName (v 0) (v 1))
    (fun v ↦ IsForcingName (v 0) (v 1)) ![P, τ]

theorem hereditarilySymmetricName_iff (j : ElementaryMap V W) (P Γ F τ : V) :
    IsHereditarilySymmetricName P Γ F τ ↔ IsHereditarilySymmetricName (j P) (j Γ) (j F) (j τ) :=
  j.map_defined hereditarilySymmetricNameFormula
    (fun v ↦ IsHereditarilySymmetricName (v 0) (v 1) (v 2) (v 3))
    (fun v ↦ IsHereditarilySymmetricName (v 0) (v 1) (v 2) (v 3)) ![P, Γ, F, τ]

theorem map_checkName (j : ElementaryMap V W) (one x : V) :
    j (checkName one x) = checkName (j one) (j x) :=
  (j.map_defined checkNameFormula (fun v ↦ v 0 = checkName (v 1) (v 2))
    (fun v ↦ v 0 = checkName (v 1) (v 2)) ![checkName one x, one, x]).mp rfl

theorem map_nameAction (j : ElementaryMap V W) (π τ : V) :
    j (nameAction π τ) = nameAction (j π) (j τ) :=
  (j.map_defined nameActionFormula (fun v ↦ v 0 = nameAction (v 1) (v 2))
    (fun v ↦ v 0 = nameAction (v 1) (v 2)) ![nameAction π τ, π, τ]).mp rfl

theorem map_atomicEquality (j : ElementaryMap V W) (P R σ τ : V) :
    j (atomicEquality P R σ τ) = atomicEquality (j P) (j R) (j σ) (j τ) :=
  (j.map_defined atomicEqualityFormula
    (fun v ↦ v 0 = atomicEquality (v 1) (v 2) (v 3) (v 4))
    (fun v ↦ v 0 = atomicEquality (v 1) (v 2) (v 3) (v 4))
    ![atomicEquality P R σ τ, P, R, σ, τ]).mp rfl

theorem forcingFormula_iff (j : ElementaryMap V W) (P R p b : V)
    {n : ℕ} (φ : SetTheorySemisentence n) :
    p ∈ forcingFormula P R φ b ↔ j p ∈ forcingFormula (j P) (j R) φ (j b) :=
  j.map_defined (ordinaryForcingTranslation φ)
    (fun v ↦ v 4 ∈ forcingFormula (v 0) (v 1) φ (v 5))
    (fun v ↦ v 4 ∈ forcingFormula (v 0) (v 1) φ (v 5)) ![P, R, P, P, p, b]

theorem symmetricForcingFormula_iff (j : ElementaryMap V W) (P R Γ F p b : V)
    {n : ℕ} (φ : SetTheorySemisentence n) :
    p ∈ symmetricForcingFormula P R Γ F φ b ↔
      j p ∈ symmetricForcingFormula (j P) (j R) (j Γ) (j F) φ (j b) :=
  j.map_defined (symmetricForcingTranslation φ)
    (fun v ↦ v 4 ∈ symmetricForcingFormula (v 0) (v 1) (v 2) (v 3) φ (v 5))
    (fun v ↦ v 4 ∈ symmetricForcingFormula (v 0) (v 1) (v 2) (v 3) φ (v 5)) ![P, R, Γ, F, p, b]

theorem forcingFormula_tuple_iff (j : ElementaryMap V W) (P R p : V)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V) :
    p ∈ forcingFormula P R φ (standardTuple v) ↔
      j p ∈ forcingFormula (j P) (j R) φ (standardTuple (j ∘ v)) := by
  rw [← j.map_standardTuple]
  exact j.forcingFormula_iff P R p _ φ

end ElementaryMap
end ZFVP
