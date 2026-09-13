import ZFVP.SetTheory.ClassFormulaForcingAction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def symmetricForcingFormula (P R Γ F : V) {n : ℕ}
    (φ : SetTheorySemisentence n) : V → V :=
  classForcingFormula P R (IsHereditarilySymmetricName P Γ F) (by definability) φ

instance symmetricForcingFormula_definable (P R Γ F : V) {n : ℕ}
    (φ : SetTheorySemisentence n) : ℒₛₑₜ-function₁[V] (symmetricForcingFormula P R Γ F φ) := by
  unfold symmetricForcingFormula
  infer_instance

theorem symmetricForcingFormula_regular {P R : V} (hR : IsForcingPreorder P R)
    (Γ F : V) {n : ℕ} (φ : SetTheorySemisentence n) (b : V) :
    IsForcingRegular P R (symmetricForcingFormula P R Γ F φ b) :=
  classForcingFormula_regular _ _ hR φ b

theorem symmetricForcingFormula_nameAction_iff {P R Γ F π p : V}
    (hR : IsForcingPreorder P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hπ : π ∈ Γ)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V)
    (hv : ∀ i, IsHereditarilySymmetricName P Γ F (v i)) (hp : p ∈ P) :
    π ‘ p ∈ symmetricForcingFormula P R Γ F φ (standardTuple (fun i ↦ nameAction π (v i))) ↔
      p ∈ symmetricForcingFormula P R Γ F φ (standardTuple v) := by
  apply classForcingFormula_nameAction_iff hR (hΓ.1 π hπ) _ _ (fun _ hx ↦ hx.1)
    (fun _ hx ↦ hereditarilySymmetric_nameAction hΓ hF hπ hx) ?_ φ v hv hp
  intro y hy
  exact ⟨nameAction (converseGraph π) y,
    hereditarilySymmetric_nameAction hΓ hF (hΓ.2.2.2 π hπ) hy,
    nameAction_cancel_inverse (hΓ.1 π hπ) hy.1⟩

theorem symmetricForcingFormula_fixed_iff {P R Γ F π p : V}
    (hR : IsForcingPreorder P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hπ : π ∈ Γ)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V)
    (hv : ∀ i, IsHereditarilySymmetricName P Γ F (v i))
    (hfix : ∀ i, nameAction π (v i) = v i) (hp : p ∈ P) :
    π ‘ p ∈ symmetricForcingFormula P R Γ F φ (standardTuple v) ↔
      p ∈ symmetricForcingFormula P R Γ F φ (standardTuple v) := by
  have he : (fun i ↦ nameAction π (v i)) = v := funext hfix
  simpa only [he] using symmetricForcingFormula_nameAction_iff hR hΓ hF hπ φ v hv hp

end ZFVP
