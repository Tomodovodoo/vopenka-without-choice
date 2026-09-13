import ZFVP.ModelTheory.ForcingQuotientImages

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingQuotient_replacementNames (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (τ : ForcingName P) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1 + 1)) (v : Fin n → ForcingName P)
    (huniq : ∀ a, a ∈ forcingQuotientMk P R G hR hG.1 τ → ∀ b c,
      φ.Evalb (a :> b :> forcingQuotientAssignment P R G hR hG.1 v) →
      φ.Evalb (a :> c :> forcingQuotientAssignment P R G hR hG.1 v) → b = c) :
    ∃ b : ForcingQuotient P R G hR hG.1, ∀ x, x ∈ b ↔
      ∃ a, a ∈ forcingQuotientMk P R G hR hG.1 τ ∧
        φ.Evalb (a :> x :> forcingQuotientAssignment P R G hR hG.1 v) := by
  unfold IsExternalForcingGeneric at hG
  apply forcingQuotient_definableImage P R G hR hG τ
    (fun σ ν ↦ forcingFormula P R φ
      (assignmentPrepend ((n + 1 : ℕ) : V)
        (assignmentPrepend (n : V) (standardTuple (fun i ↦ (v i).val)) ν) σ))
    (by definability) (fun σ ν _ _ ↦ (forcingFormula_regular hR φ _).2.1) _ _ huniq
  intro σ ν
  simpa only [forcingNameTuple_cons, forcingQuotientAssignment_cons] using
    (forcingFormula_quotient_truth P R G hR hG φ (σ :> ν :> v)).symm

theorem forcingQuotient_replacement (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) {n : ℕ} (φ : SetTheorySemisentence (n + 1 + 1))
    (v : Fin n → ForcingQuotient P R G hR hG.1) (a : ForcingQuotient P R G hR hG.1)
    (huniq : ∀ x, x ∈ a → ∀ y z, φ.Evalb (x :> y :> v) → φ.Evalb (x :> z :> v) → y = z) :
    ∃ b : ForcingQuotient P R G hR hG.1, ∀ y, y ∈ b ↔ ∃ x, x ∈ a ∧ φ.Evalb (x :> y :> v) := by
  unfold IsExternalForcingGeneric at hG
  obtain ⟨τ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 a
  choose w hw using fun i ↦ forcingQuotientMk_surjective P R G hR hG.1 (v i)
  have he : forcingQuotientAssignment P R G hR hG.1 w = v := funext hw
  simpa only [he] using forcingQuotient_replacementNames P R G hR hG τ φ w (by simpa only [he] using huniq)

end ZFVP
