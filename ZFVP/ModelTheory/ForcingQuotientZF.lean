import ZFVP.ModelTheory.ForcingQuotientPairing
import ZFVP.ModelTheory.ForcingQuotientUnion
import ZFVP.ModelTheory.ForcingQuotientPower
import ZFVP.ModelTheory.ForcingQuotientInfinity
import ZFVP.ModelTheory.ForcingQuotientFoundation
import ZFVP.ModelTheory.ForcingQuotientReplacement
import ZFVP.Syntax.CloseTailParameters

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingQuotient_models_separation (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (φ : SetTheorySemiproposition 1) :
    (ForcingQuotient P R G hR hG.1)↓[ℒₛₑₜ] ⊧ Axiom.separationSchema φ := by
  unfold IsExternalForcingGeneric at hG
  simp [models_iff, Axiom.separationSchema, Semiformula.eval_univCl]
  intro e a
  obtain ⟨b, hb⟩ := forcingQuotient_separation P R G hR hG (closeTailParameters φ)
    (fun i : Fin φ.fvSup ↦ e i.val) a
  refine ⟨b, fun x ↦ ?_⟩
  exact (hb x).trans (and_congr Iff.rfl (eval_closeTailParameters φ ![x] e))

theorem forcingQuotient_models_replacement (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (φ : SetTheorySemiproposition 2) :
    (ForcingQuotient P R G hR hG.1)↓[ℒₛₑₜ] ⊧ Axiom.replacementSchema φ := by
  unfold IsExternalForcingGeneric at hG
  simp [models_iff, Axiom.replacementSchema, Semiformula.eval_univCl]
  intro e hf a
  have he (x y : ForcingQuotient P R G hR hG.1) := eval_closeTailParameters φ ![x, y] e
  have hu : ∀ x, x ∈ a → ∀ y z,
      (closeTailParameters φ).Evalb (x :> y :> (fun i : Fin φ.fvSup ↦ e i.val)) →
      (closeTailParameters φ).Evalb (x :> z :> (fun i : Fin φ.fvSup ↦ e i.val)) → y = z := by
    intro x _ y z hy hz
    obtain ⟨w, _, hw⟩ := hf x
    exact (hw y ((he x y).mp hy)).trans (hw z ((he x z).mp hz)).symm
  obtain ⟨b, hb⟩ := forcingQuotient_replacement P R G hR hG (closeTailParameters φ)
    (fun i : Fin φ.fvSup ↦ e i.val) a hu
  refine ⟨b, fun y ↦ ?_⟩
  exact (hb y).trans (exists_congr (fun x ↦ and_congr Iff.rfl (he x y)))

theorem forcingQuotient_models_zf (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (one : V) (hone : IsForcingTop P R one) :
    (ForcingQuotient P R G hR hG.1)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  unfold IsExternalForcingGeneric at hG
  refine ⟨?_⟩
  intro φ hφ
  cases hφ with
  | axiom_of_equality φ hφ => exact Theory.models (ForcingQuotient P R G hR hG.1) (𝗘𝗤 ℒₛₑₜ) hφ
  | axiom_of_empty_set =>
      simp [models_iff, Axiom.empty]
      exact ⟨forcingQuotientMk P R G hR hG.1 ⟨∅, empty_forcingName P⟩,
        forcingQuotient_empty P R G hR hG.1⟩
  | axiom_of_extentionality =>
      simp [models_iff, Axiom.extentionality]
      intro x y
      exact ⟨by rintro rfl; simp, forcingQuotient_extensionality P R G hR hG x y⟩
  | axiom_of_pairing =>
      simpa [models_iff, Axiom.pairing] using forcingQuotient_pairing P R G hR hG
  | axiom_of_union =>
      simpa [models_iff, Axiom.union] using forcingQuotient_union P R G hR hG
  | axiom_of_power_set =>
      simpa [models_iff, Axiom.power, isSubsetOf] using forcingQuotient_power P R G hR hG
  | axiom_of_infinity =>
      simp [models_iff, Axiom.infinity, isEmpty, isSucc]
      exact forcingQuotient_infinity P R G hR hG one hone
  | axiom_of_foundation =>
      simp [models_iff, Axiom.foundation, isNonempty]
      intro x y hy
      exact forcingQuotient_foundation P R G hR hG x ⟨y, hy⟩
  | axiom_of_separation φ => exact forcingQuotient_models_separation P R G hR hG φ
  | axiom_of_replacement φ => exact forcingQuotient_models_replacement P R G hR hG φ

end ZFVP
