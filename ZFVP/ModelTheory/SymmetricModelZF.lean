import ZFVP.ModelTheory.SymmetricModelBasic
import ZFVP.ModelTheory.SymmetricModelPower
import ZFVP.ModelTheory.SymmetricModelReplacement
import ZFVP.Syntax.CloseTailParameters

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricContext

theorem models_separation (S : SymmetricContext V) (φ : SetTheorySemiproposition 1) :
    S.Model↓[ℒₛₑₜ] ⊧ Axiom.separationSchema φ := by
  simp [models_iff, Axiom.separationSchema, Semiformula.eval_univCl]
  intro e a
  obtain ⟨b, hb⟩ := S.separation (closeTailParameters φ)
    (fun i : Fin φ.fvSup ↦ e i.val) a
  refine ⟨b, fun x ↦ ?_⟩
  exact (hb x).trans (and_congr Iff.rfl (eval_closeTailParameters φ ![x] e))

theorem models_replacement (S : SymmetricContext V) (φ : SetTheorySemiproposition 2) :
    S.Model↓[ℒₛₑₜ] ⊧ Axiom.replacementSchema φ := by
  simp [models_iff, Axiom.replacementSchema, Semiformula.eval_univCl]
  intro e hf a
  have he (x y : S.Model) := eval_closeTailParameters φ ![x, y] e
  have hu : ∀ x, x ∈ a → ∀ y z,
      (closeTailParameters φ).Evalb (x :> y :> (fun i : Fin φ.fvSup ↦ e i.val)) →
      (closeTailParameters φ).Evalb (x :> z :> (fun i : Fin φ.fvSup ↦ e i.val)) → y = z := by
    intro x _ y z hy hz
    obtain ⟨w, _, hw⟩ := hf x
    exact (hw y ((he x y).mp hy)).trans (hw z ((he x z).mp hz)).symm
  obtain ⟨b, hb⟩ := S.replacement (closeTailParameters φ)
    (fun i : Fin φ.fvSup ↦ e i.val) a hu
  refine ⟨b, fun y ↦ ?_⟩
  exact (hb y).trans (exists_congr (fun x ↦ and_congr Iff.rfl (he x y)))

instance modelZF (S : SymmetricContext V) :
    S.Model↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  refine ⟨?_⟩
  intro φ hφ
  cases hφ with
  | axiom_of_equality φ hφ => exact Theory.models S.Model (𝗘𝗤 ℒₛₑₜ) hφ
  | axiom_of_empty_set =>
      simp [models_iff, Axiom.empty]
      exact S.empty_set
  | axiom_of_extentionality =>
      simp [models_iff, Axiom.extentionality]
      intro x y
      exact ⟨by rintro rfl; simp, S.extensionality x y⟩
  | axiom_of_pairing =>
      simpa [models_iff, Axiom.pairing] using S.pairing
  | axiom_of_union =>
      simpa [models_iff, Axiom.union] using S.union_set
  | axiom_of_power_set =>
      simpa [models_iff, Axiom.power, isSubsetOf] using S.power_set
  | axiom_of_infinity =>
      simp [models_iff, Axiom.infinity, isEmpty, isSucc]
      exact S.infinity
  | axiom_of_foundation =>
      simp [models_iff, Axiom.foundation, isNonempty]
      intro x y hy
      exact S.foundation x ⟨y, hy⟩
  | axiom_of_separation φ => exact S.models_separation φ
  | axiom_of_replacement φ => exact S.models_replacement φ

end SymmetricContext
end ZFVP
