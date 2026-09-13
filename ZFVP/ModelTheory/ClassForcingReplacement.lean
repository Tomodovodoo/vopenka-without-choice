import ZFVP.ModelTheory.ClassForcingImages
import ZFVP.Syntax.CloseTailParameters

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V) (hT : T.IsPretame) {G : Set V}
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
include hT

theorem classModel_replacement_names {n : ℕ} (φ : SetTheorySemisentence (n + 1 + 1))
    (w : Fin n → T.Name) (τ : T.Name)
    (huniq : ∀ x, x ∈ T.ofClassName hG τ → ∀ y z,
      φ.Evalb (x :> y :> T.classAssignment hG w) →
      φ.Evalb (x :> z :> T.classAssignment hG w) → y = z) :
    ∃ b : T.ClassModel hG, ∀ y, y ∈ b ↔ ∃ x, x ∈ T.ofClassName hG τ ∧
      φ.Evalb (x :> y :> T.classAssignment hG w) := by
  let A := fun σ ν p ↦ T.ForcesMember σ τ.val p ∧ T.towerFormula φ
    (assignmentPrepend ((n + 1 : ℕ) : V)
      (assignmentPrepend (n : V) (standardTuple (fun i ↦ (w i).val)) ν) σ) p
  have hA : ℒₛₑₜ-relation₃ A := by unfold A; definability
  have hr (σ ν : T.Name) : T.ClassRegular (A σ.val ν.val) :=
    T.classRegular_and (T.forcesMember_regular σ τ) (T.towerFormula_regular φ (σ :> ν :> w))
  apply T.classModel_definableImage hT hG τ A hA
    (fun σ ν ↦ (hr σ ν).1) (fun σ ν ↦ (hr σ ν).2.1)
    (fun x y ↦ φ.Evalb (x :> y :> T.classAssignment hG w)) _ huniq
  intro σ ν
  change T.ClassMeets G (fun p ↦ T.ForcesMember σ.val τ.val p ∧
    T.towerFormula φ (standardTuple (fun i ↦ ((σ :> ν :> w) i).val)) p) ↔ _
  rw [T.classMeets_and hG (T.forcesMember_regular σ τ).2.1
    (T.towerFormula_regular φ (σ :> ν :> w)).2.1]
  apply and_congr (T.member_truth hG σ τ).symm
  simpa only [T.classAssignment_cons] using
    (T.towerFormula_truth hG φ (σ :> ν :> w)).symm

theorem classModel_replacement {n : ℕ} (φ : SetTheorySemisentence (n + 1 + 1))
    (v : Fin n → T.ClassModel hG) (a : T.ClassModel hG)
    (huniq : ∀ x, x ∈ a → ∀ y z, φ.Evalb (x :> y :> v) → φ.Evalb (x :> z :> v) → y = z) :
    ∃ b : T.ClassModel hG, ∀ y, y ∈ b ↔ ∃ x, x ∈ a ∧ φ.Evalb (x :> y :> v) := by
  obtain ⟨τ, rfl⟩ := T.ofClassName_surjective hG a
  choose w hw using fun i ↦ T.ofClassName_surjective hG (v i)
  have he : T.classAssignment hG w = v := funext hw
  simpa only [he] using T.classModel_replacement_names hT hG φ w τ (by simpa only [he] using huniq)

theorem classModel_models_replacement (φ : SetTheorySemiproposition 2) :
    (T.ClassModel hG)↓[ℒₛₑₜ] ⊧ Axiom.replacementSchema φ := by
  simp [models_iff, Axiom.replacementSchema, Semiformula.eval_univCl]
  intro e hf a
  have he (x y : T.ClassModel hG) := eval_closeTailParameters φ ![x, y] e
  have hu : ∀ x, x ∈ a → ∀ y z,
      (closeTailParameters φ).Evalb (x :> y :> (fun i : Fin φ.fvSup ↦ e i.val)) →
      (closeTailParameters φ).Evalb (x :> z :> (fun i : Fin φ.fvSup ↦ e i.val)) → y = z := by
    intro x _ y z hy hz
    obtain ⟨w, _, hw⟩ := hf x
    exact (hw y ((he x y).mp hy)).trans (hw z ((he x z).mp hz)).symm
  obtain ⟨b, hb⟩ := T.classModel_replacement hT hG (closeTailParameters φ)
    (fun i : Fin φ.fvSup ↦ e i.val) a hu
  refine ⟨b, fun y ↦ ?_⟩
  exact (hb y).trans (exists_congr (fun x ↦ and_congr Iff.rfl (he x y)))

end DefinableForcingTower
end ZFVP
