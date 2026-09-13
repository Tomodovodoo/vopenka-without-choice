import ZFVP.ModelTheory.ForcingUniqueName
import ZFVP.ModelTheory.ForcingFunctionValues

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A name for the unique object satisfying a fixed formula. Its set code
is a definable function of the tuple of parameter names, independently of G. -/
noncomputable def formulaUniqueName (P R : V) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (a : V) : V :=
  forcingUniqueName P R (fun b ν ↦ forcingFormula P R φ (assignmentPrepend (n : V) b ν))
    (by definability) a

instance formulaUniqueName_definable (P R : V) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) : ℒₛₑₜ-function₁[V] (formulaUniqueName P R φ) := by
  unfold formulaUniqueName
  infer_instance

theorem formulaUniqueName_isName (P R : V) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (a : V) : IsForcingName P (formulaUniqueName P R φ a) :=
  forcingUniqueName_isName P R _ _ a

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def formulaName {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → ForcingName A.P) : ForcingName A.P :=
  ⟨formulaUniqueName A.P A.R φ (standardTuple (fun i ↦ (v i).val)), formulaUniqueName_isName _ _ _ _⟩

theorem formulaName_value {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → ForcingName A.P)
    (hu : ∀ x y : A.Model, φ.Evalb (x :> (fun i ↦ A.ofName (v i))) →
      φ.Evalb (y :> (fun i ↦ A.ofName (v i))) → x = y)
    {x : A.Model} (hx : φ.Evalb (x :> (fun i ↦ A.ofName (v i)))) :
    A.ofName (A.formulaName φ v) = x := by
  apply A.uniqueName_value (fun b ν ↦ forcingFormula A.P A.R φ (assignmentPrepend (n : V) b ν))
    (by definability) (standardTuple (fun i ↦ (v i).val))
    (fun x ↦ φ.Evalb (x :> (fun i ↦ A.ofName (v i)))) _ hu hx
  intro ν
  have ht := (A.formula_truth φ (ν :> v)).symm
  have hv : (fun i ↦ A.ofName ((ν :> v) i)) = A.ofName ν :> (fun i ↦ A.ofName (v i)) := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  rw [hv, forcingNameTuple_cons] at ht
  exact ht

theorem formulaName_spec {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → ForcingName A.P)
    (hex : ∃! x : A.Model, φ.Evalb (x :> (fun i ↦ A.ofName (v i)))) :
    φ.Evalb (A.ofName (A.formulaName φ v) :> (fun i ↦ A.ofName (v i))) := by
  obtain ⟨x, hx, hu⟩ := hex
  rw [A.formulaName_value φ v (fun y z hy hz ↦ (hu y hy).trans (hu z hz).symm) hx]
  exact hx

end ForcingContext
end ZFVP
