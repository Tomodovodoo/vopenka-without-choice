import ZFVP.SetTheory.NaturalMultiplication
import ZFVP.SetTheory.BoundedNaturals
import Foundation.FirstOrder.Interpretation
import Foundation.FirstOrder.Arithmetic.Basic.Model

/-! A uniform interpretation of arithmetic in the whole omega of a ZF model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

def arithmeticNaturalDomain : SetTheorySemisentence 1 := f“x. x ∈ !isω”

def arithmeticNaturalFunction {k : ℕ} : Language.ORing.Func k → SetTheorySemisentence (k + 1)
  | .zero => isEmpty
  | .one => boundedNumeralFormula 1
  | .add => ordinalAddFormula
  | .mul => naturalMulFormula

def arithmeticNaturalRelation {k : ℕ} : Language.ORing.Rel k → SetTheorySemisentence k
  | .eq => “x y. x = y”
  | .lt => “x y. x ∈ y”

section total

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance arithmeticNaturalDomain_defined :
    ℒₛₑₜ-predicate[V] (fun x ↦ x ∈ (ω : V)) via arithmeticNaturalDomain :=
  ⟨fun v ↦ by simp [arithmeticNaturalDomain]⟩

theorem arithmeticNaturalFunction_total {k : ℕ} (f : Language.ORing.Func k) :
    ∀ v : Fin k → V, (∀ i, v i ∈ (ω : V)) →
      ∃! y : V, y ∈ (ω : V) ∧ (arithmeticNaturalFunction f).Evalb (y :> v) := by
  cases f with
  | zero =>
    intro v _
    refine ⟨∅, ⟨by simp, by simp [arithmeticNaturalFunction]⟩, ?_⟩
    intro y hy; simpa [arithmeticNaturalFunction] using hy.2
  | one =>
    intro v _
    refine ⟨1, ⟨by simp, by simp [arithmeticNaturalFunction]⟩, ?_⟩
    intro y hy; simpa [arithmeticNaturalFunction] using hy.2
  | add =>
    intro v hv
    refine ⟨ordinalAdd (v 0) (v 1), ⟨ordinalAdd_natural (hv 0) (hv 1), ?_⟩, ?_⟩
    · simp [arithmeticNaturalFunction]
    · intro y hy; simpa [arithmeticNaturalFunction] using hy.2
  | mul =>
    intro v hv
    refine ⟨naturalMul (v 0) (v 1), ⟨naturalMul_natural (hv 0) (hv 1), ?_⟩, ?_⟩
    · simp [arithmeticNaturalFunction]
    · intro y hy; simpa [arithmeticNaturalFunction] using hy.2

end total

def arithmeticInZF : DirectTranslation 𝗭𝗙 ℒₒᵣ where
  domain := arithmeticNaturalDomain
  func := arithmeticNaturalFunction
  rel := arithmeticNaturalRelation
  domain_nonempty := by
    apply SetTheory.provable_of_models.{0} 𝗭𝗙 _
    intro V _ _ _
    simpa [models_iff, arithmeticNaturalDomain] using (show ∃ x : V, x ∈ (ω : V) from ⟨0, by simp⟩)
  func_defined f := by
    apply SetTheory.provable_of_models.{0} 𝗭𝗙 _
    intro V _ _ _
    simpa [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton]
      using arithmeticNaturalFunction_total (V := V) f
  preserve_eq := by
    apply SetTheory.provable_of_models.{0} 𝗭𝗙 _
    intro V _ _ _
    simp [models_iff, arithmeticNaturalRelation]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem arithmeticInZF_domain (x : V) : arithmeticInZF.Dom x ↔ x ∈ (ω : V) := by
  simp [DirectTranslation.Dom, arithmeticInZF, arithmeticNaturalDomain]

theorem arithmeticInZF_translation {n : ℕ} (φ : ArithmeticSemisentence n)
    (v : Fin n → arithmeticInZF.Model V) :
    (arithmeticInZF.translate φ).Evalb (fun i ↦ (v i).val) ↔
      φ.Evalb v := DirectTranslation.Model.evalb_translate_iff

end ZFVP
