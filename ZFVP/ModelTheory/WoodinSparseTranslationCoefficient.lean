import ZFVP.ModelTheory.SparseBoundedForcingBaseBound
import ZFVP.ModelTheory.WoodinSparseForcingTranslation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

private structure TranslationCoefficient (C A B D : ℕ) where
  value : ℕ
  exactValue : value = C + A + B + D + 100
  base : C + 100 ≤ value
  carrier : A ≤ value
  order : B ≤ value
  names : D ≤ value

private def makeTranslationCoefficient (C A B D : ℕ) : TranslationCoefficient C A B D where
  value := C + A + B + D + 100
  exactValue := rfl
  base := by omega
  carrier := by omega
  order := by omega
  names := by omega

private opaque sparseTranslationCoefficientData : TranslationCoefficient sparseAtomicSyntaxConstant
    (levySyntacticBound woodinSparseClassCarrierFormula)
    (levySyntacticBound woodinSparseClassOrderFormula)
    (levySyntacticBound woodinSparseClassNameFormula) :=
  makeTranslationCoefficient _ _ _ _

/-- Explicit fixed syntax coefficient. The checked package keeps Lean from
normalizing the entire sparse recursion while proving elementary inequalities. -/
def woodinSparseTranslationCoefficient : ℕ := sparseTranslationCoefficientData.value

theorem woodinSparseTranslationCoefficient_eq : woodinSparseTranslationCoefficient =
    sparseAtomicSyntaxConstant + levySyntacticBound woodinSparseClassCarrierFormula +
    levySyntacticBound woodinSparseClassOrderFormula +
    levySyntacticBound woodinSparseClassNameFormula + 100 := sparseTranslationCoefficientData.exactValue

theorem woodinSparseTranslationCoefficient_base :
    sparseAtomicSyntaxConstant + 100 ≤ woodinSparseTranslationCoefficient := sparseTranslationCoefficientData.base

theorem woodinSparseTranslationCoefficient_ge : 6 ≤ woodinSparseTranslationCoefficient := by
  have h := woodinSparseTranslationCoefficient_base
  omega

theorem woodinSparseTranslationCoefficient_carrier :
    levySyntacticBound woodinSparseClassCarrierFormula ≤ woodinSparseTranslationCoefficient :=
  sparseTranslationCoefficientData.carrier

theorem woodinSparseTranslationCoefficient_order :
    levySyntacticBound woodinSparseClassOrderFormula ≤ woodinSparseTranslationCoefficient :=
  sparseTranslationCoefficientData.order

theorem woodinSparseTranslationCoefficient_names :
    levySyntacticBound woodinSparseClassNameFormula ≤ woodinSparseTranslationCoefficient :=
  sparseTranslationCoefficientData.names

private theorem atomCoefficient (C K n X : ℕ) (hX : X ≤ C+6*n+60) (hK : C+100 ≤ K) :
    X ≤ K*(n+1) := by
  have hn : 6*n ≤ K*n := Nat.mul_le_mul_right n (by omega)
  simp only [Nat.mul_add, Nat.mul_one]
  omega

theorem woodinSparseAtomic_compiler_bound {n a} (r : Language.Set.Rel a)
    (ts : Fin a → SetTheorySemiterm Empty n) :
    levySyntacticBound (sparseBoundedForcingBase (.rel r ts)) ≤
      woodinSparseTranslationCoefficient * (n+1) ∧
    levySyntacticBound (sparseBoundedForcingBase (.nrel r ts)) ≤
      woodinSparseTranslationCoefficient * (n+1) :=
  ⟨atomCoefficient _ _ _ _ (sparseBoundedForcingBase_atom_bound r ts).1
      woodinSparseTranslationCoefficient_base,
   atomCoefficient _ _ _ _ (sparseBoundedForcingBase_atom_bound r ts).2
      woodinSparseTranslationCoefficient_base⟩

end ZFVP
