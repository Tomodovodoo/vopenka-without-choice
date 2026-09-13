import ZFVP.Syntax.LevyCodes
import ZFVP.Syntax.UniformBoundedCodes

/-! A parameter-free defining formula for each standard internal Levy level. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def levyQuantifierCodeFormula (p : LevyPolarity) : SetTheorySemisentence 2 :=
  match p with
  | .sigma => existsCodeFormula
  | .pi => allCodeFormula

def isLevyExtensionClosedFormula (p : LevyPolarity) : SetTheorySemisentence 2 :=
  f“B Q. B ⊆ Q ∧ ∀ n ∈ !isω,
    (∀ φ ψ, !kpair.dfn n φ ∈ Q → !kpair.dfn n ψ ∈ Q →
      !kpair.dfn n (!andCodeFormula φ ψ) ∈ Q ∧ !kpair.dfn n (!orCodeFormula φ ψ) ∈ Q) ∧
    (∀ i ∈ n, ∀ φ, !kpair.dfn (!succ.dfn n) φ ∈ Q →
      !kpair.dfn n (!boundedAllCodeFormula i φ) ∈ Q ∧ !kpair.dfn n (!boundedExistsCodeFormula i φ) ∈ Q) ∧
    ∀ φ, !kpair.dfn (!succ.dfn n) φ ∈ Q → !kpair.dfn n (!(levyQuantifierCodeFormula p) φ) ∈ Q”

def levyExtensionFamilyFormula (p : LevyPolarity) : SetTheorySemisentence 2 :=
  f“F B. ∀ q, q ∈ F ↔ q ∈ !formulaFamilyFormula (!membershipLanguageCodeFormula) (!isEmpty) ∧
    ∀ Q, !(isLevyExtensionClosedFormula p) B Q → q ∈ Q”

def levyFormulaFamilyFormula : ℕ → LevyPolarity → SetTheorySemisentence 1
  | 0, _ => boundedFormulaFamilyFormula
  | k + 1, p => f“F. F = !(levyExtensionFamilyFormula p)
      (!union.dfn (!(levyFormulaFamilyFormula k .sigma)) (!(levyFormulaFamilyFormula k .pi)))”

def isLevyFormulaCodeFormula (p : LevyPolarity) (k : ℕ) : SetTheorySemisentence 2 :=
  f“n φ. !kpair.dfn n φ ∈ !(levyFormulaFamilyFormula k p)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance levyQuantifierCodeFormula_defined (p : LevyPolarity) :
    ℒₛₑₜ-function₁[V] (levyQuantifierCode p) via levyQuantifierCodeFormula p := by
  cases p
  · exact existsCodeFormula_defined
  · exact allCodeFormula_defined

instance isLevyExtensionClosedFormula_defined (p : LevyPolarity) :
    ℒₛₑₜ-relation[V] (IsLevyExtensionClosed p) via isLevyExtensionClosedFormula p :=
  ⟨fun v ↦ by simp [isLevyExtensionClosedFormula, IsLevyExtensionClosed]⟩

instance levyExtensionFamilyFormula_defined (p : LevyPolarity) :
    ℒₛₑₜ-function₁[V] (levyExtensionFamily p) via levyExtensionFamilyFormula p :=
  ⟨fun v ↦ by
    change (levyExtensionFamilyFormula p).Evalb v ↔ v 0 = levyExtensionFamily p (v 1)
    rw [mem_ext_iff]
    simp [levyExtensionFamilyFormula, mem_levyExtensionFamily_iff]⟩

instance levyFormulaFamilyFormula_defined (k : ℕ) (p : LevyPolarity) :
    ℒₛₑₜ-function₀[V] (levyFormulaFamily k p) via levyFormulaFamilyFormula k p := by
  induction k generalizing p with
  | zero => exact boundedFormulaFamilyFormula_defined
  | succ k ih =>
    have := ih .sigma
    have := ih .pi
    exact ⟨fun v ↦ by simp [levyFormulaFamilyFormula, levyFormulaFamily]⟩

instance isLevyFormulaCodeFormula_defined (p : LevyPolarity) (k : ℕ) :
    ℒₛₑₜ-relation[V] (IsLevyFormulaCode p k) via isLevyFormulaCodeFormula p k :=
  ⟨fun v ↦ by simp [isLevyFormulaCodeFormula, IsLevyFormulaCode]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_levyFormulaCode_iff (j : ElementaryMap V W) (p : LevyPolarity) (k : ℕ) (n φ : V) :
    IsLevyFormulaCode p k (j n) (j φ) ↔ IsLevyFormulaCode p k n φ :=
  (j.map_defined (isLevyFormulaCodeFormula p k) (fun v ↦ IsLevyFormulaCode p k (v 0) (v 1))
    (fun v ↦ IsLevyFormulaCode p k (v 0) (v 1)) ![n, φ]).symm

end ElementaryMap
end ZFVP
