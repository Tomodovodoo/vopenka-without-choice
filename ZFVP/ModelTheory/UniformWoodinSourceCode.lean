import ZFVP.ModelTheory.UniformWoodinSparseSuccessor
import ZFVP.ModelTheory.WoodinSourceCode

/-! Total uniform formulas for insertion of the seed coordinate. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinRecursiveIndexFormula : SetTheorySemisentence 2 :=
  f“z β. (β ∈ !isω ∧ z = !sUnion.dfn β) ∨ (β ∉ !isω ∧ z = β)”

def woodinInsertSeedValueFormula : SetTheorySemisentence 4 :=
  f“z f a β. (!isEmpty β ∧ z = a) ∨
    (¬!isEmpty β ∧ z = !value.dfn f (!woodinRecursiveIndexFormula β))”

def woodinInsertSeedFormula : SetTheorySemisentence 4 :=
  f“g θ f a. ∀ z, z ∈ g ↔ ∃ β ∈ !sparseWoodinSourceIndexFormula θ,
    z = !kpair.dfn β (!woodinInsertSeedValueFormula f a β)”

def woodinSeedMatrixValueFormula : SetTheorySemisentence 4 :=
  f“y M C z. (!isEmpty (!kpair.π₁.dfn z) ∧ y = !value.dfn C (!kpair.π₂.dfn z)) ∨
    (¬!isEmpty (!kpair.π₁.dfn z) ∧ y = !value.dfn M
      (!kpair.dfn (!woodinRecursiveIndexFormula (!kpair.π₁.dfn z))
        (!woodinRecursiveIndexFormula (!kpair.π₂.dfn z))))”

def woodinSeedMatrixFormula : SetTheorySemisentence 4 :=
  f“g θ M C. ∀ z, z ∈ g ↔
    ∃ p ∈ !prod.dfn (!sparseWoodinSourceIndexFormula θ) (!sparseWoodinSourceIndexFormula θ),
      z = !kpair.dfn p (!woodinSeedMatrixValueFormula M C p)”

def woodinSeedProjectionColumnFormula : SetTheorySemisentence 3 :=
  f“g θ Q. ∀ z, z ∈ g ↔ ∃ j ∈ !sparseWoodinSourceIndexFormula θ,
    z = !kpair.dfn j (!prod.dfn (!value.dfn Q j) (!singleton.dfn (!isEmpty)))”

def woodinSeedSectionColumnFormula : SetTheorySemisentence 3 :=
  f“g θ t. ∀ z, z ∈ g ↔ ∃ j ∈ !sparseWoodinSourceIndexFormula θ,
    z = !kpair.dfn j (!prod.dfn (!singleton.dfn (!isEmpty)) (!singleton.dfn (!value.dfn t j)))”

def woodinSeedLiftMapFormula : SetTheorySemisentence 2 :=
  f“M Q. ∀ z, z ∈ M ↔ ∃ p ∈ !prod.dfn Q (!singleton.dfn (!isEmpty)),
    z = !kpair.dfn p (!kpair.π₁.dfn p)”

def woodinSeedLiftColumnFormula : SetTheorySemisentence 3 :=
  f“g θ Q. ∀ z, z ∈ g ↔ ∃ j ∈ !sparseWoodinSourceIndexFormula θ,
    z = !kpair.dfn j (!woodinSeedLiftMapFormula (!value.dfn Q j))”

def woodinSeedProjectionsFormula : SetTheorySemisentence 4 :=
  f“g θ P π. !woodinSeedMatrixFormula g θ π
    (!woodinSeedProjectionColumnFormula θ (!woodinInsertSeedFormula θ P (!singleton.dfn (!isEmpty))))”

def woodinSeedSectionsFormula : SetTheorySemisentence 4 :=
  f“g θ E t. !woodinSeedMatrixFormula g θ E
    (!woodinSeedSectionColumnFormula θ (!woodinInsertSeedFormula θ t (!isEmpty)))”

def woodinSeedLiftsFormula : SetTheorySemisentence 4 :=
  f“g θ P L. !woodinSeedMatrixFormula g θ L
    (!woodinSeedLiftColumnFormula θ (!woodinInsertSeedFormula θ P (!singleton.dfn (!isEmpty))))”

def woodinSourceCodeFormula : SetTheorySemisentence 3 :=
  “z θ s. ∃ P, ∃ R, ∃ π, ∃ E, ∃ L, ∃ t, ∃ o, ∃ u, ∃ v,
    ∃ Q, ∃ T, ∃ ρ, ∃ F, ∃ M, ∃ b,
    !forcingCodePFormula P s ∧ !forcingCodeRFormula R s ∧ !forcingCodeπFormula π s ∧
    !forcingCodeEFormula E s ∧ !forcingCodeLFormula L s ∧ !forcingCodetFormula t s ∧
    !isEmpty o ∧ !singleton.dfn u o ∧ !prod.dfn v u u ∧
    !woodinInsertSeedFormula Q θ P u ∧ !woodinInsertSeedFormula T θ R v ∧
    !woodinSeedProjectionsFormula ρ θ P π ∧ !woodinSeedSectionsFormula F θ E t ∧
    !woodinSeedLiftsFormula M θ P L ∧ !woodinInsertSeedFormula b θ t o ∧
    !forcingIterationCodeFormula z Q T ρ F M b”

def woodinSourceCardinalsFormula : SetTheorySemisentence 3 :=
  f“z θ K. !woodinInsertSeedFormula z θ K (!woodinSeedCardinalFormula)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinRecursiveIndexFormula_defined :
    ℒₛₑₜ-function₁[V] woodinRecursiveIndex via woodinRecursiveIndexFormula :=
  ⟨fun v ↦ by
    classical
    by_cases h : v 1 ∈ (ω : V) <;> simp [woodinRecursiveIndexFormula, woodinRecursiveIndex, h]⟩

instance woodinInsertSeedValueFormula_defined :
    ℒₛₑₜ-function₃[V] woodinInsertSeedValue via woodinInsertSeedValueFormula :=
  ⟨fun v ↦ by
    classical
    by_cases h : v 3 = ∅ <;>
      simp [woodinInsertSeedValueFormula, woodinInsertSeedValue, isEmpty_iff_eq_empty, h]⟩

instance woodinInsertSeedFormula_defined :
    ℒₛₑₜ-function₃[V] woodinInsertSeed via woodinInsertSeedFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [woodinInsertSeedFormula, woodinInsertSeed, mem_definableGraph_iff]⟩

instance woodinSeedMatrixValueFormula_defined :
    ℒₛₑₜ-function₃[V] woodinSeedMatrixValue via woodinSeedMatrixValueFormula :=
  ⟨fun v ↦ by
    classical
    by_cases h : kpair.π₁ (v 3) = ∅ <;>
      simp [woodinSeedMatrixValueFormula, woodinSeedMatrixValue, isEmpty_iff_eq_empty, h]⟩

instance woodinSeedMatrixFormula_defined :
    ℒₛₑₜ-function₃[V] woodinSeedMatrix via woodinSeedMatrixFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [woodinSeedMatrixFormula, woodinSeedMatrix, mem_definableGraph_iff]⟩

instance woodinSeedProjectionColumnFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSeedProjectionColumn via woodinSeedProjectionColumnFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [woodinSeedProjectionColumnFormula,
    woodinSeedProjectionColumn, mem_definableGraph_iff]⟩

instance woodinSeedSectionColumnFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSeedSectionColumn via woodinSeedSectionColumnFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [woodinSeedSectionColumnFormula,
    woodinSeedSectionColumn, mem_definableGraph_iff]⟩

instance woodinSeedLiftMapFormula_defined :
    ℒₛₑₜ-function₁[V] woodinSeedLiftMap via woodinSeedLiftMapFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [woodinSeedLiftMapFormula, woodinSeedLiftMap, mem_definableGraph_iff]⟩

instance woodinSeedLiftColumnFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSeedLiftColumn via woodinSeedLiftColumnFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [woodinSeedLiftColumnFormula, woodinSeedLiftColumn, mem_definableGraph_iff]⟩

instance woodinSeedProjectionsFormula_defined :
    ℒₛₑₜ-function₃[V] woodinSeedProjections via woodinSeedProjectionsFormula :=
  ⟨fun v ↦ by simp [woodinSeedProjectionsFormula, woodinSeedProjections]⟩

instance woodinSeedSectionsFormula_defined :
    ℒₛₑₜ-function₃[V] woodinSeedSections via woodinSeedSectionsFormula :=
  ⟨fun v ↦ by simp [woodinSeedSectionsFormula, woodinSeedSections]⟩

instance woodinSeedLiftsFormula_defined :
    ℒₛₑₜ-function₃[V] woodinSeedLifts via woodinSeedLiftsFormula :=
  ⟨fun v ↦ by simp [woodinSeedLiftsFormula, woodinSeedLifts]⟩

instance woodinSourceCodeFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSourceCode via woodinSourceCodeFormula :=
  ⟨fun v ↦ by simp [woodinSourceCodeFormula, woodinSourceCode, isEmpty_iff_eq_empty]⟩

instance woodinSourceCardinalsFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSourceCardinals via woodinSourceCardinalsFormula :=
  ⟨fun v ↦ by simp [woodinSourceCardinalsFormula, woodinSourceCardinals]⟩

def totalWoodinSourceDictionary : SetFormulaDictionary :=
  [⟨4, woodinInsertSeedFormula⟩, ⟨4, woodinSeedMatrixFormula⟩,
   ⟨3, woodinSourceCodeFormula⟩, ⟨3, woodinSourceCardinalsFormula⟩]

def totalWoodinSourceDictionaryBound : ℕ := levyDictionaryBound totalWoodinSourceDictionary

theorem totalWoodinSourceDictionary_complexity {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ totalWoodinSourceDictionary) (p : LevyPolarity) :
    IsLevyFormula p totalWoodinSourceDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

end ZFVP
