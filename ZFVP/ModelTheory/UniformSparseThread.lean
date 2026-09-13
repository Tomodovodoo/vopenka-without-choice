import ZFVP.ModelTheory.UniformSparsePair
import ZFVP.SetTheory.SparseThreadPresentation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sparseRestrictionThreadsFormula : SetTheorySemisentence 5 :=
  f“C θ b P U. ∀ t, t ∈ C ↔ t ∈ !function.dfn U θ ∧
    (∀ i ∈ θ, !isSparseFunctionOnFormula (!value.dfn b i) (!value.dfn t i) ∧
      !value.dfn t i ∈ !value.dfn P i) ∧
    ∀ i ∈ θ, ∀ j ∈ θ, !restrict.dfn (!value.dfn t i) (!value.dfn b j) =
      !restrict.dfn (!value.dfn t j) (!value.dfn b i)”

def sparseThreadCarrierFormula : SetTheorySemisentence 6 :=
  f“C θ A b P U. ∀ q, q ∈ C ↔ q ⊆ !sUnion.dfn U ∧
    !isSparseFunctionOnFormula A q ∧
    ∀ i ∈ θ, !restrict.dfn q (!value.dfn b i) ∈ !value.dfn P i”

def sparseThreadDecodeValueFormula : SetTheorySemisentence 4 :=
  f“t θ b q. ∀ z, z ∈ t ↔ ∃ i ∈ θ,
    z = !kpair.dfn i (!restrict.dfn q (!value.dfn b i))”

def sparseThreadDecodeFormula : SetTheorySemisentence 6 :=
  “f θ A b P U. ∃ C, !sparseThreadCarrierFormula C θ A b P U ∧
    ∀ z, z ∈ f ↔ ∃ q ∈ C, ∃ t, !sparseThreadDecodeValueFormula t θ b q ∧
      !kpair.dfn z q t”

def sparseThreadEncodeFormula : SetTheorySemisentence 5 :=
  f“f θ b P U. ∀ z, z ∈ f ↔ ∃ t ∈ !sparseRestrictionThreadsFormula θ b P U,
    z = !kpair.dfn t (!sUnion.dfn (!range.dfn t))”

def sparseThreadOrderFormula : SetTheorySemisentence 5 :=
  f“S θ b R C. ∀ z, z ∈ S ↔ z ∈ !prod.dfn C C ∧ ∀ i ∈ θ,
    !kpair.dfn (!restrict.dfn (!kpair.π₁.dfn z) (!value.dfn b i))
      (!restrict.dfn (!kpair.π₂.dfn z) (!value.dfn b i)) ∈ !value.dfn R i”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sparseRestrictionThreadsFormula_defined :
    ℒₛₑₜ-function₄[V] sparseRestrictionThreads via sparseRestrictionThreadsFormula :=
  ⟨fun v ↦ by
    change sparseRestrictionThreadsFormula.Evalb v ↔
      v 0 = sparseRestrictionThreads (v 1) (v 2) (v 3) (v 4)
    rw [mem_ext_iff]
    simp [sparseRestrictionThreadsFormula, sparseRestrictionThreads]⟩

instance sparseThreadCarrierFormula_defined :
    ℒₛₑₜ-function₅[V] sparseThreadCarrier via sparseThreadCarrierFormula :=
  ⟨fun v ↦ by
    change sparseThreadCarrierFormula.Evalb v ↔
      v 0 = sparseThreadCarrier (v 1) (v 2) (v 3) (v 4) (v 5)
    rw [mem_ext_iff]
    simp [sparseThreadCarrierFormula, sparseThreadCarrier]⟩

instance sparseThreadDecodeValueFormula_defined :
    ℒₛₑₜ-function₃[V] sparseThreadDecodeValue via sparseThreadDecodeValueFormula :=
  ⟨fun v ↦ by
    change sparseThreadDecodeValueFormula.Evalb v ↔
      v 0 = sparseThreadDecodeValue (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [sparseThreadDecodeValueFormula, sparseThreadDecodeValue, mem_definableGraph_iff]⟩

instance sparseThreadDecodeFormula_defined :
    ℒₛₑₜ-function₅[V] sparseThreadDecode via sparseThreadDecodeFormula :=
  ⟨fun v ↦ by
    simp [sparseThreadDecodeFormula]
    rw [mem_ext_iff]
    simp [sparseThreadDecode, mem_definableGraph_iff]⟩

instance sparseThreadEncodeFormula_defined :
    ℒₛₑₜ-function₄[V] sparseThreadEncode via sparseThreadEncodeFormula :=
  ⟨fun v ↦ by
    change sparseThreadEncodeFormula.Evalb v ↔
      v 0 = sparseThreadEncode (v 1) (v 2) (v 3) (v 4)
    rw [mem_ext_iff]
    simp [sparseThreadEncodeFormula, sparseThreadEncode, mem_definableGraph_iff]⟩

instance sparseThreadOrderFormula_defined :
    ℒₛₑₜ-function₄[V] sparseThreadOrder via sparseThreadOrderFormula :=
  ⟨fun v ↦ by
    change sparseThreadOrderFormula.Evalb v ↔
      v 0 = sparseThreadOrder (v 1) (v 2) (v 3) (v 4)
    rw [mem_ext_iff]
    simp [sparseThreadOrderFormula, sparseThreadOrder]⟩

def sparseThreadDictionary : SetFormulaDictionary :=
  [⟨5, sparseRestrictionThreadsFormula⟩, ⟨6, sparseThreadCarrierFormula⟩,
   ⟨4, sparseThreadDecodeValueFormula⟩, ⟨6, sparseThreadDecodeFormula⟩,
   ⟨5, sparseThreadEncodeFormula⟩, ⟨5, sparseThreadOrderFormula⟩]

def sparseThreadDictionaryBound : ℕ := levyDictionaryBound sparseThreadDictionary

theorem sparseThreadDictionary_complexity {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ sparseThreadDictionary) (p : LevyPolarity) :
    IsLevyFormula p sparseThreadDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

end ZFVP
