import ZFVP.ModelTheory.SparsePairPresentation
import ZFVP.SetTheory.LevyComplexityBound

/-! Fixed membership-language syntax for sparse pairs and their order pullback. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def isSparseFunctionOnFormula : SetTheorySemisentence 2 :=
  f“A p. !IsFunction.dfn p ∧ !domain.dfn p ⊆ A ∧
    ∀ x ∈ !domain.dfn p, ¬!isEmpty (!value.dfn p x)”

def sparsePairCarrierFormula : SetTheorySemisentence 4 :=
  f“C a P W. ∀ q, q ∈ C ↔ !isSparseFunctionOnFormula (!succ.dfn a) q ∧
    !restrict.dfn q a ∈ P ∧ !value.dfn q a ∈ W”

def sparsePairDecodeValueFormula : SetTheorySemisentence 3 :=
  f“z a q. z = !kpair.dfn (!restrict.dfn q a) (!value.dfn q a)”

def sparsePairDecodeFormula : SetTheorySemisentence 4 :=
  f“f a P W. ∀ z, z ∈ f ↔ ∃ q ∈ !sparsePairCarrierFormula a P W,
    z = !kpair.dfn q (!sparsePairDecodeValueFormula a q)”

def sparseConverseGraphFormula : SetTheorySemisentence 2 :=
  f“g f. ∀ p, p ∈ g ↔ p ∈ !prod.dfn (!range.dfn f) (!domain.dfn f) ∧
    !kpair.dfn (!kpair.π₂.dfn p) (!kpair.π₁.dfn p) ∈ f”

def sparsePairEncodeFormula : SetTheorySemisentence 4 :=
  f“f a P W. !sparseConverseGraphFormula f (!sparsePairDecodeFormula a P W)”

def sparsePullbackOrderFormula : SetTheorySemisentence 4 :=
  f“T Q R π. ∀ z, z ∈ T ↔ z ∈ !prod.dfn Q Q ∧
    !kpair.dfn (!value.dfn π (!kpair.π₁.dfn z)) (!value.dfn π (!kpair.π₂.dfn z)) ∈ R”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance isSparseFunctionOnFormula_defined :
    ℒₛₑₜ-relation[V] IsSparseFunctionOn via isSparseFunctionOnFormula :=
  ⟨fun v ↦ by simp [isSparseFunctionOnFormula, IsSparseFunctionOn, isEmpty_iff_eq_empty]⟩

instance sparsePairCarrierFormula_defined :
    ℒₛₑₜ-function₃[V] sparsePairCarrier via sparsePairCarrierFormula :=
  ⟨fun v ↦ by
    change sparsePairCarrierFormula.Evalb v ↔ v 0 = sparsePairCarrier (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [sparsePairCarrierFormula, mem_sparsePairCarrier_iff]⟩

instance sparsePairDecodeValueFormula_defined :
    ℒₛₑₜ-function₂[V] sparsePairDecodeValue via sparsePairDecodeValueFormula :=
  ⟨fun v ↦ by simp [sparsePairDecodeValueFormula, sparsePairDecodeValue]⟩

instance sparsePairDecodeFormula_defined :
    ℒₛₑₜ-function₃[V] sparsePairDecode via sparsePairDecodeFormula :=
  ⟨fun v ↦ by
    change sparsePairDecodeFormula.Evalb v ↔ v 0 = sparsePairDecode (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [sparsePairDecodeFormula, sparsePairDecode, mem_definableGraph_iff]⟩

instance sparseConverseGraphFormula_defined :
    ℒₛₑₜ-function₁[V] converseGraph via sparseConverseGraphFormula :=
  ⟨fun v ↦ by
    change sparseConverseGraphFormula.Evalb v ↔ v 0 = converseGraph (v 1)
    rw [mem_ext_iff]
    simp [sparseConverseGraphFormula, converseGraph]⟩

instance sparsePairEncodeFormula_defined :
    ℒₛₑₜ-function₃[V] sparsePairEncode via sparsePairEncodeFormula :=
  ⟨fun v ↦ by simp [sparsePairEncodeFormula, sparsePairEncode]⟩

instance sparsePullbackOrderFormula_defined :
    ℒₛₑₜ-function₃[V] forcingPullbackOrder via sparsePullbackOrderFormula :=
  ⟨fun v ↦ by
    change sparsePullbackOrderFormula.Evalb v ↔ v 0 = forcingPullbackOrder (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [sparsePullbackOrderFormula, forcingPullbackOrder]⟩

def sparsePairDictionary : SetFormulaDictionary :=
  [⟨2, isSparseFunctionOnFormula⟩, ⟨4, sparsePairCarrierFormula⟩,
   ⟨3, sparsePairDecodeValueFormula⟩, ⟨4, sparsePairDecodeFormula⟩,
   ⟨2, sparseConverseGraphFormula⟩, ⟨4, sparsePairEncodeFormula⟩,
   ⟨4, sparsePullbackOrderFormula⟩]

def sparsePairDictionaryBound : ℕ := levyDictionaryBound sparsePairDictionary

theorem sparsePairDictionary_complexity {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ sparsePairDictionary) (p : LevyPolarity) :
    IsLevyFormula p sparsePairDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

end ZFVP
