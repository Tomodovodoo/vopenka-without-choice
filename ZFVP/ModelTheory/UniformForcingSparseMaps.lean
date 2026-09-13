import ZFVP.ModelTheory.UniformNormalizationMaps
import ZFVP.ModelTheory.UniformSparsePair
import ZFVP.ModelTheory.ForcingRecodedSparse
import ZFVP.ModelTheory.ForcingLimitUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sparseMinimalSectionPointFormula : SetTheorySemisentence 4 :=
  f“P E k p. p ∈ !value.dfn P k ∧ ∀ j ∈ k, ∀ q ∈ !value.dfn P j,
    p ≠ !value.dfn (!value.dfn E (!kpair.dfn j k)) q”

def forcingSparseCodesFormula : SetTheorySemisentence 4 :=
  f“C θ s U. ∀ a, a ∈ C ↔ a ∈ !prod.dfn θ U ∧
    !sparseMinimalSectionPointFormula (!forcingCodePFormula s) (!forcingCodeEFormula s)
      (!kpair.π₁.dfn a) (!kpair.π₂.dfn a)”

def forcingSparseDecodeValueFormula : SetTheorySemisentence 4 :=
  “z θ s a. ∃ π, ∃ E, ∃ k, ∃ p, !forcingCodeπFormula π s ∧ !forcingCodeEFormula E s ∧
    !kpair.π₁.dfn k a ∧ !kpair.π₂.dfn p a ∧ !forcingSectionThreadFormula z θ π E k p”

def forcingSparseDecodeFormula : SetTheorySemisentence 4 :=
  f“f θ s U. ∀ z, z ∈ f ↔ ∃ a ∈ !forcingSparseCodesFormula θ s U,
    z = !kpair.dfn a (!forcingSparseDecodeValueFormula θ s a)”

def forcingSparseEncodeFormula : SetTheorySemisentence 4 :=
  f“f θ s U. !sparseConverseGraphFormula f (!forcingSparseDecodeFormula θ s U)”

def forcingSparseOrderFormula : SetTheorySemisentence 4 :=
  “T θ s U. ∃ P, ∃ R, ∃ π, ∃ E, ∃ D, ∃ S, ∃ C, ∃ f,
    !forcingCodePFormula P s ∧ !forcingCodeRFormula R s ∧ !forcingCodeπFormula π s ∧
    !forcingCodeEFormula E s ∧ !forcingDirectLimitFormula D θ P π E U ∧
    !forcingThreadOrderFormula S θ R D ∧ !forcingSparseCodesFormula C θ s U ∧
    !forcingSparseDecodeFormula f θ s U ∧ !sparsePullbackOrderFormula T C S f”

def forcingRecodedSparseMapFormula : SetTheorySemisentence 6 :=
  “f θ s z m U. ∃ P, ∃ π, ∃ E, ∃ D, ∃ a, ∃ W, ∃ e,
    !forcingCodePFormula P s ∧ !forcingCodeπFormula π s ∧ !forcingCodeEFormula E s ∧
    !forcingDirectLimitFormula D θ P π E U ∧ !forcingThreadActionMapFormula a θ m D ∧
    !forcingCodeUniverseFormula W z ∧ !forcingSparseEncodeFormula e θ z W ∧ !composeFormula f a e”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sparseMinimalSectionPointFormula_defined :
    ℒₛₑₜ-relation₄[V] IsMinimalSectionPoint via sparseMinimalSectionPointFormula :=
  ⟨fun v ↦ by simp [sparseMinimalSectionPointFormula, IsMinimalSectionPoint]⟩

instance forcingSparseCodesFormula_defined :
    ℒₛₑₜ-function₃[V] forcingSparseCodes via forcingSparseCodesFormula :=
  ⟨fun v ↦ by
    change forcingSparseCodesFormula.Evalb v ↔ v 0 = forcingSparseCodes (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [forcingSparseCodesFormula, forcingSparseCodes, forcingMinimalSupportCodes]⟩

instance forcingSparseDecodeValueFormula_defined :
    ℒₛₑₜ-function₃[V] (fun θ s a ↦
      forcingMinimalSupportDecode θ (forcingCodeπ s) (forcingCodeE s) a)
      via forcingSparseDecodeValueFormula :=
  ⟨fun v ↦ by simp [forcingSparseDecodeValueFormula, forcingMinimalSupportDecode]⟩

instance forcingSparseDecodeFormula_defined :
    ℒₛₑₜ-function₃[V] forcingSparseDecode via forcingSparseDecodeFormula :=
  ⟨fun v ↦ by
    change forcingSparseDecodeFormula.Evalb v ↔ v 0 = forcingSparseDecode (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [forcingSparseDecodeFormula, forcingSparseDecode, forcingMinimalSupportMap,
      forcingSparseCodes, mem_definableGraph_iff]⟩

instance forcingSparseEncodeFormula_defined :
    ℒₛₑₜ-function₃[V] forcingSparseEncode via forcingSparseEncodeFormula :=
  ⟨fun v ↦ by simp [forcingSparseEncodeFormula, forcingSparseEncode]⟩

instance forcingSparseOrderFormula_defined :
    ℒₛₑₜ-function₃[V] forcingSparseOrder via forcingSparseOrderFormula :=
  ⟨fun v ↦ by simp [forcingSparseOrderFormula, forcingSparseOrder]⟩

instance forcingRecodedSparseMapFormula_defined :
    ℒₛₑₜ-function₅[V] forcingRecodedSparseMap via forcingRecodedSparseMapFormula :=
  ⟨fun v ↦ by simp [forcingRecodedSparseMapFormula, forcingRecodedSparseMap]⟩

def forcingSparseMapsDictionary : SetFormulaDictionary :=
  [⟨4, sparseMinimalSectionPointFormula⟩, ⟨4, forcingSparseCodesFormula⟩,
   ⟨4, forcingSparseDecodeValueFormula⟩, ⟨4, forcingSparseDecodeFormula⟩,
   ⟨4, forcingSparseEncodeFormula⟩, ⟨4, forcingSparseOrderFormula⟩,
   ⟨6, forcingRecodedSparseMapFormula⟩]

def forcingSparseMapsDictionaryBound : ℕ := levyDictionaryBound forcingSparseMapsDictionary

theorem forcingSparseMapsDictionary_complexity {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ forcingSparseMapsDictionary) (p : LevyPolarity) :
    IsLevyFormula p forcingSparseMapsDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

end ZFVP
