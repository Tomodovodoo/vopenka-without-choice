import ZFVP.ModelTheory.ForcingRecodedSystem
import ZFVP.ModelTheory.ForcingCodeUniform
import ZFVP.ModelTheory.UniformSparsePair
import ZFVP.SetTheory.UniformFunctionOperations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingRecodedProjectionsFormula : SetTheorySemisentence 4 :=
  f“g θ s m. ∀ w, w ∈ g ↔ ∃ z ∈ !prod.dfn θ θ,
    w = !kpair.dfn z (!composeFormula
      (!composeFormula (!sparseConverseGraphFormula (!value.dfn m (!kpair.π₂.dfn z)))
        (!value.dfn (!forcingCodeπFormula s) z)) (!value.dfn m (!kpair.π₁.dfn z)))”

def forcingRecodedSectionsFormula : SetTheorySemisentence 4 :=
  f“g θ s m. ∀ w, w ∈ g ↔ ∃ z ∈ !prod.dfn θ θ,
    w = !kpair.dfn z (!composeFormula
      (!composeFormula (!sparseConverseGraphFormula (!value.dfn m (!kpair.π₁.dfn z)))
        (!value.dfn (!forcingCodeEFormula s) z)) (!value.dfn m (!kpair.π₂.dfn z)))”

def forcingRecodedLiftMapFormula : SetTheorySemisentence 5 :=
  f“g Q L m z. ∀ u, u ∈ g ↔
    ∃ w ∈ !prod.dfn (!value.dfn Q (!kpair.π₂.dfn z)) (!value.dfn Q (!kpair.π₁.dfn z)),
      u = !kpair.dfn w (!value.dfn (!value.dfn m (!kpair.π₂.dfn z))
        (!value.dfn (!value.dfn L z) (!kpair.dfn
          (!value.dfn (!sparseConverseGraphFormula (!value.dfn m (!kpair.π₂.dfn z))) (!kpair.π₁.dfn w))
          (!value.dfn (!sparseConverseGraphFormula (!value.dfn m (!kpair.π₁.dfn z))) (!kpair.π₂.dfn w)))))”

def forcingRecodedLiftsFormula : SetTheorySemisentence 5 :=
  f“g θ s Q m. ∀ w, w ∈ g ↔ ∃ z ∈ !prod.dfn θ θ,
    w = !kpair.dfn z (!forcingRecodedLiftMapFormula Q (!forcingCodeLFormula s) m z)”

def forcingRecodedTopsFormula : SetTheorySemisentence 4 :=
  f“g θ s m. ∀ w, w ∈ g ↔ ∃ i ∈ θ,
    w = !kpair.dfn i (!value.dfn (!value.dfn m i) (!value.dfn (!forcingCodetFormula s) i))”

def forcingRecodedCodeFormula : SetTheorySemisentence 6 :=
  f“z θ s Q T m. !forcingIterationCodeFormula z Q T
    (!forcingRecodedProjectionsFormula θ s m) (!forcingRecodedSectionsFormula θ s m)
    (!forcingRecodedLiftsFormula θ s Q m) (!forcingRecodedTopsFormula θ s m)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingRecodedProjectionsFormula_defined :
    ℒₛₑₜ-function₃[V] forcingRecodedProjections via forcingRecodedProjectionsFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingRecodedProjectionsFormula, forcingRecodedProjections, mem_definableGraph_iff]⟩

instance forcingRecodedSectionsFormula_defined :
    ℒₛₑₜ-function₃[V] forcingRecodedSections via forcingRecodedSectionsFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingRecodedSectionsFormula, forcingRecodedSections, mem_definableGraph_iff]⟩

instance forcingRecodedLiftMapFormula_defined :
    ℒₛₑₜ-function₄[V] forcingRecodedLiftMap via forcingRecodedLiftMapFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingRecodedLiftMapFormula, forcingRecodedLiftMap, mem_definableGraph_iff]⟩

instance forcingRecodedLiftsFormula_defined :
    ℒₛₑₜ-function₄[V] forcingRecodedLifts via forcingRecodedLiftsFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingRecodedLiftsFormula, forcingRecodedLifts, mem_definableGraph_iff]⟩

instance forcingRecodedTopsFormula_defined :
    ℒₛₑₜ-function₃[V] forcingRecodedTops via forcingRecodedTopsFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingRecodedTopsFormula, forcingRecodedTops, mem_definableGraph_iff]⟩

instance forcingRecodedCodeFormula_defined :
    ℒₛₑₜ-function₅[V] forcingRecodedCode via forcingRecodedCodeFormula :=
  ⟨fun v ↦ by simp [forcingRecodedCodeFormula, forcingRecodedCode]⟩

def forcingRecodedCodeDictionary : SetFormulaDictionary :=
  [⟨4, forcingRecodedProjectionsFormula⟩, ⟨4, forcingRecodedSectionsFormula⟩,
   ⟨5, forcingRecodedLiftMapFormula⟩, ⟨5, forcingRecodedLiftsFormula⟩,
   ⟨4, forcingRecodedTopsFormula⟩, ⟨6, forcingRecodedCodeFormula⟩]

def forcingRecodedCodeDictionaryBound : ℕ := levyDictionaryBound forcingRecodedCodeDictionary

theorem forcingRecodedCodeDictionary_complexity {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ forcingRecodedCodeDictionary) (p : LevyPolarity) :
    IsLevyFormula p forcingRecodedCodeDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

end ZFVP
