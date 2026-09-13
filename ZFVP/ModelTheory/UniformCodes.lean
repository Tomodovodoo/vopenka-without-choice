import ZFVP.ModelTheory.ConstantStructure
import ZFVP.SetTheory.UniformRank

/-! Uniform first-order definitions of language and structure codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def languageCodeFormula : SetTheorySemisentence 5 :=
  f“L F R fa ra. L = !kpair.dfn F (!kpair.dfn R (!kpair.dfn fa ra))”
def functionSymbolsFormula : SetTheorySemisentence 2 := kpair.π₁.dfn
def relationSymbolsFormula : SetTheorySemisentence 2 :=
  f“R L. R = !kpair.π₁.dfn (!kpair.π₂.dfn L)”
def functionAritiesFormula : SetTheorySemisentence 2 :=
  f“fa L. fa = !kpair.π₁.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn L))”
def relationAritiesFormula : SetTheorySemisentence 2 :=
  f“ra L. ra = !kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn L))”

def isLanguageCodeFormula : SetTheorySemisentence 1 :=
  f“L. L = !languageCodeFormula (!functionSymbolsFormula L) (!relationSymbolsFormula L)
      (!functionAritiesFormula L) (!relationAritiesFormula L) ∧
    !functionAritiesFormula L ∈ !function.dfn (!isω) (!functionSymbolsFormula L) ∧
    !relationAritiesFormula L ∈ !function.dfn (!isω) (!relationSymbolsFormula L)”

def structureCodeFormula : SetTheorySemisentence 4 :=
  f“M A FI RI. M = !kpair.dfn A (!kpair.dfn FI RI)”
def structureDomainFormula : SetTheorySemisentence 2 := kpair.π₁.dfn
def structureFunctionsFormula : SetTheorySemisentence 2 := relationSymbolsFormula
def structureRelationsFormula : SetTheorySemisentence 2 :=
  f“RI M. RI = !kpair.π₂.dfn (!kpair.π₂.dfn M)”

def isStructureCodeFormula : SetTheorySemisentence 2 :=
  f“L M. !isLanguageCodeFormula L ∧
    M = !structureCodeFormula (!structureDomainFormula M) (!structureFunctionsFormula M)
      (!structureRelationsFormula M) ∧
    !isNonempty (!structureDomainFormula M) ∧
    !IsFunction.dfn (!structureFunctionsFormula M) ∧
      !domain.dfn (!structureFunctionsFormula M) = !functionSymbolsFormula L ∧
    !IsFunction.dfn (!structureRelationsFormula M) ∧
      !domain.dfn (!structureRelationsFormula M) = !relationSymbolsFormula L ∧
    (∀ f ∈ !functionSymbolsFormula L,
      !value.dfn (!structureFunctionsFormula M) f ∈
        !function.dfn (!structureDomainFormula M)
          (!function.dfn (!structureDomainFormula M) (!value.dfn (!functionAritiesFormula L) f))) ∧
    ∀ r ∈ !relationSymbolsFormula L,
      !value.dfn (!structureRelationsFormula M) r ⊆
        !function.dfn (!structureDomainFormula M) (!value.dfn (!relationAritiesFormula L) r)”

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance languageCodeFormula_defined : ℒₛₑₜ-function₄[V] languageCode via languageCodeFormula :=
  ⟨fun v ↦ by simp [languageCodeFormula, languageCode]⟩
instance functionSymbolsFormula_defined :
    ℒₛₑₜ-function₁[V] functionSymbols via functionSymbolsFormula := kpair.π₁.defined
instance relationSymbolsFormula_defined :
    ℒₛₑₜ-function₁[V] relationSymbols via relationSymbolsFormula :=
  ⟨fun v ↦ by simp [relationSymbolsFormula, relationSymbols]⟩
instance functionAritiesFormula_defined :
    ℒₛₑₜ-function₁[V] functionArities via functionAritiesFormula :=
  ⟨fun v ↦ by simp [functionAritiesFormula, functionArities]⟩
instance relationAritiesFormula_defined :
    ℒₛₑₜ-function₁[V] relationArities via relationAritiesFormula :=
  ⟨fun v ↦ by simp [relationAritiesFormula, relationArities]⟩
instance isLanguageCodeFormula_defined :
    ℒₛₑₜ-predicate[V] IsLanguageCode via isLanguageCodeFormula :=
  ⟨fun v ↦ by simp [isLanguageCodeFormula, IsLanguageCode]⟩
instance structureCodeFormula_defined : ℒₛₑₜ-function₃[V] structureCode via structureCodeFormula :=
  ⟨fun v ↦ by simp [structureCodeFormula, structureCode]⟩
instance structureDomainFormula_defined :
    ℒₛₑₜ-function₁[V] structureDomain via structureDomainFormula := kpair.π₁.defined
instance structureFunctionsFormula_defined :
    ℒₛₑₜ-function₁[V] structureFunctions via structureFunctionsFormula := relationSymbolsFormula_defined
instance structureRelationsFormula_defined :
    ℒₛₑₜ-function₁[V] structureRelations via structureRelationsFormula :=
  ⟨fun v ↦ by simp [structureRelationsFormula, structureRelations]⟩
instance isStructureCodeFormula_defined :
    ℒₛₑₜ-relation[V] IsStructureCode via isStructureCodeFormula :=
  ⟨fun v ↦ by simp [isStructureCodeFormula, IsStructureCode]⟩

theorem ElementaryMap.map_languageCode_iff (j : ElementaryMap V W) (L : V) :
    IsLanguageCode (j L) ↔ IsLanguageCode L :=
  (j.map_defined isLanguageCodeFormula (fun v ↦ IsLanguageCode (v 0))
    (fun v ↦ IsLanguageCode (v 0)) ![L]).symm

theorem ElementaryMap.map_structureCode_iff (j : ElementaryMap V W) (L M : V) :
    IsStructureCode (j L) (j M) ↔ IsStructureCode L M :=
  (j.map_defined isStructureCodeFormula (fun v ↦ IsStructureCode (v 0) (v 1))
    (fun v ↦ IsStructureCode (v 0) (v 1)) ![L, M]).symm

end ZFVP
