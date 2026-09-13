import ZFVP.SetTheory.LevyComplexityBound
import ZFVP.Syntax.UniformLevyCodes
import ZFVP.Syntax.UniformNegation

/-! Checked upper bounds for the fixed syntax and low-truth dictionaries. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def coreSyntaxDictionary : SetFormulaDictionary :=
  [⟨_, languageCodeFormula⟩, ⟨_, isLanguageCodeFormula⟩,
   ⟨_, structureCodeFormula⟩, ⟨_, isStructureCodeFormula⟩,
   ⟨_, termSetFormula⟩, ⟨_, formulaFamilyFormula⟩,
   ⟨_, satisfactionGraphFormula⟩, ⟨_, satisfiesFormula⟩,
   ⟨_, membershipStructureCodeFormula⟩, ⟨_, membershipSatisfiesFormula⟩,
   ⟨_, isBoundedFormulaCodeFormula⟩,
   ⟨_, formulaNegationGraphFormula⟩, ⟨_, negateFormulaFormula⟩]

def coreSyntaxDictionaryBound : ℕ := levyDictionaryBound coreSyntaxDictionary

theorem coreSyntaxDictionary_complexity {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ coreSyntaxDictionary) (p : LevyPolarity) :
    IsLevyFormula p coreSyntaxDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

def lowTruthDictionary : SetFormulaDictionary :=
  [⟨3, boundedTruthFormula⟩, ⟨3, sigmaOneTruthFormula⟩, ⟨3, piOneTruthFormula⟩]

def lowTruthDictionaryBound : ℕ := levyDictionaryBound lowTruthDictionary

theorem boundedTruthFormula_complexity (p : LevyPolarity) :
    IsLevyFormula p lowTruthDictionaryBound boundedTruthFormula :=
  isLevyFormula_dictionaryBound lowTruthDictionary (by simp [lowTruthDictionary]) p

theorem sigmaOneTruthFormula_complexity (p : LevyPolarity) :
    IsLevyFormula p lowTruthDictionaryBound sigmaOneTruthFormula :=
  isLevyFormula_dictionaryBound lowTruthDictionary (by simp [lowTruthDictionary]) p

theorem piOneTruthFormula_complexity (p : LevyPolarity) :
    IsLevyFormula p lowTruthDictionaryBound piOneTruthFormula :=
  isLevyFormula_dictionaryBound lowTruthDictionary (by simp [lowTruthDictionary]) p

def levyCodeDefinitionBound (p : LevyPolarity) (k : ℕ) : ℕ :=
  levySyntacticBound (isLevyFormulaCodeFormula p k)

theorem levyFormulaCodeFormula_complexity (p : LevyPolarity) (k : ℕ) (q : LevyPolarity) :
    IsLevyFormula q (levyCodeDefinitionBound p k) (isLevyFormulaCodeFormula p k) :=
  isLevyFormula_syntacticBound _ q

theorem coreSyntaxDictionary_substitution_complexity {n m : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ coreSyntaxDictionary) (p : LevyPolarity)
    (ts : Fin n → SetTheorySemiterm Empty m) :
    IsLevyFormula p coreSyntaxDictionaryBound (φ.subst ts) :=
  isLevyFormula_dictionary_substitution coreSyntaxDictionary hφ p ts

end ZFVP
