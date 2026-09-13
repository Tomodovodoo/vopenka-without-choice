import ZFVP.ModelTheory.WoodinSparseTranslationCoefficient
import ZFVP.ModelTheory.ClassForcingTranslationBound
import ZFVP.SetTheory.DomainTruthStructuralHeightPrimrec
import ZFVP.ModelTheory.WoodinSparseFiniteTruthWindow

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- A primitive-recursive bound for the finite sparse forcing truth window. -/
def woodinSparseSatLevelMajorant (k : ℕ) : ℕ :=
  woodinSparseTranslationCoefficient * (4 + 2 * domainTruthStructuralHeightBound k) + 1

theorem woodinSparseSatLevelMajorant_primrec : Primrec woodinSparseSatLevelMajorant :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const _)
      (Primrec.nat_add.comp (Primrec.const 4)
        (Primrec.nat_mul.comp (Primrec.const 2) domainTruthStructuralHeightBound_primrec)))
    (Primrec.const 1)

theorem woodinSparseForcingTranslation_syntacticBound_le {n : ℕ}
    (φ : SetTheorySemisentence n) :
    levySyntacticBound (woodinSparseForcingTranslation φ) ≤
      woodinSparseTranslationCoefficient * (n + 2 * formulaStructuralHeight φ + 1) :=
  ClassForcingDictionary.translation_syntacticBound_le woodinSparseForcingDictionary
    woodinSparseTranslationCoefficient_ge woodinSparseTranslationCoefficient_carrier
    woodinSparseTranslationCoefficient_order woodinSparseTranslationCoefficient_names
    woodinSparseAtomic_compiler_bound φ

private theorem height_bound (K h H : ℕ) (hh : h ≤ H) :
    K * (3 + 2 * h + 1) ≤ K * (4 + 2 * H) :=
  Nat.mul_le_mul_left K (by omega)

private theorem dictionary_bound (X Y B : ℕ) (hX : X ≤ B) (hY : Y ≤ B) :
    max X (max Y 0) + 1 ≤ B + 1 := by omega

theorem woodinSparseSatLevel_le_majorant (k : ℕ) :
    woodinSparseSatLevel k ≤ woodinSparseSatLevelMajorant k := by
  have hp := (woodinSparseForcingTranslation_syntacticBound_le
    (domainTruthFormula .sigma k)).trans
      (height_bound _ _ _ (domainTruthFormula_structuralHeight_le k))
  have hn := woodinSparseForcingTranslation_syntacticBound_le (∼domainTruthFormula .sigma k)
  simp only [formulaStructuralHeight_neg] at hn
  have hn' := hn.trans (height_bound _ _ _ (domainTruthFormula_structuralHeight_le k))
  simpa only [woodinSparseSatLevel, woodinSparseSatDictionary, levyDictionaryBound,
    woodinSparseSatLevelMajorant] using dictionary_bound _ _ _ hp hn'

end ZFVP
