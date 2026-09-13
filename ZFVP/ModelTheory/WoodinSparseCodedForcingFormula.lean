import ZFVP.SetTheory.SourceNestedQuantifierBound
import ZFVP.ModelTheory.WoodinSparseSourceTruthWindow
import ZFVP.ModelTheory.ForcingSequenceNameDictionary

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- A condition-independent code for polarity, arity, and formula. -/
noncomputable def woodinForcingCode {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (p : LevyPolarity) (n φ : V) : V :=
  ⟨(match p with | .sigma => ∅ | .pi => succ ∅), ⟨n, φ⟩ₖ⟩ₖ

/-- The source W05 formula on a condition, a fixed formula code, and a sequence
of parameter names. The code's polarity is independent of the condition.
Canonical check and tuple names are part of the expanded formula. -/
def woodinCodedForcingFormula (k : ℕ) : SetTheorySemisentence 3 :=
  f“p c s. ∃ d n e u v b,
    c = !kpair.dfn d (!kpair.dfn n e) ∧
    !checkNameFormula u (!isEmpty) n ∧ !checkNameFormula v (!isEmpty) e ∧
    !sequenceNameFormula b (!isEmpty) s ∧
    ((d = !isEmpty ∧ !(woodinSparseForcingTranslation (domainTruthFormula .sigma k)) p u v b) ∨
      (d = !succ.dfn (!isEmpty) ∧ !(woodinSparseForcingTranslation (domainTruthFormula .pi k)) p u v b) ∨
      (d ≠ !isEmpty ∧ d ≠ !succ.dfn (!isEmpty) ∧
        !(woodinSparseForcingTranslation (∼domainTruthFormula .sigma k)) p u v b))”

/-- The literal source recipe applied after all graph substitutions. -/
def woodinCodedForcingLevel (k : ℕ) : ℕ := sourceQuantifierCount (woodinCodedForcingFormula k) + 3

theorem woodinCodedForcingLevel_literal (k : ℕ) :
    woodinCodedForcingLevel k = sourceQuantifierCount (woodinCodedForcingFormula k) + 3 :=
  rfl

theorem woodinCodedForcingLevel_source (k : ℕ) :
    woodinCodedForcingLevel k = sourceSingletonBound (woodinCodedForcingFormula k) :=
  (sourceSingletonBound_eq _).symm

theorem woodinCodedForcingTranslation_complexity (k : ℕ) :
    IsSigmaFormula (woodinCodedForcingLevel k)
      (woodinSparseForcingTranslation (domainTruthFormula .sigma k)) ∧
    IsSigmaFormula (woodinCodedForcingLevel k)
      (woodinSparseForcingTranslation (∼domainTruthFormula .sigma k)) := by
  have hbound : sourceQuantifierCount (woodinSparseForcingTranslation (domainTruthFormula .sigma k)) +
      sourceQuantifierCount (woodinSparseForcingTranslation (∼domainTruthFormula .sigma k)) ≤
      sourceQuantifierCount (woodinCodedForcingFormula k) := by
    have hpos := sourceQuantifierCount_le_nestFormulae
      (woodinSparseForcingTranslation (domainTruthFormula .sigma k))
      (![“#0 = #7”, “#0 = #3”, “#0 = #2”, “#0 = #1”] : Fin 4 → SetTheorySemisentence 10)
    have hneg := sourceQuantifierCount_le_nestFormulae
      (woodinSparseForcingTranslation (∼domainTruthFormula .sigma k))
      (![“#0 = #7”, “#0 = #3”, “#0 = #2”, “#0 = #1”] : Fin 4 → SetTheorySemisentence 10)
    simp only [woodinCodedForcingFormula, sourceQuantifierCount]
    omega
  constructor
  · exact (isLevyFormula_sourceQuantifierCount _ .sigma).mono (by rw [woodinCodedForcingLevel_literal]; omega)
  · exact (isLevyFormula_sourceQuantifierCount _ .sigma).mono (by rw [woodinCodedForcingLevel_literal]; omega)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_woodinCodedForcingFormula (k : ℕ) (pol : LevyPolarity) (p n φ s : V) :
    (woodinCodedForcingFormula k).Evalb ![p, woodinForcingCode pol n φ, s] ↔
      (woodinSparseForcingTranslation (domainTruthFormula pol k)).Evalb
        ![p, checkName ∅ n, checkName ∅ φ, sequenceName ∅ s] := by
  have he : (woodinCodedForcingFormula k).Evalb ![p, woodinForcingCode pol n φ, s] ↔
      ∃ d n' e u v b : V,
        woodinForcingCode pol n φ = ⟨d, ⟨n', e⟩ₖ⟩ₖ ∧
        u = checkName ∅ n' ∧ v = checkName ∅ e ∧ b = sequenceName ∅ s ∧
        ((d = ∅ ∧ (woodinSparseForcingTranslation (domainTruthFormula .sigma k)).Evalb ![p,u,v,b]) ∨
          (d = succ ∅ ∧ (woodinSparseForcingTranslation (domainTruthFormula .pi k)).Evalb ![p,u,v,b]) ∨
          (d ≠ ∅ ∧ d ≠ succ ∅ ∧ (woodinSparseForcingTranslation (∼domainTruthFormula .sigma k)).Evalb ![p,u,v,b])) := by
    simp [woodinCodedForcingFormula]
  rw [he]
  have h10 : succ (∅ : V) ≠ ∅ := by
    intro hz
    have hh := mem_succ_self (∅ : V)
    rw [hz] at hh
    exact not_mem_empty hh
  cases pol <;> simp [woodinForcingCode, kpair_iff, h10]

end ZFVP






