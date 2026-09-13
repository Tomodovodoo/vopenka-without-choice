import ZFVP.ModelTheory.BinaryRelationRepresentation
import ZFVP.ModelTheory.CodedZFModel
import ZFVP.Syntax.TemplateInstantiation
import ZFVP.Syntax.CloseTailParameters

/-! Full internal ZF truth implies standard ZF truth for an arbitrary relation.
The standard fragment quantifies over external formulas only; no converse to
full internal schema satisfaction is asserted without a standardness hypothesis. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- This external predicate tests only standard ZF axiom codes. Its quantifier
over Lean formulas does not cover nonstandard internal Separation/Replacement. -/
def StandardCodedZFTruth (C : V) : Prop :=
  IsStructureCode membershipLanguageCode C ∧ ∀ φ : SetTheorySentence, φ ∈ 𝗭𝗙 →
    Satisfies membershipLanguageCode ∅ C ∅ 0 (encodeMembershipFormula φ) ∅

namespace BinaryRelationRepresentation

variable {M : Type*} [SetStructure M] [Nonempty M] (R : BinaryRelationRepresentation (V := V) M)

theorem satisfies_sentence_iff (φ : SetTheorySentence) :
    Satisfies membershipLanguageCode ∅ R.code ∅ 0 (encodeMembershipFormula φ) ∅ ↔
      M↓[ℒₛₑₜ] ⊧ φ := by
  have he := R.satisfies_iff φ (![] : Fin 0 → M)
  have hzero : ((0 : ℕ) : V) = (0 : V) := rfl
  rw [hzero] at he
  simpa only [standardTuple, models_iff, Semiformula.Realize, Semiformula.Evalb] using he

theorem standardCodedZFTruth_iff : StandardCodedZFTruth R.code ↔ M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  constructor
  · intro h
    exact ⟨fun φ hφ ↦ (R.satisfies_sentence_iff φ).mp (h.2 φ hφ)⟩
  · intro h
    let := h
    exact ⟨R.code_valid, fun φ hφ ↦ (R.satisfies_sentence_iff φ).mpr (Theory.models M 𝗭𝗙 hφ)⟩

omit [Nonempty M] in
theorem codedZF_separation_template (h : IsCodedZFModel R.code)
    (k : ℕ) (φ : SetTheorySemisentence (k + 1)) (b : Fin k → M) :
    (separationTemplate.instantiateTail k φ).Evalb b := by
  have hφ : IsMembershipFormulaCode (succ (k : V)) (encodeMembershipFormula φ) := by
    simpa only [IsMembershipFormulaCode, num_succ_def] using
      (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem (V := V) φ)
  have hb : standardTuple (fun i ↦ (R.equiv (b i)).val) ∈ structureDomain R.code ^ (k : V) := by
    simpa only [code, binaryRelationStructureCode_domain] using
      standardTuple_mem_function (fun i ↦ (R.equiv (b i)).val) (fun i ↦ (R.equiv (b i)).property)
  have ht := h.separation (by simp) hφ hb
  rw [separationCode, MembershipTemplate.compileTail_encode] at ht
  exact (R.satisfies_iff _ b).mp ht

omit [Nonempty M] in
theorem codedZF_replacement_template (h : IsCodedZFModel R.code)
    (k : ℕ) (φ : SetTheorySemisentence (k + 2)) (b : Fin k → M) :
    (replacementTemplate.instantiateTail k φ).Evalb b := by
  have hφ : IsMembershipFormulaCode (succ (succ (k : V))) (encodeMembershipFormula φ) := by
    simpa only [IsMembershipFormulaCode, num_succ_def] using
      (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem (V := V) φ)
  have hb : standardTuple (fun i ↦ (R.equiv (b i)).val) ∈ structureDomain R.code ^ (k : V) := by
    simpa only [code, binaryRelationStructureCode_domain] using
      standardTuple_mem_function (fun i ↦ (R.equiv (b i)).val) (fun i ↦ (R.equiv (b i)).property)
  have ht := h.replacement (by simp) hφ hb
  rw [replacementCode, MembershipTemplate.compileTail_encode] at ht
  exact (R.satisfies_iff _ b).mp ht

theorem codedZF_models_separation (h : IsCodedZFModel R.code) (φ : SetTheorySemiproposition 1) :
    M↓[ℒₛₑₜ] ⊧ Axiom.separationSchema φ := by
  simp [models_iff, Axiom.separationSchema, Semiformula.eval_univCl]
  intro e a
  have ht := (MembershipTemplate.eval_instantiateTail (closeTailParameters φ) separationTemplate
    (![] : Fin 0 → M) (fun i : Fin φ.fvSup ↦ e i.val)).mp
      (R.codedZF_separation_template h φ.fvSup (closeTailParameters φ) _)
  obtain ⟨c, hc⟩ := (eval_separationTemplate _).mp ht a
  refine ⟨c, fun x ↦ ?_⟩
  exact (hc x).trans (and_congr Iff.rfl (eval_closeTailParameters φ ![x] e))

theorem codedZF_models_replacement (h : IsCodedZFModel R.code) (φ : SetTheorySemiproposition 2) :
    M↓[ℒₛₑₜ] ⊧ Axiom.replacementSchema φ := by
  simp [models_iff, Axiom.replacementSchema, Semiformula.eval_univCl]
  intro e hf a
  have ht := (MembershipTemplate.eval_instantiateTail (closeTailParameters φ) replacementTemplate
    (![] : Fin 0 → M) (fun i : Fin φ.fvSup ↦ e i.val)).mp
      (R.codedZF_replacement_template h φ.fvSup (closeTailParameters φ) _)
  have he (x y : M) := eval_closeTailParameters φ ![x, y] e
  have hhf : ∀ x : M, x ∈ a → ∃! y : M,
      (closeTailParameters φ).Evalb (prefixVector ![x, y] (fun i : Fin φ.fvSup ↦ e i.val)) := by
    intro x _
    obtain ⟨y, hy, hu⟩ := hf x
    exact ⟨y, (he x y).mpr hy, fun z hz ↦ hu z ((he x z).mp hz)⟩
  obtain ⟨c, hc⟩ := (eval_replacementTemplate _).mp ht a hhf
  refine ⟨c, fun y ↦ ?_⟩
  exact (hc y).trans (exists_congr (fun x ↦ and_congr Iff.rfl (he x y)))

theorem models_zf_of_isCodedZFModel (h : IsCodedZFModel R.code) : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  have hf (φ : SetTheorySentence) (hφ : encodeMembershipFormula φ ∈ (fixedZFSentenceCodes : V)) :
      M↓[ℒₛₑₜ] ⊧ φ := (R.satisfies_sentence_iff φ).mp (h.fixed hφ)
  refine ⟨?_⟩
  intro φ hφ
  cases hφ with
  | axiom_of_equality φ hφ => exact Theory.models M (𝗘𝗤 ℒₛₑₜ) hφ
  | axiom_of_empty_set => exact hf _ (by simp [fixedZFSentenceCodes])
  | axiom_of_extentionality => exact hf _ (by simp [fixedZFSentenceCodes])
  | axiom_of_pairing => exact hf _ (by simp [fixedZFSentenceCodes])
  | axiom_of_union => exact hf _ (by simp [fixedZFSentenceCodes])
  | axiom_of_power_set => exact hf _ (by simp [fixedZFSentenceCodes])
  | axiom_of_infinity => exact hf _ (by simp [fixedZFSentenceCodes])
  | axiom_of_foundation => exact hf _ (by simp [fixedZFSentenceCodes])
  | axiom_of_separation φ => exact R.codedZF_models_separation h φ
  | axiom_of_replacement φ => exact R.codedZF_models_replacement h φ

theorem standardCodedZFTruth_of_isCodedZFModel (h : IsCodedZFModel R.code) :
    StandardCodedZFTruth R.code := R.standardCodedZFTruth_iff.mpr (R.models_zf_of_isCodedZFModel h)

end BinaryRelationRepresentation

end ZFVP
