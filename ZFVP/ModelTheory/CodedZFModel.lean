import ZFVP.Syntax.ZFOpenAxiomSet
import ZFVP.Syntax.InternalUniversalClosure
import ZFVP.ModelTheory.CodedElementaryEmbedding

/-! Full internally coded ZF models for arbitrary structure codes. The schema
quantifiers range over all internal formula codes and all internal assignments. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def SatisfiesCodedOpenTheory (L M T : V) : Prop :=
  IsStructureCode L M ∧ ∀ n φ, ⟨n, φ⟩ₖ ∈ T → φ ∈ formulaSet L ∅ n ∧
    ∀ b ∈ structureDomain M ^ n, Satisfies L ∅ M ∅ n φ b

def satisfiesCodedOpenTheoryFormula : SetTheorySemisentence 3 :=
  f“L M T. !isStructureCodeFormula L M ∧ ∀ n φ, !kpair.dfn n φ ∈ T →
    φ ∈ !formulaSetFormula L (!isEmpty) n ∧
      ∀ b ∈ !function.dfn (!structureDomainFormula M) n,
        !satisfiesFormula L (!isEmpty) M (!isEmpty) n φ b”

instance satisfiesCodedOpenTheoryFormula_defined :
    ℒₛₑₜ-relation₃[V] SatisfiesCodedOpenTheory via satisfiesCodedOpenTheoryFormula :=
  ⟨fun v ↦ by simp [satisfiesCodedOpenTheoryFormula, SatisfiesCodedOpenTheory]⟩

instance satisfiesCodedOpenTheory_definable : ℒₛₑₜ-relation₃[V] SatisfiesCodedOpenTheory :=
  satisfiesCodedOpenTheoryFormula_defined.to_definable

namespace IsCodedElementaryEmbedding

theorem sentence_iff {L M N f φ : V} (h : IsCodedElementaryEmbedding L M N f)
    (hφ : φ ∈ formulaSet L ∅ 0) :
    Satisfies L ∅ M ∅ 0 φ ∅ ↔ Satisfies L ∅ N ∅ 0 φ ∅ := by
  have hs := h.satisfies_iff (by simp) hφ
    (show (∅ : V) ∈ structureDomain M ^ (0 : V) by simp [mem_function_iff, zero_def])
  simpa only [graph_empty_compose] using hs

/-- Universal closure transfers truth at every target assignment, including
parameters outside the image of a non-surjective elementary embedding. -/
theorem all_assignments_iff {L M N f n φ : V} (h : IsCodedElementaryEmbedding L M N f)
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet L ∅ n) :
    (∀ b ∈ structureDomain M ^ n, Satisfies L ∅ M ∅ n φ b) ↔
      ∀ b ∈ structureDomain N ^ n, Satisfies L ∅ N ∅ n φ b := by
  rw [← internalAllClosureCode_satisfies_iff h.source.language hn hφ,
    ← internalAllClosureCode_satisfies_iff h.target.language hn hφ]
  exact h.sentence_iff (internalAllClosureCode_sentence_valid h.source.language hn hφ)

theorem satisfiesCodedOpenTheory_iff {L M N f T : V} (h : IsCodedElementaryEmbedding L M N f) :
    SatisfiesCodedOpenTheory L M T ↔ SatisfiesCodedOpenTheory L N T := by
  constructor
  · rintro ⟨_, hM⟩
    refine ⟨h.target, fun n φ hφ ↦ ?_⟩
    obtain ⟨hv, hs⟩ := hM n φ hφ
    exact ⟨hv, (h.all_assignments_iff (formulaSet_context h.source.language hv) hv).mp hs⟩
  · rintro ⟨_, hN⟩
    refine ⟨h.source, fun n φ hφ ↦ ?_⟩
    obtain ⟨hv, hs⟩ := hN n φ hφ
    exact ⟨hv, (h.all_assignments_iff (formulaSet_context h.source.language hv) hv).mpr hs⟩

end IsCodedElementaryEmbedding

/-- This is the existing complete internal axiom set, evaluated in an arbitrary
structure code rather than the ambient-membership structure of its carrier. -/
def IsCodedZFModel (M : V) : Prop := SatisfiesCodedOpenTheory membershipLanguageCode M zfOpenAxiomCodes

instance isCodedZFModel_definable : ℒₛₑₜ-predicate[V] IsCodedZFModel := by
  unfold IsCodedZFModel
  definability

namespace IsCodedZFModel

theorem valid {M : V} (h : IsCodedZFModel M) : IsStructureCode membershipLanguageCode M := h.1

theorem satisfies_axiom {M n φ b : V} (h : IsCodedZFModel M) (hφ : IsZFOpenAxiom n φ)
    (hb : b ∈ structureDomain M ^ n) : Satisfies membershipLanguageCode ∅ M ∅ n φ b :=
  (h.2 n φ ((mem_zfOpenAxiomCodes_iff n φ).mpr hφ)).2 b hb

theorem fixed {M φ : V} (h : IsCodedZFModel M) (hφ : φ ∈ (fixedZFSentenceCodes : V)) :
    Satisfies membershipLanguageCode ∅ M ∅ 0 φ ∅ :=
  h.satisfies_axiom (Or.inl ⟨rfl, hφ⟩) (by simp [mem_function_iff, zero_def])

theorem separation {M n φ b : V} (h : IsCodedZFModel M) (hn : n ∈ (ω : V))
    (hφ : IsMembershipFormulaCode (succ n) φ) (hb : b ∈ structureDomain M ^ n) :
    Satisfies membershipLanguageCode ∅ M ∅ n (separationCode n φ) b :=
  h.satisfies_axiom (Or.inr (Or.inl ⟨hn, φ, hφ, rfl⟩)) hb

theorem replacement {M n φ b : V} (h : IsCodedZFModel M) (hn : n ∈ (ω : V))
    (hφ : IsMembershipFormulaCode (succ (succ n)) φ) (hb : b ∈ structureDomain M ^ n) :
    Satisfies membershipLanguageCode ∅ M ∅ n (replacementCode n φ) b :=
  h.satisfies_axiom (Or.inr (Or.inr ⟨hn, φ, hφ, rfl⟩)) hb

end IsCodedZFModel

/-- An actual internal set of sentence codes: every open axiom is closed by its
own internal number of parameter variables. Nonstandard schema instances remain. -/
noncomputable def zfClosedAxiomCodes : V :=
  {χ ∈ formulaSet membershipLanguageCode ∅ 0 ;
    ∃ n φ, IsZFOpenAxiom n φ ∧ χ = internalAllClosureCode φ n}

theorem mem_zfClosedAxiomCodes_iff (χ : V) : χ ∈ (zfClosedAxiomCodes : V) ↔
    ∃ n φ, IsZFOpenAxiom n φ ∧ χ = internalAllClosureCode φ n := by
  rw [zfClosedAxiomCodes, mem_sep_iff]
  constructor
  · exact And.right
  · rintro ⟨n, φ, hφ, rfl⟩
    exact ⟨internalAllClosureCode_sentence_valid membershipLanguageCode_valid hφ.valid.context hφ.valid.valid,
      n, φ, hφ, rfl⟩

theorem zfClosedAxiomCodes_valid {χ : V} (hχ : χ ∈ (zfClosedAxiomCodes : V)) :
    χ ∈ formulaSet (membershipLanguageCode : V) ∅ (0 : V) := by
  unfold zfClosedAxiomCodes at hχ
  exact (mem_sep_iff.mp hχ).1

theorem isCodedZFModel_iff_closed (M : V) : IsCodedZFModel M ↔
    IsStructureCode membershipLanguageCode M ∧
      ∀ χ ∈ (zfClosedAxiomCodes : V), Satisfies membershipLanguageCode ∅ M ∅ 0 χ ∅ := by
  constructor
  · intro h
    refine ⟨h.valid, fun χ hχ ↦ ?_⟩
    obtain ⟨n, φ, hφ, rfl⟩ := (mem_zfClosedAxiomCodes_iff χ).mp hχ
    exact (internalAllClosureCode_satisfies_iff membershipLanguageCode_valid hφ.valid.context hφ.valid.valid).mpr
      (fun b hb ↦ h.satisfies_axiom hφ hb)
  · rintro ⟨hM, hsent⟩
    refine ⟨hM, fun n φ hφ ↦ ?_⟩
    have hax := (mem_zfOpenAxiomCodes_iff n φ).mp hφ
    refine ⟨hax.valid.valid, ?_⟩
    apply (internalAllClosureCode_satisfies_iff membershipLanguageCode_valid hax.valid.context hax.valid.valid).mp
    exact hsent _ ((mem_zfClosedAxiomCodes_iff _).mpr ⟨n, φ, hax, rfl⟩)

theorem IsCodedElementaryEmbedding.isCodedZFModel_iff {M N f : V}
    (h : IsCodedElementaryEmbedding membershipLanguageCode M N f) :
    IsCodedZFModel M ↔ IsCodedZFModel N := h.satisfiesCodedOpenTheory_iff

theorem satisfiesCodedOpenTheory_membership_iff (D T : V) :
    SatisfiesCodedOpenTheory membershipLanguageCode (membershipStructureCode D) T ↔ SatisfiesOpenCodes D T := by
  constructor
  · rintro ⟨hM, hT⟩
    refine ⟨by simpa using hM.domain_nonempty, fun n φ hφ ↦ ?_⟩
    obtain ⟨hv, hs⟩ := hT n φ hφ
    refine ⟨(mem_formulaSet_iff _ _ _ _).mp hv, fun b hb ↦ ?_⟩
    exact hs b (by simpa only [membershipStructureCode_domain] using hb)
  · rintro ⟨hD, hT⟩
    refine ⟨membershipStructureCode_valid hD, fun n φ hφ ↦ ?_⟩
    obtain ⟨hv, hs⟩ := hT n φ hφ
    refine ⟨hv.valid, fun b hb ↦ ?_⟩
    exact hs b (by simpa only [membershipStructureCode_domain] using hb)

theorem isCodedZFModel_membership_iff (D : V) :
    IsCodedZFModel (membershipStructureCode D) ↔ IsInternalZFModel D :=
  (satisfiesCodedOpenTheory_membership_iff D zfOpenAxiomCodes).trans (satisfiesOpenCodes_zf_iff D)

end ZFVP
