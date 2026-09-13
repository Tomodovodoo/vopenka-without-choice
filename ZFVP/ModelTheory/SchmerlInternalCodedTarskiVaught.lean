import ZFVP.ModelTheory.SchmerlInternalCodedSubstructure
import ZFVP.Syntax.FormulaInduction

/-! Internal Tarski–Vaught, proved by definable induction through all
internally finite formulas, including the nonstandard ones. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCodedWitnessClosed (L M A : V) : Prop :=
  ∀ n ∈ (ω : V), ∀ φ ∈ formulaSet L ∅ (succ n), ∀ b ∈ A ^ n,
    ((∃ x ∈ structureDomain M, Satisfies L ∅ M ∅ (succ n) φ (assignmentPrepend n b x)) →
      ∃ x ∈ A, Satisfies L ∅ M ∅ (succ n) φ (assignmentPrepend n b x)) ∧
    ((∃ x ∈ structureDomain M, ¬Satisfies L ∅ M ∅ (succ n) φ (assignmentPrepend n b x)) →
      ∃ x ∈ A, ¬Satisfies L ∅ M ∅ (succ n) φ (assignmentPrepend n b x))

instance isCodedWitnessClosed_definable (L M : V) :
    ℒₛₑₜ-predicate[V] (IsCodedWitnessClosed L M) := by
  unfold IsCodedWitnessClosed Satisfies
  definability

theorem IsCodedSubstructure.satisfies_iff {L N M : V} (h : IsCodedSubstructure L N M)
    (hw : IsCodedWitnessClosed L M (structureDomain N))
    {n φ b : V} (_hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet L ∅ n) (hb : b ∈ structureDomain N ^ n) :
    Satisfies L ∅ N ∅ n φ b ↔ Satisfies L ∅ M ∅ n φ b := by
  have hall : ∀ n φ, φ ∈ formulaSet L ∅ n → ∀ b ∈ structureDomain N ^ n,
      (Satisfies L ∅ N ∅ n φ b ↔ Satisfies L ∅ M ∅ n φ b) := by
    apply formulaSet_induction h.1.language ∅
      (fun n φ ↦ ∀ b ∈ structureDomain N ^ n,
        (Satisfies L ∅ N ∅ n φ b ↔ Satisfies L ∅ M ∅ n φ b)) (by unfold Satisfies; definability)
    · intro n hn
      constructor
      · intro b hb
        rw [satisfies_truth h.1.language hn, satisfies_truth h.1.language hn]
        exact iff_of_true hb (mem_function_of_mem_function_of_subset hb h.2.2.1)
      · intro b _
        exact iff_of_false (not_satisfies_falsity h.1.language hn) (not_satisfies_falsity h.1.language hn)
    · intro n hn r args ha
      constructor
      · intro b hb
        rw [satisfies_atom h.1.language hn ha hb,
          satisfies_atom h.1.language hn ha (mem_function_of_mem_function_of_subset hb h.2.2.1)]
        exact h.atomicHolds_iff hn hb ha
      · intro b hb
        rw [satisfies_negAtom h.1.language hn ha hb,
          satisfies_negAtom h.1.language hn ha (mem_function_of_mem_function_of_subset hb h.2.2.1)]
        exact not_congr (h.atomicHolds_iff hn hb ha)
    · intro n hn φ ψ hφ hψ ihφ ihψ
      constructor
      · intro b hb
        rw [satisfies_and h.1.language hn hφ hψ hb,
          satisfies_and h.1.language hn hφ hψ (mem_function_of_mem_function_of_subset hb h.2.2.1)]
        exact and_congr (ihφ b hb) (ihψ b hb)
      · intro b hb
        rw [satisfies_or h.1.language hn hφ hψ hb,
          satisfies_or h.1.language hn hφ hψ (mem_function_of_mem_function_of_subset hb h.2.2.1)]
        exact or_congr (ihφ b hb) (ihψ b hb)
    · intro n hn φ hφ ih
      constructor
      · intro b hb
        rw [satisfies_all h.1.language hn hφ hb,
          satisfies_all h.1.language hn hφ (mem_function_of_mem_function_of_subset hb h.2.2.1)]
        constructor
        · intro hall x hx
          by_contra hnot
          obtain ⟨y, hy, hny⟩ := (hw n hn φ hφ b hb).2 ⟨x, hx, hnot⟩
          exact hny ((ih _ (assignmentPrepend_mem_function hn hb hy)).mp (hall y hy))
        · intro hall x hx
          exact (ih _ (assignmentPrepend_mem_function hn hb hx)).mpr (hall x (h.2.2.1 x hx))
      · intro b hb
        rw [satisfies_exists h.1.language hn hφ hb,
          satisfies_exists h.1.language hn hφ (mem_function_of_mem_function_of_subset hb h.2.2.1)]
        constructor
        · rintro ⟨x, hx, hxSat⟩
          exact ⟨x, h.2.2.1 x hx, (ih _ (assignmentPrepend_mem_function hn hb hx)).mp hxSat⟩
        · intro hex
          obtain ⟨x, hx, hxSat⟩ := (hw n hn φ hφ b hb).1 hex
          exact ⟨x, hx, (ih _ (assignmentPrepend_mem_function hn hb hx)).mpr hxSat⟩
  exact hall n φ hφ b hb

theorem IsCodedSubstructure.elementary {L N M : V} (h : IsCodedSubstructure L N M)
    (hw : IsCodedWitnessClosed L M (structureDomain N)) :
    IsCodedElementaryEmbedding L N M (SetTheory.identity (structureDomain N)) := by
  refine ⟨h.1, h.2.1, mem_function_of_mem_function_of_subset (identity_mem_function _) h.2.2.1, ?_⟩
  intro n hn φ hφ b hb
  rw [graph_compose_identity hb]
  exact h.satisfies_iff hw hn hφ hb

theorem codedRestriction_elementary {L M A : V} (hM : IsStructureCode L M)
    (hA : A ⊆ structureDomain M) (hne : IsNonempty A)
    (hc : IsCodedFunctionClosed L M A) (hw : IsCodedWitnessClosed L M A) :
    IsCodedElementaryEmbedding L (codedRestriction L M A) M (SetTheory.identity A) := by
  have h := (codedRestriction_substructure hM hA hne hc).elementary
    (by simpa only [structureDomain_codedRestriction] using hw)
  simpa only [structureDomain_codedRestriction] using h

end ZFVP.Schmerl
