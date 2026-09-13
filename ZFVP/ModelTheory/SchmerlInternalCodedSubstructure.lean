import ZFVP.ModelTheory.CodedElementaryEmbedding
import ZFVP.Syntax.SatisfactionEquations
import ZFVP.Syntax.TermInduction

/-! Induced coded substructures and their agreement on all internal terms. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCodedFunctionClosed (L M A : V) : Prop :=
  ∀ f ∈ functionSymbols L, ∀ s ∈ A ^ ((functionArities L) ‘ f),
    ((structureFunctions M) ‘ f) ‘ s ∈ A

instance isCodedFunctionClosed_definable : ℒₛₑₜ-relation₃[V] IsCodedFunctionClosed := by
  unfold IsCodedFunctionClosed
  definability

noncomputable def codedRestriction (L M A : V) : V :=
  structureCode A
    (definableGraph (functionSymbols L)
      (fun f ↦ ((structureFunctions M) ‘ f) ↾ (A ^ ((functionArities L) ‘ f))) (by definability))
    (definableGraph (relationSymbols L)
      (fun r ↦ ((structureRelations M) ‘ r) ∩ (A ^ ((relationArities L) ‘ r))) (by definability))

@[simp] theorem structureDomain_codedRestriction (L M A : V) :
    structureDomain (codedRestriction L M A) = A := structureDomain_code _ _ _

theorem codedRestriction_valid {L M A : V} (hM : IsStructureCode L M)
    (hA : A ⊆ structureDomain M) (hne : IsNonempty A) (hc : IsCodedFunctionClosed L M A) :
    IsStructureCode L (codedRestriction L M A) := by
  simp only [IsStructureCode, codedRestriction, structureDomain_code,
    structureFunctions_code, structureRelations_code, domain_definableGraph]
  refine ⟨hM.language, True.intro, hne, inferInstance, True.intro, inferInstance, True.intro, ?_, ?_⟩
  · intro f hf
    rw [value_definableGraph _ _ _ hf]
    have hfun := hM.2.2.2.2.2.2.2.1 f hf
    let : IsFunction ((structureFunctions M) ‘ f) := IsFunction.of_mem hfun
    apply restrict_mem_function_of_values
    · rw [domain_eq_of_mem_function hfun]
      exact fun _ hs ↦ mem_function_of_mem_function_of_subset hs hA
    · exact hc f hf
  · intro r hr
    rw [value_definableGraph _ _ _ hr]
    exact fun _ hs ↦ (mem_inter_iff.mp hs).2

def IsCodedSubstructure (L N M : V) : Prop :=
  IsStructureCode L N ∧ IsStructureCode L M ∧ structureDomain N ⊆ structureDomain M ∧
    (∀ f ∈ functionSymbols L, ∀ s ∈ structureDomain N ^ ((functionArities L) ‘ f),
      ((structureFunctions N) ‘ f) ‘ s = ((structureFunctions M) ‘ f) ‘ s) ∧
    ∀ r ∈ relationSymbols L, ∀ s ∈ structureDomain N ^ ((relationArities L) ‘ r),
      (s ∈ (structureRelations N) ‘ r ↔ s ∈ (structureRelations M) ‘ r)

theorem codedRestriction_substructure {L M A : V} (hM : IsStructureCode L M)
    (hA : A ⊆ structureDomain M) (hne : IsNonempty A) (hc : IsCodedFunctionClosed L M A) :
    IsCodedSubstructure L (codedRestriction L M A) M := by
  refine ⟨codedRestriction_valid hM hA hne hc, hM,
    by simpa only [structureDomain_codedRestriction] using hA, ?_, ?_⟩
  · intro f hf s hs
    simp only [structureDomain_codedRestriction] at hs
    simp only [codedRestriction, structureFunctions_code]
    rw [value_definableGraph _ _ _ hf]
    have hfun := hM.2.2.2.2.2.2.2.1 f hf
    let : IsFunction ((structureFunctions M) ‘ f) := IsFunction.of_mem hfun
    have hsdom : s ∈ domain ((structureFunctions M) ‘ f) := by
      rw [domain_eq_of_mem_function hfun]
      exact mem_function_of_mem_function_of_subset hs hA
    exact value_restrict hsdom hs
  · intro r hr s hs
    simp only [structureDomain_codedRestriction] at hs
    simp only [codedRestriction, structureRelations_code]
    rw [value_definableGraph _ _ _ hr, mem_inter_iff]
    exact and_iff_left hs

theorem compose_eq_of_values {f g h : V} [IsFunction g] [IsFunction h]
    (hg : range f ⊆ domain g) (hh : range f ⊆ domain h)
    (he : ∀ x ∈ range f, g ‘ x = h ‘ x) : compose f g = compose f h := by
  have hsub {g h : V} [IsFunction g] [IsFunction h]
      (hh : range f ⊆ domain h) (he : ∀ x ∈ range f, g ‘ x = h ‘ x) : compose f g ⊆ compose f h := by
    intro z hz
    obtain ⟨x, y, w, hxy, hyw, rfl⟩ := mem_compose_iff.mp hz
    have hy := mem_range_of_kpair_mem hxy
    exact mem_compose_iff.mpr ⟨x, y, w, hxy,
      kpair_mem_iff_value.mpr ⟨hh y hy, (he y hy).symm.trans (value_eq_of_kpair_mem hyw)⟩, rfl⟩
  exact SetTheory.subset_antisymm (hsub hh he) (hsub hg (fun x hx ↦ (he x hx).symm))

namespace IsCodedSubstructure

variable {L N M : V} (h : IsCodedSubstructure L N M)

include h

theorem termEvaluation_eq {n b : V} (hn : n ∈ (ω : V)) (hb : b ∈ structureDomain N ^ n)
    {t : V} (ht : t ∈ termSet L ∅ n) :
    (termEvaluation L ∅ n N b ∅) ‘ t = (termEvaluation L ∅ n M b ∅) ‘ t := by
  apply termSet_induction h.1.language hn ∅
    (fun t ↦ (termEvaluation L ∅ n N b ∅) ‘ t = (termEvaluation L ∅ n M b ∅) ‘ t)
    (by definability) ?_ ?_ ?_ t ht
  · intro i hi
    rw [termEvaluation_boundVar h.1.language hn ∅ N b ∅ hi,
      termEvaluation_boundVar h.1.language hn ∅ M b ∅ hi]
  · intro x hx
    exact False.elim (not_mem_empty hx)
  · intro f hf args ha ih
    have ht := (functionTermCode_mem_iff h.1.language hn ∅ f args).mpr ⟨hf, ha⟩
    rw [termEvaluation_function h.1.language hn ∅ N b ∅ ht,
      termEvaluation_function h.1.language hn ∅ M b ∅ ht]
    have he := compose_eq_of_values
      (g := termEvaluation L ∅ n N b ∅) (h := termEvaluation L ∅ n M b ∅)
      (by simpa only [domain_termEvaluation] using range_subset_of_mem_function ha)
      (by simpa only [domain_termEvaluation] using range_subset_of_mem_function ha) ih
    have haN := evaluatedArguments_mem_function h.1 hn hb
      (show (∅ : V) ∈ structureDomain N ^ (∅ : V) from by simp [mem_function_iff]) ha
    change compose args (termEvaluation L ∅ n N b ∅) ∈ structureDomain N ^ _ at haN
    exact (h.2.2.2.1 f hf _ haN).trans (congrArg (fun s ↦ ((structureFunctions M) ‘ f) ‘ s) he)

theorem evaluatedArguments_eq {n b args k : V} (hn : n ∈ (ω : V))
    (hb : b ∈ structureDomain N ^ n) (ha : args ∈ termSet L ∅ n ^ k) :
    evaluatedArguments L ∅ N ∅ n b args = evaluatedArguments L ∅ M ∅ n b args := by
  change compose args (termEvaluation L ∅ n N b ∅) = compose args (termEvaluation L ∅ n M b ∅)
  exact compose_eq_of_values
    (by simpa only [domain_termEvaluation] using range_subset_of_mem_function ha)
    (by simpa only [domain_termEvaluation] using range_subset_of_mem_function ha)
    (fun _ ht ↦ h.termEvaluation_eq hn hb (range_subset_of_mem_function ha _ ht))

theorem atomicHolds_iff {n b r args : V} (hn : n ∈ (ω : V))
    (hb : b ∈ structureDomain N ^ n) (ha : IsAtomicArguments L ∅ n r args) :
    AtomicHolds L ∅ N ∅ n b r args ↔ AtomicHolds L ∅ M ∅ n b r args := by
  rcases ha with ⟨rfl, ha⟩ | ⟨s, hs, rfl, ha⟩
  · rw [atomicHolds_equality, atomicHolds_equality, h.evaluatedArguments_eq hn hb ha]
  · rw [atomicHolds_relation, atomicHolds_relation]
    apply and_congr Iff.rfl
    rw [← h.evaluatedArguments_eq hn hb ha]
    exact h.2.2.2.2 s hs _ (evaluatedArguments_mem_function h.1 hn hb
      (show (∅ : V) ∈ structureDomain N ^ (∅ : V) from by simp [mem_function_iff]) ha)

end IsCodedSubstructure
end ZFVP.Schmerl
