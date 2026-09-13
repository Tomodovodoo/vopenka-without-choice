import ZFVP.ModelTheory.InternalEmbeddingRelabeling
import ZFVP.ModelTheory.SchmerlInternalCodedFiniteTraces

/-! Actual coded elementary embeddings become literal inclusions after
relabeling. Countability, full coded ZF, and finite member traces are preserved. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCodedFiniteTraceEmbedding (M N f : V) : Prop :=
  ∀ a ∈ structureDomain M, codedUnary M (encodeMembershipFormula internallyFiniteFormula) a →
    ∀ y ∈ structureDomain N, codedMember N y (f ‘ a) → y ∈ range f

def isCodedFiniteTraceEmbeddingFormula : SetTheorySemisentence 3 :=
  f“M N f. ∀ a ∈ !structureDomainFormula M,
    !codedUnaryFormula M (!(encodeMembershipFormulaFormula internallyFiniteFormula)) a →
      ∀ y ∈ !structureDomainFormula N, !codedMemberFormula N y (!value.dfn f a) → y ∈ !range.dfn f”

instance isCodedFiniteTraceEmbeddingFormula_defined :
    ℒₛₑₜ-relation₃[V] IsCodedFiniteTraceEmbedding via isCodedFiniteTraceEmbeddingFormula :=
  ⟨fun v ↦ by simp [isCodedFiniteTraceEmbeddingFormula, IsCodedFiniteTraceEmbedding]⟩

instance isCodedFiniteTraceEmbedding_definable : ℒₛₑₜ-relation₃[V] IsCodedFiniteTraceEmbedding :=
  isCodedFiniteTraceEmbeddingFormula_defined.to_definable

theorem embeddingRelabelStructure_countable {D A R f : V} (hA : IsInternallyCountable A) :
    IsInternallyCountable (structureDomain (embeddingRelabelStructure D A R f)) := by
  rw [embeddingRelabelStructure_domain]
  exact embeddingRelabelCarrier_countable hA

theorem embeddingRelabelStructure_codedZF {D E A R f : V}
    (hf : IsCodedElementaryEmbedding membershipLanguageCode
      (binaryRelationStructureCode D E) (binaryRelationStructureCode A R) f)
    (hZF : IsCodedZFModel (binaryRelationStructureCode D E)) :
    IsCodedZFModel (embeddingRelabelStructure D A R f) :=
  (embeddingRelabelStructure_inclusion_elementary hf).satisfiesCodedOpenTheory_iff.mp hZF

theorem embeddingRelabelStructure_codedZF_of_target {D E A R f : V}
    (hf : IsCodedElementaryEmbedding membershipLanguageCode
      (binaryRelationStructureCode D E) (binaryRelationStructureCode A R) f)
    (hZF : IsCodedZFModel (binaryRelationStructureCode A R)) :
    IsCodedZFModel (embeddingRelabelStructure D A R f) :=
  embeddingRelabelStructure_codedZF hf (hf.satisfiesCodedOpenTheory_iff.mpr hZF)

theorem embeddingRelabelStructure_finiteEndExtension {D E A R f : V}
    (hf : IsCodedElementaryEmbedding membershipLanguageCode
      (binaryRelationStructureCode D E) (binaryRelationStructureCode A R) f)
    (htrace : IsCodedFiniteTraceEmbedding
      (binaryRelationStructureCode D E) (binaryRelationStructureCode A R) f) :
    IsCodedFiniteEndExtension (binaryRelationStructureCode D E) (embeddingRelabelStructure D A R f) := by
  have hff : f ∈ A ^ D := by simpa only [binaryRelationStructureCode_domain] using hf.function
  have hA : IsNonempty A := by simpa only [binaryRelationStructureCode_domain] using hf.target.domain_nonempty
  have hB : IsNonempty (embeddingRelabelCarrier D A f) := embeddingRelabelCarrier_nonempty hA
  intro a ha hfin x hx hmem
  have haD : a ∈ D := by simpa only [binaryRelationStructureCode_domain] using ha
  have hxB : x ∈ embeddingRelabelCarrier D A f := by simpa only [embeddingRelabelStructure_domain] using hx
  have haB := embeddingRelabelCarrier_includes hff hf.injective a haD
  have he : ⟨x, a⟩ₖ ∈ embeddingRelabelEdges D A R f :=
    (codedMember_binary_iff hB hxB haB).mp hmem
  obtain ⟨y, hy, rfl⟩ := (mem_embeddingRelabelCarrier D A f x).mp hxB
  have hfa : f ‘ a ∈ A := function_value_mem hff haD
  have hold : ⟨y, f ‘ a⟩ₖ ∈ R := by
    apply (embeddingRelabelEdges_iff hff hf.injective hy hfa).mp
    simpa only [embeddingRelabelGraph_value hy, embeddingRelabelGraph_value hfa,
      embeddingRelabelValue_old hff hf.injective haD] using he
  have hyr : y ∈ range f := htrace a ha hfin y
    (by simpa only [binaryRelationStructureCode_domain] using hy)
    ((codedMember_binary_iff hA hy hfa).mpr hold)
  rw [binaryRelationStructureCode_domain]
  rw [embeddingRelabelValue, ite_eq_left hyr]
  exact function_value_mem (converseGraph_mem_function hff hf.injective) hyr

theorem exists_literal_coded_elementary_extension {D E A R f : V}
    (hf : IsCodedElementaryEmbedding membershipLanguageCode
      (binaryRelationStructureCode D E) (binaryRelationStructureCode A R) f)
    (hcount : IsInternallyCountable A) (hZF : IsCodedZFModel (binaryRelationStructureCode D E)) :
    ∃ B S : V, D ⊆ B ∧ S ⊆ B ×ˢ B ∧ IsInternallyCountable B ∧
      IsCodedZFModel (binaryRelationStructureCode B S) ∧
      IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D E)
        (binaryRelationStructureCode B S) (SetTheory.identity D) := by
  have hff : f ∈ A ^ D := by simpa only [binaryRelationStructureCode_domain] using hf.function
  exact ⟨embeddingRelabelCarrier D A f, embeddingRelabelEdges D A R f,
    embeddingRelabelCarrier_includes hff hf.injective, embeddingRelabelEdges_subset D A R f,
    embeddingRelabelCarrier_countable hcount, embeddingRelabelStructure_codedZF hf hZF,
    embeddingRelabelStructure_inclusion_elementary hf⟩

theorem exists_literal_coded_finite_end_extension {D E A R f : V}
    (hf : IsCodedElementaryEmbedding membershipLanguageCode
      (binaryRelationStructureCode D E) (binaryRelationStructureCode A R) f)
    (hcount : IsInternallyCountable A) (hZF : IsCodedZFModel (binaryRelationStructureCode D E))
    (htrace : IsCodedFiniteTraceEmbedding
      (binaryRelationStructureCode D E) (binaryRelationStructureCode A R) f) :
    ∃ B S : V, D ⊆ B ∧ S ⊆ B ×ˢ B ∧ IsInternallyCountable B ∧
      IsCodedZFModel (binaryRelationStructureCode B S) ∧
      IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D E)
        (binaryRelationStructureCode B S) (SetTheory.identity D) ∧
      IsCodedFiniteEndExtension (binaryRelationStructureCode D E) (binaryRelationStructureCode B S) := by
  have hff : f ∈ A ^ D := by simpa only [binaryRelationStructureCode_domain] using hf.function
  exact ⟨embeddingRelabelCarrier D A f, embeddingRelabelEdges D A R f,
    embeddingRelabelCarrier_includes hff hf.injective, embeddingRelabelEdges_subset D A R f,
    embeddingRelabelCarrier_countable hcount, embeddingRelabelStructure_codedZF hf hZF,
    embeddingRelabelStructure_inclusion_elementary hf, embeddingRelabelStructure_finiteEndExtension hf htrace⟩

end ZFVP.Schmerl
