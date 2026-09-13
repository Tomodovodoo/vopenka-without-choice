import ZFVP.ModelTheory.SchmerlNamedUpperRealization
import ZFVP.ModelTheory.SchmerlDefinitionTransport
import ZFVP.ModelTheory.InternalNamedModel

/-! An actual countable elementary successor with simultaneous strict bounds
for every directed poset defined over the source by internal syntax. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCodedCofinalBounds (M N e c : V) : Prop :=
  c ∈ structureDomain N ^ codedDirectedPosetIndex M ∧
    ∀ i ∈ codedDirectedPosetIndex M,
      c ‘ i ∈ unaryDefinitionSet N (transportDefinition (kpair.π₁ i) e) ∧
      ∀ x ∈ (codedDirectedPosetDomains M) ‘ i,
        ⟨e ‘ x, c ‘ i⟩ₖ ∈ binaryDefinitionRelation N (transportDefinition (kpair.π₂ i) e) ∧ e ‘ x ≠ c ‘ i

instance isCodedCofinalBounds_definable : ℒₛₑₜ-relation₄[V] IsCodedCofinalBounds := by
  unfold IsCodedCofinalBounds
  definability

theorem namedUpper_complete_model_bounds {D R j k T : V}
    (hD : IsNonempty D)
    (hj : j ∈ (ω : V) ^ structureDomain (binaryRelationStructureCode D R))
    (hk : k ∈ (ω : V) ^ codedDirectedPosetIndex (binaryRelationStructureCode D R))
    (hT : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j
      (namedUpperBackground (binaryRelationStructureCode D R) j k) T) :
    IsCodedCofinalBounds (binaryRelationStructureCode D R) (namedTheoryModel T)
      (compose j (namedTheoryProjection T)) (compose k (namedTheoryProjection T)) := by
  let M := binaryRelationStructureCode D R
  let N := namedTheoryModel T
  let e := compose j (namedTheoryProjection T)
  let c := compose k (namedTheoryProjection T)
  have he : IsCodedElementaryEmbedding membershipLanguageCode M N e :=
    hT.model_elementary hD (by simpa only [binaryRelationStructureCode_domain] using hj)
      (namedUpperBackground_diagram M j k)
  have hmem : ∀ i ∈ codedDirectedPosetIndex M,
      c ‘ i ∈ unaryDefinitionSet N (transportDefinition (kpair.π₁ i) e) := by
    intro i hi
    exact (namedUpperMember_model_iff (codedDirectedPosetIndex_spec hi).1 hj hk (namedTheoryProjection_mem T) hi).mp
      (hT.model_background hD _ (namedUpperMember_mem hi))
  have hupper : ∀ i ∈ codedDirectedPosetIndex M, ∀ x ∈ (codedDirectedPosetDomains M) ‘ i,
      ⟨e ‘ x, c ‘ i⟩ₖ ∈ binaryDefinitionRelation N (transportDefinition (kpair.π₂ i) e) := by
    intro i hi x hx
    have hxD := mem_power_iff.mp (function_value_mem (codedDirectedPosetDomains_mem M) hi) x hx
    exact (namedUpperOrder_model_iff (codedDirectedPosetIndex_spec hi).2.1 hj hk
      (namedTheoryProjection_mem T) hi hxD).mp (hT.model_background hD _ (namedUpperOrder_mem hi hx))
  refine ⟨compose_function hk (namedTheoryProjection_mem T), fun i hi ↦ ⟨hmem i hi, fun x hx ↦ ⟨hupper i hi x hx, ?_⟩⟩⟩
  intro hxc
  obtain ⟨z, hz, hxz, hxne⟩ := (codedDirectedPosetFamily_directed hi).strict_upper hx
  have hzD := mem_power_iff.mp (function_value_mem (codedDirectedPosetDomains_mem M) hi) z hz
  have hxD := mem_power_iff.mp (function_value_mem (codedDirectedPosetDomains_mem M) hi) x hx
  have hzxN := hupper i hi z hz
  rw [← hxc] at hzxN
  have hzx := (elementary_binaryDefinition_iff he (codedDirectedPosetIndex_spec hi).2.1 hzD hxD).mpr hzxN
  rw [← codedDirectedPosetRelations_value hi] at hzx
  exact hxne ((codedDirectedPosetFamily_poset hi).2 x hx z hz hxz hzx)

theorem namedTheoryModel_binary (T : V) :
    ∃ A S, namedTheoryModel T = binaryRelationStructureCode A S ∧ S ⊆ A ×ˢ A := by
  exact ⟨_, _, rfl, internalQuotientEdges_subset (namedTableRelation_subset T (relationToken 1))⟩

theorem exists_codedCofinalSuccessor (hAC : InternalChoice V) {D R : V}
    (hM : IsCodedZFModel (binaryRelationStructureCode D R))
    (hcount : IsInternallyCountable D) :
    ∃ N e c : V, (∃ A S, N = binaryRelationStructureCode A S ∧ S ⊆ A ×ˢ A) ∧
      IsCodedZFModel N ∧ IsInternallyCountable (structureDomain N) ∧
      IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D R) N e ∧
      IsCodedCofinalBounds (binaryRelationStructureCode D R) N e c := by
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hM.valid.domain_nonempty
  obtain ⟨j, k, hj, _, hk, _, _, hfr, hB⟩ := exists_namedUpperBackground hAC hM.valid
    (by simpa only [binaryRelationStructureCode_domain] using hcount)
  obtain ⟨T, hT, hZF, hc, he, _⟩ := exists_named_countable_elementary_extension hAC hM
    (by simpa only [binaryRelationStructureCode_domain] using hj) hB hfr
    (namedUpperBackground_diagram _ j k)
  exact ⟨namedTheoryModel T, compose j (namedTheoryProjection T), compose k (namedTheoryProjection T),
    namedTheoryModel_binary T, hZF, hc, he, namedUpper_complete_model_bounds hD hj hk hT⟩

end ZFVP.Schmerl
