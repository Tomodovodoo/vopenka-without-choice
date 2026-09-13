import ZFVP.ModelTheory.SchmerlNamedUpperEntries
import ZFVP.ModelTheory.CodedElementaryEmbedding

/-! Parameter transport in actual raw definitions and named requirements. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def transportDefinition (d e : V) : V :=
  ⟨⟨definitionParameterCount d, definitionFormula d⟩ₖ, compose (definitionTuple d) e⟩ₖ

instance transportDefinition_definable : ℒₛₑₜ-function₂[V] transportDefinition := by
  unfold transportDefinition
  definability

@[simp] theorem transportDefinition_count (d e : V) :
    definitionParameterCount (transportDefinition d e) = definitionParameterCount d := by
  simp only [transportDefinition, definitionParameterCount_pair]

@[simp] theorem transportDefinition_formula (d e : V) :
    definitionFormula (transportDefinition d e) = definitionFormula d := by
  simp only [transportDefinition, definitionFormula_pair]

@[simp] theorem transportDefinition_tuple (d e : V) :
    definitionTuple (transportDefinition d e) = compose (definitionTuple d) e := by
  simp only [transportDefinition, definitionTuple_pair]

theorem transportDefinition_unary {M N d e : V}
    (hd : d ∈ unaryDefinitionParameters M) (he : e ∈ structureDomain N ^ structureDomain M) :
    transportDefinition d e ∈ unaryDefinitionParameters N := by
  obtain ⟨hn, hφ, hb⟩ := unaryDefinitionParameters_spec hd
  exact pair_mem_unaryDefinitionParameters.mpr ⟨hn, hφ, compose_function hb he⟩

theorem transportDefinition_binary {M N d e : V}
    (hd : d ∈ binaryDefinitionParameters M) (he : e ∈ structureDomain N ^ structureDomain M) :
    transportDefinition d e ∈ binaryDefinitionParameters N := by
  obtain ⟨hn, hφ, hb⟩ := binaryDefinitionParameters_spec hd
  exact pair_mem_binaryDefinitionParameters.mpr ⟨hn, hφ, compose_function hb he⟩

theorem elementary_unaryDefinition_iff {M N d e x : V}
    (he : IsCodedElementaryEmbedding membershipLanguageCode M N e)
    (hd : d ∈ unaryDefinitionParameters M) (hx : x ∈ structureDomain M) :
    x ∈ unaryDefinitionSet M d ↔ e ‘ x ∈ unaryDefinitionSet N (transportDefinition d e) := by
  obtain ⟨hn, hφ, hb⟩ := unaryDefinitionParameters_spec hd
  rw [mem_unaryDefinitionSet, mem_unaryDefinitionSet, and_iff_right hx,
    and_iff_right (function_value_mem he.function hx), transportDefinition_count,
    transportDefinition_formula, transportDefinition_tuple]
  have hs := he.satisfies_iff (ω_succ_closed hn) hφ (assignmentPrepend_mem_function hn hb hx)
  rw [compose_assignmentPrepend hn hb he.function hx] at hs
  exact hs

theorem elementary_binaryDefinition_iff {M N d e x y : V}
    (he : IsCodedElementaryEmbedding membershipLanguageCode M N e)
    (hd : d ∈ binaryDefinitionParameters M) (hx : x ∈ structureDomain M) (hy : y ∈ structureDomain M) :
    ⟨x, y⟩ₖ ∈ binaryDefinitionRelation M d ↔
      ⟨e ‘ x, e ‘ y⟩ₖ ∈ binaryDefinitionRelation N (transportDefinition d e) := by
  obtain ⟨hn, hφ, hb⟩ := binaryDefinitionParameters_spec hd
  rw [pair_mem_binaryDefinitionRelation, pair_mem_binaryDefinitionRelation, and_iff_right ⟨hx, hy⟩,
    and_iff_right ⟨function_value_mem he.function hx, function_value_mem he.function hy⟩,
    transportDefinition_count, transportDefinition_formula, transportDefinition_tuple]
  have hs := he.satisfies_iff (ω_succ_closed (ω_succ_closed hn)) hφ
    (assignmentPrepend_mem_function (ω_succ_closed hn) (assignmentPrepend_mem_function hn hb hy) hx)
  rw [compose_assignmentPrepend (ω_succ_closed hn) (assignmentPrepend_mem_function hn hb hy) he.function hx,
    compose_assignmentPrepend hn hb he.function hy] at hs
  exact hs

theorem namedUpperMember_model_iff {M N I j k i q : V}
    (hd : kpair.π₁ i ∈ unaryDefinitionParameters M)
    (hj : j ∈ (ω : V) ^ structureDomain M) (hk : k ∈ (ω : V) ^ I)
    (hq : q ∈ structureDomain N ^ (ω : V)) (hi : i ∈ I) :
    NamedHolds membershipLanguageCode N q (namedUpperMember j k i) ↔
      (compose k q) ‘ i ∈ unaryDefinitionSet N (transportDefinition (kpair.π₁ i) (compose j q)) := by
  obtain ⟨hn, _, hb⟩ := unaryDefinitionParameters_spec hd
  rw [namedUpperMember, namedUnaryInstance, namedHolds_pair,
    compose_assignmentPrepend hn (compose_function hb hj) hq (function_value_mem hk hi), graph_compose_assoc,
    mem_unaryDefinitionSet, and_iff_right (function_value_mem (compose_function hk hq) hi),
    transportDefinition_count, transportDefinition_formula, transportDefinition_tuple,
    value_compose_of_mem_function hk hq hi]
  rfl

theorem namedUpperOrder_model_iff {M N I j k i x q : V}
    (hd : kpair.π₂ i ∈ binaryDefinitionParameters M)
    (hj : j ∈ (ω : V) ^ structureDomain M) (hk : k ∈ (ω : V) ^ I)
    (hq : q ∈ structureDomain N ^ (ω : V)) (hi : i ∈ I) (hx : x ∈ structureDomain M) :
    NamedHolds membershipLanguageCode N q (namedUpperOrder j k i x) ↔
      ⟨(compose j q) ‘ x, (compose k q) ‘ i⟩ₖ ∈
        binaryDefinitionRelation N (transportDefinition (kpair.π₂ i) (compose j q)) := by
  obtain ⟨hn, _, hb⟩ := binaryDefinitionParameters_spec hd
  rw [namedUpperOrder, namedBinaryInstance, namedHolds_pair,
    compose_assignmentPrepend (ω_succ_closed hn)
      (assignmentPrepend_mem_function hn (compose_function hb hj) (function_value_mem hk hi)) hq
      (function_value_mem hj hx),
    compose_assignmentPrepend hn (compose_function hb hj) hq (function_value_mem hk hi), graph_compose_assoc,
    pair_mem_binaryDefinitionRelation,
    and_iff_right ⟨function_value_mem (compose_function hj hq) hx, function_value_mem (compose_function hk hq) hi⟩,
    transportDefinition_count, transportDefinition_formula, transportDefinition_tuple,
    value_compose_of_mem_function hj hq hx, value_compose_of_mem_function hk hq hi]
  rfl

end ZFVP.Schmerl
