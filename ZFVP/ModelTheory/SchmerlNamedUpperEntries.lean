import ZFVP.ModelTheory.SchmerlCodedDefinitionParameters
import ZFVP.ModelTheory.InternalNamedParameters

/-! The raw named requirements for one cofinal bound: membership in the
defined poset and an order requirement above each old member. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp
attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₅.comp

noncomputable def namedUpperMember (j k i : V) : V :=
  namedUnaryInstance j (definitionParameterCount (kpair.π₁ i))
    (definitionFormula (kpair.π₁ i)) (definitionTuple (kpair.π₁ i)) (k ‘ i)

noncomputable def namedUpperOrder (j k i x : V) : V :=
  namedBinaryInstance j (definitionParameterCount (kpair.π₂ i))
    (definitionFormula (kpair.π₂ i)) (definitionTuple (kpair.π₂ i)) (j ‘ x) (k ‘ i)

instance namedUpperMember_definable : ℒₛₑₜ-function₃[V] namedUpperMember := by
  unfold namedUpperMember namedUnaryInstance
  definability

instance namedUpperOrder_definable : ℒₛₑₜ-function₄[V] namedUpperOrder := by
  unfold namedUpperOrder namedBinaryInstance
  definability

theorem namedUpperMember_valid {M I j k i A : V}
    (hd : kpair.π₁ i ∈ unaryDefinitionParameters M)
    (hj : j ∈ A ^ structureDomain M) (hk : k ∈ A ^ I) (hi : i ∈ I) :
    namedUpperMember j k i ∈ namedFormulaSet membershipLanguageCode A := by
  obtain ⟨hn, hφ, hb⟩ := unaryDefinitionParameters_spec hd
  exact (pair_mem_namedFormulaSet_iff membershipLanguageCode_valid).mpr
    ⟨hφ, assignmentPrepend_mem_function hn (compose_function hb hj) (function_value_mem hk hi)⟩

theorem namedUpperOrder_valid {M I j k i x A : V}
    (hd : kpair.π₂ i ∈ binaryDefinitionParameters M)
    (hj : j ∈ A ^ structureDomain M) (hk : k ∈ A ^ I) (hi : i ∈ I) (hx : x ∈ structureDomain M) :
    namedUpperOrder j k i x ∈ namedFormulaSet membershipLanguageCode A := by
  obtain ⟨hn, hφ, hb⟩ := binaryDefinitionParameters_spec hd
  exact (pair_mem_namedFormulaSet_iff membershipLanguageCode_valid).mpr
    ⟨hφ, assignmentPrepend_mem_function (ω_succ_closed hn)
      (assignmentPrepend_mem_function hn (compose_function hb hj) (function_value_mem hk hi))
      (function_value_mem hj hx)⟩

theorem SourceNaming.upperMember_iff {M I j k i f : V} (hf : ZFVP.SourceNaming M j f)
    (hd : kpair.π₁ i ∈ unaryDefinitionParameters M)
    (hj : j ∈ (ω : V) ^ structureDomain M) (hk : k ∈ (ω : V) ^ I) (hi : i ∈ I) :
    NamedHolds membershipLanguageCode M f (namedUpperMember j k i) ↔
      f ‘ (k ‘ i) ∈ unaryDefinitionSet M (kpair.π₁ i) := by
  obtain ⟨hn, _, hb⟩ := unaryDefinitionParameters_spec hd
  rw [namedUpperMember, hf.unary_iff hn hj hb (function_value_mem hk hi), mem_unaryDefinitionSet]
  exact (and_iff_right (function_value_mem hf.1 (function_value_mem hk hi))).symm

theorem SourceNaming.upperOrder_iff {M I j k i x f : V} (hf : ZFVP.SourceNaming M j f)
    (hd : kpair.π₂ i ∈ binaryDefinitionParameters M)
    (hj : j ∈ (ω : V) ^ structureDomain M) (hk : k ∈ (ω : V) ^ I)
    (hi : i ∈ I) (hx : x ∈ structureDomain M) :
    NamedHolds membershipLanguageCode M f (namedUpperOrder j k i x) ↔
      ⟨x, f ‘ (k ‘ i)⟩ₖ ∈ binaryDefinitionRelation M (kpair.π₂ i) := by
  obtain ⟨hn, _, hb⟩ := binaryDefinitionParameters_spec hd
  rw [namedUpperOrder, hf.binary_iff hn hj hb (function_value_mem hj hx) (function_value_mem hk hi),
    hf.2 x hx, pair_mem_binaryDefinitionRelation]
  exact (and_iff_right ⟨hx, function_value_mem hf.1 (function_value_mem hk hi)⟩).symm

theorem namedUpperOrder_first {M j k i x : V}
    (hd : kpair.π₂ i ∈ binaryDefinitionParameters M) :
    (kpair.π₂ (namedUpperOrder j k i x)) ‘ (0 : V) = j ‘ x := by
  simp only [namedUpperOrder, namedBinaryInstance, kpair.π₂_kpair,
    assignmentPrepend_zero (ω_succ_closed (binaryDefinitionParameters_spec hd).1)]

theorem namedUpperOrder_second {M j k i x : V}
    (hd : kpair.π₂ i ∈ binaryDefinitionParameters M) :
    (kpair.π₂ (namedUpperOrder j k i x)) ‘ (1 : V) = k ‘ i := by
  have hn := (binaryDefinitionParameters_spec hd).1
  have h01 : (1 : V) = succ (0 : V) := rfl
  simp only [namedUpperOrder, namedBinaryInstance, kpair.π₂_kpair, h01,
    assignmentPrepend_succ (ω_succ_closed hn) (zero_mem_succ_natural hn), assignmentPrepend_zero hn]

theorem namedUpperOrder_injective {M I j k : V}
    (hI : ∀ i ∈ I, kpair.π₂ i ∈ binaryDefinitionParameters M)
    (hj : j ∈ (ω : V) ^ structureDomain M) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ I) (hki : Injective k)
    {i l x y : V} (hi : i ∈ I) (hl : l ∈ I) (hx : x ∈ structureDomain M) (hy : y ∈ structureDomain M)
    (he : namedUpperOrder j k i x = namedUpperOrder j k l y) : i = l ∧ x = y := by
  have h0 := congrArg (fun p : V ↦ (kpair.π₂ p) ‘ (0 : V)) he
  have h1 := congrArg (fun p : V ↦ (kpair.π₂ p) ‘ (1 : V)) he
  rw [namedUpperOrder_first (hI i hi), namedUpperOrder_first (hI l hl)] at h0
  rw [namedUpperOrder_second (hI i hi), namedUpperOrder_second (hI l hl)] at h1
  exact ⟨injective_value_eq hk hki hi hl h1, injective_value_eq hj hji hx hy h0⟩

end ZFVP.Schmerl
