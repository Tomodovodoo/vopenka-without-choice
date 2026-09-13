import ZFVP.ModelTheory.InternalNamedFiniteOmission
import ZFVP.ModelTheory.SchmerlCodedDefinitionParameters
import ZFVP.SetTheory.SurjectionAssignmentLift

/-! Actual omission tasks preventing separation of a specified pair of sets.
All target parameter tuples lift to actual name tuples; density is separate. -/

set_option autoImplicit false

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace Schmerl

def IsCodedInseparable (M U W : V) : Prop :=
  U ⊆ structureDomain M ∧ W ⊆ structureDomain M ∧
    ¬∃ A, IsCodedDefinableSet M A ∧ U ⊆ A ∧ ∀ x ∈ W, x ∉ A

attribute [local irreducible] IsCodedDefinableSet

instance isCodedInseparable_definable : ℒₛₑₜ-relation₃[V] IsCodedInseparable := by
  unfold IsCodedInseparable
  definability

end Schmerl

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₅.comp

noncomputable def namedUnaryDefinitionQueries : V :=
  Schmerl.unaryDefinitionParameters (binaryRelationStructureCode (ω : V) ∅)

theorem pair_mem_namedUnaryDefinitionQueries {n φ b : V} :
    ⟨⟨n, φ⟩ₖ, b⟩ₖ ∈ (namedUnaryDefinitionQueries : V) ↔
      n ∈ (ω : V) ∧ φ ∈ formulaSet membershipLanguageCode ∅ (succ n) ∧ b ∈ (ω : V) ^ n := by
  simpa only [namedUnaryDefinitionQueries, binaryRelationStructureCode_domain] using
    (Schmerl.pair_mem_unaryDefinitionParameters (M := binaryRelationStructureCode (ω : V) ∅) (n := n) (φ := φ) (b := b))

theorem namedUnaryDefinitionQueries_spec {t : V} (ht : t ∈ (namedUnaryDefinitionQueries : V)) :
    Schmerl.definitionParameterCount t ∈ (ω : V) ∧
      Schmerl.definitionFormula t ∈ formulaSet membershipLanguageCode ∅ (succ (Schmerl.definitionParameterCount t)) ∧
      Schmerl.definitionTuple t ∈ (ω : V) ^ Schmerl.definitionParameterCount t := by
  simpa only [binaryRelationStructureCode_domain] using Schmerl.unaryDefinitionParameters_spec ht

theorem namedUnaryDefinitionQueries_countable (hAC : InternalChoice V) :
    IsInternallyCountable (namedUnaryDefinitionQueries : V) :=
  Schmerl.unaryDefinitionParameters_countable hAC (by
    simpa only [binaryRelationStructureCode_domain] using internallyCountable_omega (V := V))

noncomputable def namedUnaryQueryInstance (t l : V) : V :=
  ⟨⟨succ (Schmerl.definitionParameterCount t), Schmerl.definitionFormula t⟩ₖ,
    assignmentPrepend (Schmerl.definitionParameterCount t) (Schmerl.definitionTuple t) l⟩ₖ

instance namedUnaryQueryInstance_definable : ℒₛₑₜ-function₂[V] namedUnaryQueryInstance := by
  unfold namedUnaryQueryInstance
  definability

theorem namedUnaryQueryInstance_valid {t l : V} (ht : t ∈ (namedUnaryDefinitionQueries : V)) (hl : l ∈ (ω : V)) :
    namedUnaryQueryInstance t l ∈ namedFormulaSet membershipLanguageCode (ω : V) := by
  obtain ⟨hn, hφ, hb⟩ := namedUnaryDefinitionQueries_spec ht
  exact (pair_mem_namedFormulaSet_iff membershipLanguageCode_valid).mpr
    ⟨hφ, assignmentPrepend_mem_function hn hb hl⟩

theorem namedUnaryQueryInstance_holds {N f t l : V} (hf : f ∈ structureDomain N ^ (ω : V))
    (ht : t ∈ (namedUnaryDefinitionQueries : V)) (hl : l ∈ (ω : V)) :
    NamedHolds membershipLanguageCode N f (namedUnaryQueryInstance t l) ↔
      Schmerl.codedSatisfies N (succ (Schmerl.definitionParameterCount t)) (Schmerl.definitionFormula t)
        (assignmentPrepend (Schmerl.definitionParameterCount t) (compose (Schmerl.definitionTuple t) f) (f ‘ l)) := by
  obtain ⟨hn, _, hb⟩ := namedUnaryDefinitionQueries_spec ht
  rw [namedUnaryQueryInstance, namedHolds_pair, compose_assignmentPrepend hn hb hf hl]
  rfl

theorem quotientAssignment_lift (hAC : InternalChoice V) {D E n b : V}
    (hb : b ∈ internalQuotientCarrier D E ^ n) :
    ∃ c ∈ D ^ n, compose c (internalQuotientProjection D E) = b :=
  exists_assignment_lift_of_surjection hAC (internalQuotientProjection_mem D E) (internalQuotientProjection_range D E) hb

theorem namedTheoryAssignment_lift (hAC : InternalChoice V) {T n b : V}
    (hb : b ∈ structureDomain (namedTheoryModel T) ^ n) :
    ∃ c ∈ (ω : V) ^ n, compose c (namedTheoryProjection T) = b :=
  exists_assignment_lift_of_surjection hAC (namedTheoryProjection_mem T) (namedTheoryProjection_range T) hb

noncomputable def namedSeparationOmissionDense (P j U W t : V) : V :=
  {A ∈ P ; (∃ x ∈ U, namedNegation membershipLanguageCode (namedUnaryQueryInstance t (j ‘ x)) ∈ A) ∨
    ∃ x ∈ W, namedUnaryQueryInstance t (j ‘ x) ∈ A}

instance namedSeparationOmissionDense_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (namedSeparationOmissionDense (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun E P j U W t : V ↦ ∀ A, A ∈ E ↔ A ∈ P ∧
    ((∃ x ∈ U, namedNegation membershipLanguageCode (namedUnaryQueryInstance t (j ‘ x)) ∈ A) ∨
      ∃ x ∈ W, namedUnaryQueryInstance t (j ‘ x) ∈ A)) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [namedSeparationOmissionDense, mem_sep_iff]
  rfl

theorem mem_namedSeparationOmissionDense (P j U W t A : V) : A ∈ namedSeparationOmissionDense P j U W t ↔
    A ∈ P ∧ ((∃ x ∈ U, namedNegation membershipLanguageCode (namedUnaryQueryInstance t (j ‘ x)) ∈ A) ∨
      ∃ x ∈ W, namedUnaryQueryInstance t (j ‘ x) ∈ A) := mem_sep_iff

theorem namedSeparationOmissionDense_subset (P j U W t : V) : namedSeparationOmissionDense P j U W t ⊆ P :=
  fun _ hA ↦ (mem_sep_iff.mp hA).1

noncomputable def namedSeparationOmissionFamily (P j F : V) : V :=
  repl (fun p ↦ namedSeparationOmissionDense P j (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ (kpair.π₁ p)) (kpair.π₂ p))
    (by definability) (F ×ˢ namedUnaryDefinitionQueries)

instance namedSeparationOmissionFamily_definable : ℒₛₑₜ-function₃[V] namedSeparationOmissionFamily := by
  have h : ℒₛₑₜ-relation₄[V] (fun E P j F ↦ ∀ A, A ∈ E ↔
    ∃ p ∈ F ×ˢ namedUnaryDefinitionQueries,
      A = namedSeparationOmissionDense P j (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ (kpair.π₁ p)) (kpair.π₂ p)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [namedSeparationOmissionFamily, repl_spec]
  rfl

theorem namedSeparationOmissionFamily_countable (hAC : InternalChoice V) {P j F : V}
    (hF : IsInternallyCountable F) : IsInternallyCountable (namedSeparationOmissionFamily P j F) :=
  internallyCountable_repl _ _ ((prod_cardLE_prod hF (namedUnaryDefinitionQueries_countable hAC)).trans omega_prod_cardLE_omega)

theorem namedSeparationOmissionDense_mem_family {P j F U W t : V}
    (hpair : ⟨U, W⟩ₖ ∈ F) (ht : t ∈ (namedUnaryDefinitionQueries : V)) :
    namedSeparationOmissionDense P j U W t ∈ namedSeparationOmissionFamily P j F :=
  (repl_spec _).mpr ⟨⟨⟨U, W⟩ₖ, t⟩ₖ, kpair_mem_iff.mpr ⟨hpair, ht⟩, by simp⟩

theorem namedSeparationOmissionFamily_cases {D P j F E : V}
    (hF : F ⊆ power D ×ˢ power D) (hE : E ∈ namedSeparationOmissionFamily P j F) :
    ∃ U W, ⟨U, W⟩ₖ ∈ F ∧ ∃ t ∈ (namedUnaryDefinitionQueries : V), E = namedSeparationOmissionDense P j U W t := by
  obtain ⟨p, hp, rfl⟩ := (repl_spec _).mp hE
  obtain ⟨r, hr, t, ht, rfl⟩ := mem_prod_iff.mp hp
  obtain ⟨U, _, W, _, rfl⟩ := mem_prod_iff.mp (hF r hr)
  exact ⟨U, W, hr, t, ht, by simp⟩

namespace IsCompleteNamedTheory

theorem model_inseparable_of_separationOmission (hAC : InternalChoice V) {D R j B G P U W : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B (⋃ˢ G))
    (hD : IsNonempty D) (hj : j ∈ (ω : V) ^ D) (hU : U ⊆ D) (hW : W ⊆ D)
    (hmeet : ∀ t ∈ (namedUnaryDefinitionQueries : V), ∃ A ∈ G, A ∈ namedSeparationOmissionDense P j U W t) :
    Schmerl.IsCodedInseparable (namedTheoryModel (⋃ˢ G))
      (graphImage (compose j (namedTheoryProjection (⋃ˢ G))) U)
      (graphImage (compose j (namedTheoryProjection (⋃ˢ G))) W) := by
  let q := namedTheoryProjection (⋃ˢ G)
  let f := compose j q
  have hq : q ∈ structureDomain (namedTheoryModel (⋃ˢ G)) ^ (ω : V) := namedTheoryProjection_mem _
  have hf : f ∈ structureDomain (namedTheoryModel (⋃ˢ G)) ^ D := compose_function hj hq
  let : IsFunction f := IsFunction.of_mem hf
  have himage {X x : V} (hXD : X ⊆ D) (hx : x ∈ X) : f ‘ x ∈ graphImage f X :=
    (mem_graphImage_iff _ _ _).mpr ⟨x, hx, kpair_value_mem (by rw [domain_eq_of_mem_function hf]; exact hXD x hx)⟩
  refine ⟨graphImage_subset hf, graphImage_subset hf, ?_⟩
  rintro ⟨A, hA, hUA, hWA⟩
  obtain ⟨_, n, hn, φ, hφ, b, hb, hdef⟩ := hA
  obtain ⟨c, hc, hcb⟩ := namedTheoryAssignment_lift hAC hb
  let t := ⟨⟨n, φ⟩ₖ, c⟩ₖ
  have ht : t ∈ (namedUnaryDefinitionQueries : V) := pair_mem_namedUnaryDefinitionQueries.mpr ⟨hn, hφ, hc⟩
  have hinst (x : V) (hx : x ∈ D) :
      NamedHolds membershipLanguageCode (namedTheoryModel (⋃ˢ G)) q (namedUnaryQueryInstance t (j ‘ x)) ↔
        Schmerl.codedSatisfies (namedTheoryModel (⋃ˢ G)) (succ n) φ (assignmentPrepend n b (f ‘ x)) := by
    rw [namedUnaryQueryInstance_holds hq ht (function_value_mem hj hx)]
    simp only [t, Schmerl.definitionParameterCount_pair, Schmerl.definitionFormula_pair, Schmerl.definitionTuple_pair]
    rw [show compose c q = b from hcb, show f ‘ x = q ‘ (j ‘ x) from value_compose_of_mem_function hj hq hx]
  obtain ⟨C, hCG, hC⟩ := hmeet t ht
  rcases ((mem_namedSeparationOmissionDense _ _ _ _ _ _).mp hC).2 with ⟨x, hx, hp⟩ | ⟨x, hx, hp⟩
  · have hv := namedUnaryQueryInstance_valid ht (function_value_mem hj (hU x hx))
    have hpT := mem_sUnion_iff.mpr ⟨C, hCG, hp⟩
    have hpH := (h.model_named_truth hD (namedNegation_mem membershipLanguageCode_valid hv)).mp hpT
    have hnot := (namedHolds_negation membershipLanguageCode_valid hq hv).mp hpH
    apply hnot
    apply (hinst x (hU x hx)).mpr
    exact (hdef _ (function_value_mem hf (hU x hx))).mp (hUA _ (himage hU hx))
  · have hv := namedUnaryQueryInstance_valid ht (function_value_mem hj (hW x hx))
    have hpT := mem_sUnion_iff.mpr ⟨C, hCG, hp⟩
    have hpH := (h.model_named_truth hD hv).mp hpT
    exact hWA _ (himage hW hx)
      ((hdef _ (function_value_mem hf (hW x hx))).mpr ((hinst x (hW x hx)).mp hpH))

theorem model_preserves_inseparable_of_family (hAC : InternalChoice V) {D R j B G P F U W : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B (⋃ˢ G))
    (hD : IsNonempty D) (hj : j ∈ (ω : V) ^ D)
    (hmeet : ∀ E ∈ namedSeparationOmissionFamily P j F, ∃ A ∈ G, A ∈ E)
    (hpair : ⟨U, W⟩ₖ ∈ F) (hUW : Schmerl.IsCodedInseparable (binaryRelationStructureCode D R) U W) :
    Schmerl.IsCodedInseparable (namedTheoryModel (⋃ˢ G))
      (graphImage (compose j (namedTheoryProjection (⋃ˢ G))) U)
      (graphImage (compose j (namedTheoryProjection (⋃ˢ G))) W) :=
  h.model_inseparable_of_separationOmission hAC hD hj
    (by simpa only [binaryRelationStructureCode_domain] using hUW.1)
    (by simpa only [binaryRelationStructureCode_domain] using hUW.2.1)
    (fun t ht ↦ hmeet _ (namedSeparationOmissionDense_mem_family hpair ht))

theorem model_elementary_inseparableFamily (hAC : InternalChoice V) {D R j B G P F : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B (⋃ˢ G))
    (hD : IsNonempty D) (hj : j ∈ (ω : V) ^ D)
    (hd : namedElementaryDiagram membershipLanguageCode (binaryRelationStructureCode D R) j ⊆ B)
    (hmeet : ∀ E ∈ namedSeparationOmissionFamily P j F, ∃ A ∈ G, A ∈ E) :
    IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D R)
      (namedTheoryModel (⋃ˢ G)) (compose j (namedTheoryProjection (⋃ˢ G))) ∧
    ∀ U W, ⟨U, W⟩ₖ ∈ F → Schmerl.IsCodedInseparable (binaryRelationStructureCode D R) U W →
      Schmerl.IsCodedInseparable (namedTheoryModel (⋃ˢ G))
        (graphImage (compose j (namedTheoryProjection (⋃ˢ G))) U)
        (graphImage (compose j (namedTheoryProjection (⋃ˢ G))) W) :=
  ⟨h.model_elementary hD hj hd, fun _ _ hpair hUW ↦ h.model_preserves_inseparable_of_family hAC hD hj hmeet hpair hUW⟩

end IsCompleteNamedTheory
end ZFVP
