import ZFVP.ModelTheory.FiniteSatisfactionCode
import ZFVP.Syntax.TermSubstitutionSemantics

/-! Extracting an elementary embedding from the finite satisfaction codes.
Pointwise fixing of the common label copy is an explicit hypothesis. No
endomorphism-rigidity theorem is assumed or proved by this construction.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The variables of a relation atom of standard finite arity. -/
noncomputable def standardRelationArguments (k : ℕ) : V :=
  standardTuple (fun i : Fin k ↦ boundVarCode (i.val : V))

noncomputable def standardRelationCode (k : ℕ) (r : V) : V :=
  atomCode (relationToken r) (standardRelationArguments k)

theorem standardRelationArguments_typed {L : V} (hL : IsLanguageCode L) (Γ : V) (k : ℕ) :
    standardRelationArguments k ∈ termSet L Γ (k : V) ^ (k : V) :=
  standardTuple_mem_function _ (fun i ↦
    (termSet_closed hL (by simp) Γ).1 _ (natCast_mem_of_lt i.isLt))

theorem standardRelationCode_mem {L r : V} (hL : IsLanguageCode L) (Γ : V) {k : ℕ}
    (hr : r ∈ relationSymbols L) (har : (relationArities L) ‘ r = (k : V)) :
    standardRelationCode k r ∈ formulaSet L Γ (k : V) := by
  apply (atomCode_mem_iff hL).mpr
  refine ⟨by simp, Or.inr ⟨r, hr, rfl, ?_⟩⟩
  rw [har]
  exact standardRelationArguments_typed hL Γ k

theorem evaluatedArguments_standardRelationArguments {L : V} (hL : IsLanguageCode L)
    (Γ M E b : V) (k : ℕ) :
    evaluatedArguments L Γ M E (k : V) b (standardRelationArguments k) =
      standardTuple (fun i : Fin k ↦ b ‘ (i.val : V)) := by
  unfold evaluatedArguments evaluateWithFreeAssignment standardRelationArguments
  rw [compose_standardTuple _ _ (fun i ↦ by
    simpa using (termSet_closed hL (by simp) Γ).1 _ (natCast_mem_of_lt i.isLt))]
  congr 1
  funext i
  exact termEvaluation_boundVar hL (by simp) Γ M b E (natCast_mem_of_lt i.isLt)

theorem satisfies_standardRelationCode {L M Γ E r b : V} (hM : IsStructureCode L M)
    {k : ℕ} (hr : r ∈ relationSymbols L) (har : (relationArities L) ‘ r = (k : V))
    (hb : b ∈ structureDomain M ^ (k : V)) :
    Satisfies L Γ M E (k : V) (standardRelationCode k r) b ↔
      standardTuple (fun i : Fin k ↦ b ‘ (i.val : V)) ∈ (structureRelations M) ‘ r := by
  have hargs : IsAtomicArguments L Γ (k : V) (relationToken r) (standardRelationArguments k) := by
    refine Or.inr ⟨r, hr, rfl, ?_⟩
    rw [har]
    exact standardRelationArguments_typed hM.language Γ k
  rw [standardRelationCode, satisfies_atom hM.language (by simp) hargs hb,
    atomicHolds_relation, and_iff_right hr,
    evaluatedArguments_standardRelationArguments hM.language]

theorem IsCodedElementaryEmbedding.relation_standardTuple {L M N f r : V}
    (h : IsCodedElementaryEmbedding L M N f) {k : ℕ}
    (hr : r ∈ relationSymbols L) (har : (relationArities L) ‘ r = (k : V))
    (v : Fin k → V) (hv : ∀ i, v i ∈ structureDomain M) :
    standardTuple v ∈ (structureRelations M) ‘ r ↔
      standardTuple (fun i ↦ f ‘ (v i)) ∈ (structureRelations N) ‘ r := by
  have hb := standardTuple_mem_function v hv
  have ht := h.satisfies_iff (by simp) (standardRelationCode_mem h.source.language ∅ hr har) hb
  rw [satisfies_standardRelationCode h.source hr har hb,
    satisfies_standardRelationCode h.target hr har (compose_function hb h.function)] at ht
  have : IsFunction f := IsFunction.of_mem h.function
  rw [compose_standardTuple v f (fun i ↦ by
    simpa only [domain_eq_of_mem_function h.function] using hv i)] at ht
  simpa only [value_standardTuple] using ht

theorem satisfactionCodeLanguage_symbol {r : V} (hr : r ∈ (7 : V)) :
    r ∈ relationSymbols (satisfactionCodeLanguage : V) := by
  simpa only [satisfactionCodeLanguage, relationSymbols_code] using hr

theorem satisfactionCodeLanguage_arity {r : V} (hr : r ∈ (7 : V)) :
    (relationArities (satisfactionCodeLanguage : V)) ‘ r = satisfactionCodeArity r := by
  simp only [satisfactionCodeLanguage, relationArities_code, satisfactionCodeArities]
  exact value_definableGraph _ _ _ hr

/-- Atomic relation preservation, expressed in the raw predicates of the finite code. -/
theorem IsCodedElementaryEmbedding.finiteSatisfaction_relation_tuple {L M N T e r : V}
    (h : IsCodedElementaryEmbedding satisfactionCodeLanguage
      (finiteSatisfactionCode L M T) (finiteSatisfactionCode L N T) e)
    {k : ℕ} (hr : r ∈ (7 : V)) (har : satisfactionCodeArity r = (k : V))
    (v : Fin k → V) (hv : ∀ i, v i ∈ satisfactionCodeDomain L M) :
    SatisfactionCodeHolds L M T r (standardTuple v) ↔
      SatisfactionCodeHolds L N T r (standardTuple (fun i ↦ e ‘ (v i))) := by
  have hdom : ∀ i, v i ∈ structureDomain (finiteSatisfactionCode L M T) := by
    simpa only [finiteSatisfactionCode_domain] using hv
  have ht := h.relation_standardTuple (satisfactionCodeLanguage_symbol hr)
    ((satisfactionCodeLanguage_arity hr).trans har) v hdom
  rw [finiteSatisfactionCode_relation hr, finiteSatisfactionCode_relation hr] at ht
  have hsrc : standardTuple v ∈ satisfactionCodeDomain L M ^ satisfactionCodeArity r := by
    rw [har]
    exact standardTuple_mem_function v hv
  have htar : standardTuple (fun i ↦ e ‘ (v i)) ∈
      satisfactionCodeDomain L N ^ satisfactionCodeArity r := by
    rw [har]
    exact standardTuple_mem_function _ (fun i ↦ by
      simpa only [finiteSatisfactionCode_domain] using function_value_mem h.function (hdom i))
  exact (and_iff_right hsrc).symm.trans (ht.trans (and_iff_right htar))

theorem satisfactionCodeArity_element : satisfactionCodeArity (1 : V) = (1 : V) := by
  have h1 : (1 : V) ∈ (3 : V) := natCast_mem_of_lt (show 1 < 3 by decide)
  simp only [satisfactionCodeArity, ite_eq_left h1]

theorem satisfactionCodeArity_assignment : satisfactionCodeArity (2 : V) = (1 : V) := by
  have h2 : (2 : V) ∈ (3 : V) := natCast_mem_of_lt (show 2 < 3 by decide)
  simp only [satisfactionCodeArity, ite_eq_left h2]

theorem IsCodedElementaryEmbedding.finiteSatisfaction_element_image {L M N T e a : V}
    (h : IsCodedElementaryEmbedding satisfactionCodeLanguage
      (finiteSatisfactionCode L M T) (finiteSatisfactionCode L N T) e)
    (ha : a ∈ structureDomain M) :
    ∃ b ∈ structureDomain N, e ‘ (⟨1, a⟩ₖ : V) = ⟨1, b⟩ₖ := by
  have h1 : (1 : V) ∈ (7 : V) := natCast_mem_of_lt (show 1 < 7 by decide)
  have ht := h.finiteSatisfaction_relation_tuple h1 satisfactionCodeArity_element
    ![⟨1, a⟩ₖ] (by simpa using element_mem_satisfactionCodeDomain (L := L) ha)
  rw [satisfactionCodeHolds_elements, satisfactionCodeHolds_elements] at ht
  have hs : (standardTuple ![(⟨1, a⟩ₖ : V)]) ‘ (0 : V) = ⟨1, a⟩ₖ :=
    value_standardTuple _ (0 : Fin 1)
  have he : (standardTuple (fun i ↦ e ‘ (![(⟨1, a⟩ₖ : V)] i))) ‘ (0 : V) = e ‘ ⟨1, a⟩ₖ :=
    value_standardTuple _ (0 : Fin 1)
  rw [hs, he] at ht
  have himg := ht.mp (kpair_mem_iff.mpr ⟨by simp, ha⟩)
  obtain ⟨x, hx, b, hb, heq⟩ := mem_prod_iff.mp himg
  have hx1 : x = (1 : V) := by simpa using hx
  exact ⟨b, hb, heq.trans (by rw [hx1])⟩

theorem IsCodedElementaryEmbedding.finiteSatisfaction_assignment_image {L M N T e t : V}
    (h : IsCodedElementaryEmbedding satisfactionCodeLanguage
      (finiteSatisfactionCode L M T) (finiteSatisfactionCode L N T) e)
    (ht : t ∈ finiteSequences (structureDomain M)) :
    ∃ u ∈ finiteSequences (structureDomain N), e ‘ (⟨2, t⟩ₖ : V) = ⟨2, u⟩ₖ := by
  have h2 : (2 : V) ∈ (7 : V) := natCast_mem_of_lt (show 2 < 7 by decide)
  have hs := h.finiteSatisfaction_relation_tuple h2 satisfactionCodeArity_assignment
    ![⟨2, t⟩ₖ] (by simpa using assignment_mem_satisfactionCodeDomain (L := L) ht)
  rw [satisfactionCodeHolds_assignments, satisfactionCodeHolds_assignments] at hs
  have hs0 : (standardTuple ![(⟨2, t⟩ₖ : V)]) ‘ (0 : V) = ⟨2, t⟩ₖ :=
    value_standardTuple _ (0 : Fin 1)
  have he0 : (standardTuple (fun i ↦ e ‘ (![(⟨2, t⟩ₖ : V)] i))) ‘ (0 : V) = e ‘ ⟨2, t⟩ₖ :=
    value_standardTuple _ (0 : Fin 1)
  rw [hs0, he0] at hs
  have himg := hs.mp (kpair_mem_iff.mpr ⟨by simp, ht⟩)
  obtain ⟨x, hx, u, hu, heq⟩ := mem_prod_iff.mp himg
  have hx2 : x = (2 : V) := by simpa using hx
  exact ⟨u, hu, heq.trans (by rw [hx2])⟩

/-- The internal graph obtained by restricting to the element sort and removing its tag. -/
noncomputable def finiteSatisfactionElementMap (M e : V) : V :=
  definableGraph (structureDomain M) (fun a ↦ kpair.π₂ (e ‘ (⟨1, a⟩ₖ : V))) (by definability)

theorem finiteSatisfactionElementMap_value {M e a : V} (ha : a ∈ structureDomain M) :
    (finiteSatisfactionElementMap M e) ‘ a = kpair.π₂ (e ‘ (⟨1, a⟩ₖ : V)) :=
  value_definableGraph _ _ _ ha

theorem IsCodedElementaryEmbedding.finiteSatisfaction_elementMap_function {L M N T e : V}
    (h : IsCodedElementaryEmbedding satisfactionCodeLanguage
      (finiteSatisfactionCode L M T) (finiteSatisfactionCode L N T) e) :
    finiteSatisfactionElementMap M e ∈ structureDomain N ^ structureDomain M := by
  apply definableGraph_mem_function_of_mapsTo
  intro a ha
  obtain ⟨b, hb, heq⟩ := h.finiteSatisfaction_element_image ha
  simpa only [heq, kpair.π₂_kpair] using hb

theorem IsCodedElementaryEmbedding.finiteSatisfaction_elementMap_tag {L M N T e a : V}
    (h : IsCodedElementaryEmbedding satisfactionCodeLanguage
      (finiteSatisfactionCode L M T) (finiteSatisfactionCode L N T) e)
    (ha : a ∈ structureDomain M) :
    e ‘ (⟨1, a⟩ₖ : V) = ⟨1, (finiteSatisfactionElementMap M e) ‘ a⟩ₖ := by
  obtain ⟨b, hb, heq⟩ := h.finiteSatisfaction_element_image ha
  rw [finiteSatisfactionElementMap_value ha, heq, kpair.π₂_kpair]

/-- The underlying assignment represented by the image of an assignment vertex. -/
noncomputable def finiteSatisfactionAssignmentImage (e t : V) : V := kpair.π₂ (e ‘ (⟨2, t⟩ₖ : V))

theorem IsCodedElementaryEmbedding.finiteSatisfaction_assignmentImage_mem {L M N T e t : V}
    (h : IsCodedElementaryEmbedding satisfactionCodeLanguage
      (finiteSatisfactionCode L M T) (finiteSatisfactionCode L N T) e)
    (ht : t ∈ finiteSequences (structureDomain M)) :
    finiteSatisfactionAssignmentImage e t ∈ finiteSequences (structureDomain N) := by
  obtain ⟨u, hu, heq⟩ := h.finiteSatisfaction_assignment_image ht
  simpa only [finiteSatisfactionAssignmentImage, heq, kpair.π₂_kpair] using hu

theorem IsCodedElementaryEmbedding.finiteSatisfaction_assignmentImage_tag {L M N T e t : V}
    (h : IsCodedElementaryEmbedding satisfactionCodeLanguage
      (finiteSatisfactionCode L M T) (finiteSatisfactionCode L N T) e)
    (ht : t ∈ finiteSequences (structureDomain M)) :
    e ‘ (⟨2, t⟩ₖ : V) = ⟨2, finiteSatisfactionAssignmentImage e t⟩ₖ := by
  obtain ⟨u, hu, heq⟩ := h.finiteSatisfaction_assignment_image ht
  simp only [finiteSatisfactionAssignmentImage, heq, kpair.π₂_kpair]

private theorem finiteCodeNumeral_eq (m n : ℕ) :
    (SetTheory.ofNat m : V) = SetTheory.ofNat n ↔ m = n := natCast_eq_iff m n

private theorem finiteCodeNumeral_mem (m n : ℕ) :
    (SetTheory.ofNat m : V) ∈ (SetTheory.ofNat n : V) ↔ m < n := natCast_mem_iff m n

theorem satisfactionCodeArity_length : satisfactionCodeArity (4 : V) = (2 : V) := by
  simp [satisfactionCodeArity, OfNat.ofNat, finiteCodeNumeral_mem, finiteCodeNumeral_eq]

theorem satisfactionCodeArity_evaluation : satisfactionCodeArity (5 : V) = (3 : V) := by
  simp [satisfactionCodeArity, OfNat.ofNat, finiteCodeNumeral_mem]

theorem satisfactionCodeArity_satisfaction : satisfactionCodeArity (6 : V) = (2 : V) := by
  simp [satisfactionCodeArity, OfNat.ofNat, finiteCodeNumeral_mem, finiteCodeNumeral_eq]

/-- Fixed natural-number labels force preservation of every internal finite length. -/
theorem IsCodedElementaryEmbedding.finiteSatisfaction_assignmentImage_length {L M N T e n t : V}
    (h : IsCodedElementaryEmbedding satisfactionCodeLanguage
      (finiteSatisfactionCode L M T) (finiteSatisfactionCode L N T) e)
    (hfix : ∀ b ∈ satisfactionLabels L, e ‘ (⟨0, b⟩ₖ : V) = ⟨0, b⟩ₖ)
    (hn : n ∈ (ω : V)) (ht : t ∈ structureDomain M ^ n) :
    domain (finiteSatisfactionAssignmentImage e t) = n := by
  have htseq := (mem_finiteSequences_iff _ _).mpr ⟨n, hn, ht⟩
  have h4 : (4 : V) ∈ (7 : V) := natCast_mem_of_lt (show 4 < 7 by decide)
  have hmap := h.relation_standardTuple (satisfactionCodeLanguage_symbol h4)
    ((satisfactionCodeLanguage_arity h4).trans satisfactionCodeArity_length)
    ![(⟨2, t⟩ₖ : V), ⟨0, ⟨0, n⟩ₖ⟩ₖ] (by
      simp only [finiteSatisfactionCode_domain, Fin.forall_fin_succ, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
      exact ⟨assignment_mem_satisfactionCodeDomain htseq,
        label_mem_satisfactionCodeDomain (natural_mem_satisfactionLabels hn)⟩)
  have hsrc := (finiteSatisfactionCode_length (L := L) (T := T) htseq hn).mpr
    (domain_eq_of_mem_function ht)
  have htar := hmap.mp hsrc
  simp only [Matrix.comp_vecCons', Matrix.empty_eq] at htar
  rw [h.finiteSatisfaction_assignmentImage_tag htseq,
    hfix _ (natural_mem_satisfactionLabels hn)] at htar
  exact (finiteSatisfactionCode_length (h.finiteSatisfaction_assignmentImage_mem htseq) hn).mp htar

theorem IsCodedElementaryEmbedding.finiteSatisfaction_assignmentImage_function {L M N T e n t : V}
    (h : IsCodedElementaryEmbedding satisfactionCodeLanguage
      (finiteSatisfactionCode L M T) (finiteSatisfactionCode L N T) e)
    (hfix : ∀ b ∈ satisfactionLabels L, e ‘ (⟨0, b⟩ₖ : V) = ⟨0, b⟩ₖ)
    (hn : n ∈ (ω : V)) (ht : t ∈ structureDomain M ^ n) :
    finiteSatisfactionAssignmentImage e t ∈ structureDomain N ^ n := by
  have htseq := (mem_finiteSequences_iff _ _).mpr ⟨n, hn, ht⟩
  have hf := ((mem_finiteSequences_iff_domain _ _).mp (h.finiteSatisfaction_assignmentImage_mem htseq)).2
  rwa [h.finiteSatisfaction_assignmentImage_length hfix hn ht] at hf

/-- Evaluation fixes every coordinate of every internal finite assignment image. -/
theorem IsCodedElementaryEmbedding.finiteSatisfaction_assignmentImage_value {L M N T e n t i : V}
    (h : IsCodedElementaryEmbedding satisfactionCodeLanguage
      (finiteSatisfactionCode L M T) (finiteSatisfactionCode L N T) e)
    (hfix : ∀ b ∈ satisfactionLabels L, e ‘ (⟨0, b⟩ₖ : V) = ⟨0, b⟩ₖ)
    (hn : n ∈ (ω : V)) (ht : t ∈ structureDomain M ^ n) (hi : i ∈ n) :
    (finiteSatisfactionAssignmentImage e t) ‘ i = (finiteSatisfactionElementMap M e) ‘ (t ‘ i) := by
  have htseq := (mem_finiteSequences_iff _ _).mpr ⟨n, hn, ht⟩
  have hidom : i ∈ domain t := by rwa [domain_eq_of_mem_function ht]
  have hiω : i ∈ (ω : V) := IsTransitive.transitive _ hn i hi
  have ha : t ‘ i ∈ structureDomain M := function_value_mem ht hi
  have h5 : (5 : V) ∈ (7 : V) := natCast_mem_of_lt (show 5 < 7 by decide)
  have hmap := h.relation_standardTuple (satisfactionCodeLanguage_symbol h5)
    ((satisfactionCodeLanguage_arity h5).trans satisfactionCodeArity_evaluation)
    ![(⟨2, t⟩ₖ : V), ⟨0, ⟨0, i⟩ₖ⟩ₖ, ⟨1, t ‘ i⟩ₖ] (by
      simp only [finiteSatisfactionCode_domain, Fin.forall_fin_succ, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
      exact ⟨assignment_mem_satisfactionCodeDomain htseq,
        label_mem_satisfactionCodeDomain (natural_mem_satisfactionLabels hiω),
        element_mem_satisfactionCodeDomain ha⟩)
  have hsrc := (finiteSatisfactionCode_evaluation (L := L) (T := T) htseq hidom ha).mpr rfl
  have htar := hmap.mp hsrc
  simp only [Matrix.comp_vecCons', Matrix.empty_eq] at htar
  rw [h.finiteSatisfaction_assignmentImage_tag htseq,
    hfix _ (natural_mem_satisfactionLabels hiω), h.finiteSatisfaction_elementMap_tag ha] at htar
  have hitarget : i ∈ domain (finiteSatisfactionAssignmentImage e t) := by
    rw [h.finiteSatisfaction_assignmentImage_length hfix hn ht]
    exact hi
  exact (finiteSatisfactionCode_evaluation (h.finiteSatisfaction_assignmentImage_mem htseq) hitarget
    (function_value_mem h.finiteSatisfaction_elementMap_function ha)).mp htar

/-- The image of an assignment is exactly composition with the extracted element map. -/
theorem IsCodedElementaryEmbedding.finiteSatisfaction_assignmentImage_eq_compose {L M N T e n t : V}
    (h : IsCodedElementaryEmbedding satisfactionCodeLanguage
      (finiteSatisfactionCode L M T) (finiteSatisfactionCode L N T) e)
    (hfix : ∀ b ∈ satisfactionLabels L, e ‘ (⟨0, b⟩ₖ : V) = ⟨0, b⟩ₖ)
    (hn : n ∈ (ω : V)) (ht : t ∈ structureDomain M ^ n) :
    finiteSatisfactionAssignmentImage e t = compose t (finiteSatisfactionElementMap M e) := by
  apply function_eq_of_values (h.finiteSatisfaction_assignmentImage_function hfix hn ht)
    (compose_function ht h.finiteSatisfaction_elementMap_function)
  intro i hi
  rw [value_compose_of_mem_function ht h.finiteSatisfaction_elementMap_function hi]
  exact h.finiteSatisfaction_assignmentImage_value hfix hn ht hi

/-- Elementary embeddings of the finite codes yield elementary embeddings of the original
structures whenever they fix all common labels. This includes all internal formulas and
all internal finite assignment lengths. -/
theorem IsCodedElementaryEmbedding.finiteSatisfaction_elementary {L M N T e : V}
    (h : IsCodedElementaryEmbedding satisfactionCodeLanguage
      (finiteSatisfactionCode L M T) (finiteSatisfactionCode L N T) e)
    (hM : IsStructureCode L M) (hN : IsStructureCode L N)
    (hfix : ∀ b ∈ satisfactionLabels L, e ‘ (⟨0, b⟩ₖ : V) = ⟨0, b⟩ₖ) :
    IsCodedElementaryEmbedding L M N (finiteSatisfactionElementMap M e) := by
  refine ⟨hM, hN, h.finiteSatisfaction_elementMap_function, ?_⟩
  intro n hn φ hφ t ht
  have htseq := (mem_finiteSequences_iff _ _).mpr ⟨n, hn, ht⟩
  have h6 : (6 : V) ∈ (7 : V) := natCast_mem_of_lt (show 6 < 7 by decide)
  have hmap := h.relation_standardTuple (satisfactionCodeLanguage_symbol h6)
    ((satisfactionCodeLanguage_arity h6).trans satisfactionCodeArity_satisfaction)
    ![(⟨0, ⟨1, ⟨n, φ⟩ₖ⟩ₖ⟩ₖ : V), ⟨2, t⟩ₖ] (by
      simp only [finiteSatisfactionCode_domain, Fin.forall_fin_succ, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
      exact ⟨label_mem_satisfactionCodeDomain (formula_mem_satisfactionLabels hφ),
        assignment_mem_satisfactionCodeDomain htseq⟩)
  simp only [Matrix.comp_vecCons', Matrix.empty_eq] at hmap
  rw [hfix _ (formula_mem_satisfactionLabels hφ), h.finiteSatisfaction_assignmentImage_tag htseq,
    h.finiteSatisfaction_assignmentImage_eq_compose hfix hn ht] at hmap
  rw [finiteSatisfactionCode_satisfaction hn hφ ht,
    finiteSatisfactionCode_satisfaction hn hφ
      (compose_function ht h.finiteSatisfaction_elementMap_function)] at hmap
  exact hmap

end ZFVP
