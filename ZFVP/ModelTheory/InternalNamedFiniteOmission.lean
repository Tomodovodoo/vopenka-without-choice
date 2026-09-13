import ZFVP.ModelTheory.InternalNamedModel
import ZFVP.ModelTheory.SchmerlCodedExtensionRelabeling

/-! Actual omission tasks for old internally finite sets. Meeting these
candidate sets implies finite-trace preservation; density is a separate claim. -/

set_option autoImplicit false

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local irreducible] Schmerl.codedUnary Schmerl.codedMemberTrace
attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₅.comp

noncomputable def namedMembershipEntry (l r : V) : V :=
  ⟨⟨(2 : V), encodeMembershipFormula (“x a. x ∈ a” : SetTheorySemisentence 2)⟩ₖ, standardTuple ![l, r]⟩ₖ

noncomputable def namedEqualityEntry (l r : V) : V :=
  ⟨⟨(2 : V), standardEqualityCode⟩ₖ, standardTuple ![l, r]⟩ₖ

instance namedMembershipEntry_definable : ℒₛₑₜ-function₂[V] namedMembershipEntry := by
  unfold namedMembershipEntry standardTuple
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
  definability

instance namedEqualityEntry_definable : ℒₛₑₜ-function₂[V] namedEqualityEntry := by
  unfold namedEqualityEntry standardTuple
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
  definability

theorem namedMembershipEntry_valid {l r : V} (hl : l ∈ (ω : V)) (hr : r ∈ (ω : V)) :
    namedMembershipEntry l r ∈ namedFormulaSet membershipLanguageCode (ω : V) :=
  (pair_mem_namedFormulaSet_iff membershipLanguageCode_valid).mpr
    ⟨encodeMembershipFormula_mem _, standardTuple_mem_function _ (by simp [hl, hr])⟩

theorem namedEqualityEntry_valid {l r : V} (hl : l ∈ (ω : V)) (hr : r ∈ (ω : V)) :
    namedEqualityEntry l r ∈ namedFormulaSet membershipLanguageCode (ω : V) :=
  (pair_mem_namedFormulaSet_iff membershipLanguageCode_valid).mpr
    ⟨standardEqualityCode_mem membershipLanguageCode_valid ∅, standardTuple_mem_function _ (by simp [hl, hr])⟩

theorem namedMembershipEntry_holds {N f l r : V} (hf : f ∈ structureDomain N ^ (ω : V))
    (hl : l ∈ (ω : V)) (hr : r ∈ (ω : V)) :
    NamedHolds membershipLanguageCode N f (namedMembershipEntry l r) ↔
      Schmerl.codedMember N (f ‘ l) (f ‘ r) := by
  let : IsFunction f := IsFunction.of_mem hf
  rw [namedMembershipEntry, namedHolds_pair, compose_standardTuple _ _ (fun i ↦ by
    rw [domain_eq_of_mem_function hf]
    exact (by simp [hl, hr] : ∀ i : Fin 2, (![l, r] i) ∈ (ω : V)) i)]
  have he : (fun i : Fin 2 ↦ f ‘ (![l, r] i)) = ![f ‘ l, f ‘ r] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  rfl

theorem namedEqualityEntry_holds {N f l r : V} (hN : IsStructureCode membershipLanguageCode N)
    (hf : f ∈ structureDomain N ^ (ω : V)) (hl : l ∈ (ω : V)) (hr : r ∈ (ω : V)) :
    NamedHolds membershipLanguageCode N f (namedEqualityEntry l r) ↔ f ‘ l = f ‘ r := by
  have hb : standardTuple ![l, r] ∈ (ω : V) ^ (2 : V) := standardTuple_mem_function _ (by simp [hl, hr])
  have h0 : (standardTuple ![l, r]) ‘ (0 : V) = l := value_standardTuple ![l, r] 0
  have h1 : (standardTuple ![l, r]) ‘ (1 : V) = r := value_standardTuple ![l, r] 1
  rw [namedEqualityEntry, namedHolds_pair, satisfies_standardEqualityCode hN (compose_function hb hf),
    value_compose_of_mem_function hb hf (show (0 : V) ∈ (2 : V) from by simp),
    value_compose_of_mem_function hb hf (show (1 : V) ∈ (2 : V) from by simp), h0, h1]

noncomputable def namedFiniteOmissionDense (P M j a l : V) : V :=
  {A ∈ P ; namedNegation membershipLanguageCode (namedMembershipEntry l (j ‘ a)) ∈ A ∨
    ∃ x ∈ Schmerl.codedMemberTrace M a, namedEqualityEntry l (j ‘ x) ∈ A}

instance namedFiniteOmissionDense_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (namedFiniteOmissionDense (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun U P M j a l : V ↦ ∀ A, A ∈ U ↔ A ∈ P ∧
    (namedNegation membershipLanguageCode (namedMembershipEntry l (j ‘ a)) ∈ A ∨
      ∃ x ∈ Schmerl.codedMemberTrace M a, namedEqualityEntry l (j ‘ x) ∈ A)) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [namedFiniteOmissionDense, mem_sep_iff]
  rfl

theorem mem_namedFiniteOmissionDense (P M j a l A : V) : A ∈ namedFiniteOmissionDense P M j a l ↔
    A ∈ P ∧ (namedNegation membershipLanguageCode (namedMembershipEntry l (j ‘ a)) ∈ A ∨
      ∃ x ∈ Schmerl.codedMemberTrace M a, namedEqualityEntry l (j ‘ x) ∈ A) := mem_sep_iff

theorem namedFiniteOmissionDense_subset (P M j a l : V) : namedFiniteOmissionDense P M j a l ⊆ P :=
  fun _ hA ↦ (mem_sep_iff.mp hA).1

noncomputable def namedFiniteOmissionTasks (M : V) : V :=
  {p ∈ structureDomain M ×ˢ (ω : V) ;
    Schmerl.codedUnary M (encodeMembershipFormula internallyFiniteFormula) (kpair.π₁ p)}

instance namedFiniteOmissionTasks_definable : ℒₛₑₜ-function₁[V] namedFiniteOmissionTasks := by
  have h : ℒₛₑₜ-relation[V] (fun I M ↦ ∀ p, p ∈ I ↔ p ∈ structureDomain M ×ˢ (ω : V) ∧
    Schmerl.codedUnary M (encodeMembershipFormula internallyFiniteFormula) (kpair.π₁ p)) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [namedFiniteOmissionTasks, mem_sep_iff]
  rfl

theorem pair_mem_namedFiniteOmissionTasks (M a l : V) : ⟨a, l⟩ₖ ∈ namedFiniteOmissionTasks M ↔
    (a ∈ structureDomain M ∧ l ∈ (ω : V)) ∧
      Schmerl.codedUnary M (encodeMembershipFormula internallyFiniteFormula) a := by
  simp only [namedFiniteOmissionTasks, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair]

noncomputable def namedFiniteOmissionFamily (P M j : V) : V :=
  repl (fun p ↦ namedFiniteOmissionDense P M j (kpair.π₁ p) (kpair.π₂ p)) (by definability)
    (namedFiniteOmissionTasks M)

instance namedFiniteOmissionFamily_definable : ℒₛₑₜ-function₃[V] namedFiniteOmissionFamily := by
  have h : ℒₛₑₜ-relation₄[V] (fun F P M j ↦ ∀ U, U ∈ F ↔
    ∃ p ∈ namedFiniteOmissionTasks M, U = namedFiniteOmissionDense P M j (kpair.π₁ p) (kpair.π₂ p)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [namedFiniteOmissionFamily, repl_spec]
  rfl

theorem namedFiniteOmissionTasks_countable {M : V} (hM : IsInternallyCountable (structureDomain M)) :
    IsInternallyCountable (namedFiniteOmissionTasks M) :=
  internallyCountable_subset ((prod_cardLE_prod hM internallyCountable_omega).trans omega_prod_cardLE_omega)
    (fun _ hp ↦ (mem_sep_iff.mp hp).1)

theorem namedFiniteOmissionFamily_countable {P M j : V} (hM : IsInternallyCountable (structureDomain M)) :
    IsInternallyCountable (namedFiniteOmissionFamily P M j) :=
  internallyCountable_repl _ _ (namedFiniteOmissionTasks_countable hM)

theorem namedFiniteOmissionDense_mem_family {P M j a l : V} (ha : a ∈ structureDomain M)
    (hfin : Schmerl.codedUnary M (encodeMembershipFormula internallyFiniteFormula) a) (hl : l ∈ (ω : V)) :
    namedFiniteOmissionDense P M j a l ∈ namedFiniteOmissionFamily P M j :=
  (repl_spec _).mpr ⟨⟨a, l⟩ₖ, (pair_mem_namedFiniteOmissionTasks _ _ _).mpr ⟨⟨ha, hl⟩, hfin⟩, by simp⟩

theorem namedFiniteOmissionFamily_cases {P M j U : V} (hU : U ∈ namedFiniteOmissionFamily P M j) :
    ∃ a ∈ structureDomain M, Schmerl.codedUnary M (encodeMembershipFormula internallyFiniteFormula) a ∧
      ∃ l ∈ (ω : V), U = namedFiniteOmissionDense P M j a l := by
  obtain ⟨p, hp, rfl⟩ := (repl_spec _).mp hU
  obtain ⟨a, ha, l, hl, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hp).1
  have hfin := ((pair_mem_namedFiniteOmissionTasks M a l).mp hp).2
  exact ⟨a, ha, hfin, l, hl, by simp⟩

theorem namedTheoryProjection_range (T : V) :
    range (namedTheoryProjection T) = structureDomain (namedTheoryModel T) := by
  simp only [namedTheoryProjection, namedTheoryModel, internalQuotientProjection_range, internalQuotientStructure_domain]

namespace IsCompleteNamedTheory

theorem model_finiteMember_source_witness {D R j B G P a y : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B (⋃ˢ G))
    (hD : IsNonempty D) (hj : j ∈ (ω : V) ^ D)
    (ha : a ∈ D)
    (hmeet : ∀ l ∈ (ω : V), ∃ A ∈ G, A ∈ namedFiniteOmissionDense P (binaryRelationStructureCode D R) j a l)
    (hy : y ∈ structureDomain (namedTheoryModel (⋃ˢ G)))
    (hmem : Schmerl.codedMember (namedTheoryModel (⋃ˢ G)) y ((compose j (namedTheoryProjection (⋃ˢ G))) ‘ a)) :
    ∃ x ∈ Schmerl.codedMemberTrace (binaryRelationStructureCode D R) a,
      y = (compose j (namedTheoryProjection (⋃ˢ G))) ‘ x := by
  have hq := namedTheoryProjection_mem (⋃ˢ G)
  let : IsFunction (namedTheoryProjection (⋃ˢ G)) := IsFunction.of_mem hq
  have hyRange : y ∈ range (namedTheoryProjection (⋃ˢ G)) := namedTheoryProjection_range (⋃ˢ G) ▸ hy
  obtain ⟨l, hly⟩ := mem_range_iff.mp hyRange
  have hl := (mem_of_mem_functions hq hly).1
  have hlyval : (namedTheoryProjection (⋃ˢ G)) ‘ l = y := value_eq_of_kpair_mem hly
  have hja := function_value_mem hj ha
  obtain ⟨A, hAG, hA⟩ := hmeet l hl
  rcases ((mem_namedFiniteOmissionDense _ _ _ _ _ _).mp hA).2 with hn | ⟨x, hx, he⟩
  · have hv := namedMembershipEntry_valid hl hja
    have hnT := mem_sUnion_iff.mpr ⟨A, hAG, hn⟩
    have hnH := (h.model_named_truth hD (namedNegation_mem membershipLanguageCode_valid hv)).mp hnT
    have hnot := (namedHolds_negation membershipLanguageCode_valid hq hv).mp hnH
    exfalso
    apply hnot
    apply (namedMembershipEntry_holds hq hl hja).mpr
    rw [hlyval]
    simpa only [value_compose_of_mem_function hj hq ha] using hmem
  · have hxD : x ∈ D := by
      simpa only [binaryRelationStructureCode_domain] using (Schmerl.mem_codedMemberTrace _ _ _).mp hx |>.1
    have hjx := function_value_mem hj hxD
    have heT := mem_sUnion_iff.mpr ⟨A, hAG, he⟩
    have heH := (h.model_named_truth hD (namedEqualityEntry_valid hl hjx)).mp heT
    have heq := (namedEqualityEntry_holds (namedTheoryModel_valid _) hq hl hjx).mp heH
    refine ⟨x, hx, ?_⟩
    rw [value_compose_of_mem_function hj hq hxD, ← hlyval]
    exact heq

theorem model_finiteTraceEmbedding_of_omissionFamily {D R j B G P : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B (⋃ˢ G))
    (hD : IsNonempty D) (hj : j ∈ (ω : V) ^ D)
    (hmeet : ∀ U ∈ namedFiniteOmissionFamily P (binaryRelationStructureCode D R) j, ∃ A ∈ G, A ∈ U) :
    Schmerl.IsCodedFiniteTraceEmbedding (binaryRelationStructureCode D R) (namedTheoryModel (⋃ˢ G))
      (compose j (namedTheoryProjection (⋃ˢ G))) := by
  intro a ha hfin y hy hmem
  have haD : a ∈ D := by simpa only [binaryRelationStructureCode_domain] using ha
  obtain ⟨x, hx, rfl⟩ := h.model_finiteMember_source_witness hD hj haD
    (fun l hl ↦ hmeet _ (namedFiniteOmissionDense_mem_family ha hfin hl)) hy hmem
  have hxD : x ∈ D := by
    simpa only [binaryRelationStructureCode_domain] using (Schmerl.mem_codedMemberTrace _ _ _).mp hx |>.1
  exact value_mem_range (compose_function hj (namedTheoryProjection_mem _)) hxD

theorem model_elementary_finiteTrace_of_omissionFamily {D R j B G P : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B (⋃ˢ G))
    (hD : IsNonempty D) (hj : j ∈ (ω : V) ^ D)
    (hd : namedElementaryDiagram membershipLanguageCode (binaryRelationStructureCode D R) j ⊆ B)
    (hmeet : ∀ U ∈ namedFiniteOmissionFamily P (binaryRelationStructureCode D R) j, ∃ A ∈ G, A ∈ U) :
    IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D R)
      (namedTheoryModel (⋃ˢ G)) (compose j (namedTheoryProjection (⋃ˢ G))) ∧
    Schmerl.IsCodedFiniteTraceEmbedding (binaryRelationStructureCode D R) (namedTheoryModel (⋃ˢ G))
      (compose j (namedTheoryProjection (⋃ˢ G))) :=
  ⟨h.model_elementary hD hj hd, h.model_finiteTraceEmbedding_of_omissionFamily hD hj hmeet⟩

theorem exists_literal_finiteEndExtension_of_omissionFamily {D R j B G P : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B (⋃ˢ G))
    (hM : IsCodedZFModel (binaryRelationStructureCode D R)) (hj : j ∈ (ω : V) ^ D)
    (hd : namedElementaryDiagram membershipLanguageCode (binaryRelationStructureCode D R) j ⊆ B)
    (hmeet : ∀ U ∈ namedFiniteOmissionFamily P (binaryRelationStructureCode D R) j, ∃ A ∈ G, A ∈ U) :
    ∃ A S : V, D ⊆ A ∧ S ⊆ A ×ˢ A ∧ IsInternallyCountable A ∧
      IsCodedZFModel (binaryRelationStructureCode A S) ∧
      IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D R)
        (binaryRelationStructureCode A S) (SetTheory.identity D) ∧
      Schmerl.IsCodedFiniteEndExtension (binaryRelationStructureCode D R) (binaryRelationStructureCode A S) := by
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hM.valid.domain_nonempty
  obtain ⟨he, ht⟩ := h.model_elementary_finiteTrace_of_omissionFamily hD hj hd hmeet
  exact Schmerl.exists_literal_coded_finite_end_extension he
    (internalQuotientCarrier_countable internallyCountable_omega) hM ht

end IsCompleteNamedTheory
end ZFVP
