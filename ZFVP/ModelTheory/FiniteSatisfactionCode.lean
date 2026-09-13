import ZFVP.ModelTheory.CodedElementaryEmbedding
import ZFVP.ModelTheory.ConstantStructure

/-! The canonical finite relational satisfaction code used in the first stage of
the fixed-language reduction. The seven symbols describe three sorts, the label
relation, assignment length, evaluation, and satisfaction. All objects below are
internal sets, including formulas and assignments of internally finite length.

This module constructs the code and proves its defining relations. It does not
assert existence of an endomorphism-rigid label relation or the reduction to a
single binary relation and unary marker predicate. The Foundation definability
instances permit model parameters. A uniform syntactic graph formula and its
effective complexity bound are not supplied here.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

attribute [local aesop 4 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableRel₅.comp

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Labels are natural numbers and context/formula pairs, with disjoint tags. -/
noncomputable def satisfactionLabels (L : V) : V :=
  (({0} : V) ×ˢ (ω : V)) ∪ (({1} : V) ×ˢ formulaFamily L ∅)

instance satisfactionLabels_definable : ℒₛₑₜ-function₁[V] satisfactionLabels := by
  unfold satisfactionLabels
  definability

theorem natural_mem_satisfactionLabels {L n : V} (hn : n ∈ (ω : V)) :
    (⟨0, n⟩ₖ : V) ∈ satisfactionLabels L := by
  exact mem_union_iff.mpr (Or.inl (kpair_mem_iff.mpr ⟨by simp, hn⟩))

theorem formula_mem_satisfactionLabels {L n φ : V} (hφ : φ ∈ formulaSet L ∅ n) :
    (⟨1, ⟨n, φ⟩ₖ⟩ₖ : V) ∈ satisfactionLabels L := by
  exact mem_union_iff.mpr (Or.inr (kpair_mem_iff.mpr
    ⟨by simp, (mem_formulaSet_iff L ∅ n φ).mp hφ⟩))

/-- Disjoint copies of labels, elements, and finite assignments. -/
noncomputable def satisfactionCodeDomain (L M : V) : V :=
  ((({0} : V) ×ˢ satisfactionLabels L) ∪ (({1} : V) ×ˢ structureDomain M)) ∪
    (({2} : V) ×ˢ finiteSequences (structureDomain M))

instance satisfactionCodeDomain_definable : ℒₛₑₜ-function₂[V] satisfactionCodeDomain := by
  unfold satisfactionCodeDomain
  definability

theorem label_mem_satisfactionCodeDomain {L M b : V} (hb : b ∈ satisfactionLabels L) :
    (⟨0, b⟩ₖ : V) ∈ satisfactionCodeDomain L M :=
  mem_union_iff.mpr (Or.inl (mem_union_iff.mpr
    (Or.inl (kpair_mem_iff.mpr ⟨by simp, hb⟩))))

theorem element_mem_satisfactionCodeDomain {L M a : V} (ha : a ∈ structureDomain M) :
    (⟨1, a⟩ₖ : V) ∈ satisfactionCodeDomain L M :=
  mem_union_iff.mpr (Or.inl (mem_union_iff.mpr
    (Or.inr (kpair_mem_iff.mpr ⟨by simp, ha⟩))))

theorem assignment_mem_satisfactionCodeDomain {L M t : V}
    (ht : t ∈ finiteSequences (structureDomain M)) :
    (⟨2, t⟩ₖ : V) ∈ satisfactionCodeDomain L M :=
  mem_union_iff.mpr (Or.inr (kpair_mem_iff.mpr ⟨by simp, ht⟩))

theorem satisfactionCodeDomain_nonempty (L M : V) :
    IsNonempty (satisfactionCodeDomain L M) :=
  ⟨⟨2, ∅⟩ₖ, assignment_mem_satisfactionCodeDomain (empty_mem_finiteSequences _)⟩

/-- Symbol indices `0,1,2` are unary, index `5` is ternary, and the rest binary. -/
noncomputable def satisfactionCodeArity (r : V) : V := by
  classical
  exact if r ∈ (3 : V) then 1 else if r = 5 then 3 else 2

instance satisfactionCodeArity_definable : ℒₛₑₜ-function₁[V] satisfactionCodeArity := by
  have hd : ℒₛₑₜ-relation[V] (fun a r ↦
      (r ∈ (3 : V) ∧ a = 1) ∨
      (r ∉ (3 : V) ∧ ((r = 5 ∧ a = 3) ∨ (r ≠ 5 ∧ a = 2)))) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = satisfactionCodeArity (v 1) ↔ _
  unfold satisfactionCodeArity
  split_ifs <;> simp_all

theorem satisfactionCodeArity_natural (r : V) : satisfactionCodeArity r ∈ (ω : V) := by
  unfold satisfactionCodeArity
  split_ifs
  · exact ofNat_mem_ω 1
  · exact ofNat_mem_ω 3
  · exact ofNat_mem_ω 2

noncomputable def satisfactionCodeArities : V :=
  definableGraph (7 : V) satisfactionCodeArity (by definability)

instance satisfactionCodeArities_definable :
    Language.DefinableFunction₀ ℒₛₑₜ (satisfactionCodeArities : V) := by
  have hd : ℒₛₑₜ-predicate[V] (fun a ↦ ∀ p, p ∈ a ↔
      ∃ r ∈ (7 : V), p = ⟨r, satisfactionCodeArity r⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = satisfactionCodeArities ↔ _
  rw [mem_ext_iff]
  simp only [satisfactionCodeArities, mem_definableGraph_iff]

noncomputable def satisfactionCodeLanguage : V :=
  languageCode ∅ (7 : V) ∅ satisfactionCodeArities

instance satisfactionCodeLanguage_definable :
    Language.DefinableFunction₀ ℒₛₑₜ (satisfactionCodeLanguage : V) := by
  unfold satisfactionCodeLanguage
  definability

theorem satisfactionCodeLanguage_valid : IsLanguageCode (satisfactionCodeLanguage : V) := by
  apply (isLanguageCode_iff _ _ _ _).mpr
  refine ⟨by simp [mem_function_iff], ?_⟩
  exact definableGraph_mem_function_of_mapsTo _ _ _ _ (fun r _ ↦ satisfactionCodeArity_natural r)

/-- The raw relations, before restricting tuples to the appropriate arity. -/
def SatisfactionCodeHolds (L M T r s : V) : Prop :=
  (r = 0 ∧ s ‘ (0 : V) ∈ ({0} : V) ×ˢ satisfactionLabels L) ∨
  (r = 1 ∧ s ‘ (0 : V) ∈ ({1} : V) ×ˢ structureDomain M) ∨
  (r = 2 ∧ s ‘ (0 : V) ∈ ({2} : V) ×ˢ finiteSequences (structureDomain M)) ∨
  (r = 3 ∧ ∃ b ∈ satisfactionLabels L, ∃ c ∈ satisfactionLabels L,
    s ‘ (0 : V) = ⟨0, b⟩ₖ ∧ s ‘ (1 : V) = ⟨0, c⟩ₖ ∧ ⟨b, c⟩ₖ ∈ T) ∨
  (r = 4 ∧ ∃ t ∈ finiteSequences (structureDomain M), ∃ n ∈ (ω : V),
    s ‘ (0 : V) = ⟨2, t⟩ₖ ∧ s ‘ (1 : V) = ⟨0, ⟨0, n⟩ₖ⟩ₖ ∧ domain t = n) ∨
  (r = 5 ∧ ∃ t ∈ finiteSequences (structureDomain M), ∃ i ∈ domain t,
    ∃ a ∈ structureDomain M, s ‘ (0 : V) = ⟨2, t⟩ₖ ∧
      s ‘ (1 : V) = ⟨0, ⟨0, i⟩ₖ⟩ₖ ∧ s ‘ (2 : V) = ⟨1, a⟩ₖ ∧ t ‘ i = a) ∨
  (r = 6 ∧ ∃ n ∈ (ω : V), ∃ φ ∈ formulaSet L ∅ n, ∃ t ∈ structureDomain M ^ n,
    s ‘ (0 : V) = ⟨0, ⟨1, ⟨n, φ⟩ₖ⟩ₖ⟩ₖ ∧ s ‘ (1 : V) = ⟨2, t⟩ₖ ∧
      Satisfies L ∅ M ∅ n φ t)

instance satisfactionCodeHolds_definable :
    ℒₛₑₜ-relation₅[V] SatisfactionCodeHolds := by
  unfold SatisfactionCodeHolds
  unfold Satisfies
  aesop (config := { terminal := true, maxRuleApplications := 1000 }) (rule_sets := [Definability])

noncomputable def satisfactionCodeRelation (L M T r : V) : V :=
  {s ∈ satisfactionCodeDomain L M ^ satisfactionCodeArity r ; SatisfactionCodeHolds L M T r s}

theorem mem_satisfactionCodeRelation_iff (L M T r s : V) :
    s ∈ satisfactionCodeRelation L M T r ↔
      s ∈ satisfactionCodeDomain L M ^ satisfactionCodeArity r ∧
        SatisfactionCodeHolds L M T r s := mem_sep_iff

instance satisfactionCodeRelation_definable : ℒₛₑₜ-function₄[V] satisfactionCodeRelation := by
  have hd : ℒₛₑₜ-relation₅[V] (fun a L M T r ↦ ∀ s, s ∈ a ↔
      s ∈ satisfactionCodeDomain L M ^ satisfactionCodeArity r ∧
        SatisfactionCodeHolds L M T r s) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = satisfactionCodeRelation (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [mem_satisfactionCodeRelation_iff]

noncomputable def satisfactionCodeRelations (L M T : V) : V :=
  definableGraph (7 : V) (satisfactionCodeRelation L M T) (by definability)

instance satisfactionCodeRelations_definable : ℒₛₑₜ-function₃[V] satisfactionCodeRelations := by
  have hd : ℒₛₑₜ-relation₄[V] (fun a L M T ↦ ∀ p, p ∈ a ↔
      ∃ r ∈ (7 : V), p = ⟨r, satisfactionCodeRelation L M T r⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = satisfactionCodeRelations (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [satisfactionCodeRelations, mem_definableGraph_iff]

/-- The canonical seven-relation code, with no function symbols. -/
noncomputable def finiteSatisfactionCode (L M T : V) : V :=
  structureCode (satisfactionCodeDomain L M) ∅ (satisfactionCodeRelations L M T)

instance finiteSatisfactionCode_definable : ℒₛₑₜ-function₃[V] finiteSatisfactionCode := by
  unfold finiteSatisfactionCode
  definability

@[simp] theorem finiteSatisfactionCode_domain (L M T : V) :
    structureDomain (finiteSatisfactionCode L M T) = satisfactionCodeDomain L M := by
  simp [finiteSatisfactionCode]

theorem finiteSatisfactionCode_valid (L M T : V) :
    IsStructureCode satisfactionCodeLanguage (finiteSatisfactionCode L M T) := by
  simp only [IsStructureCode, finiteSatisfactionCode, satisfactionCodeLanguage,
    structureDomain_code, structureFunctions_code, structureRelations_code,
    functionSymbols_code, relationSymbols_code, functionArities_code, relationArities_code]
  refine ⟨satisfactionCodeLanguage_valid, True.intro, satisfactionCodeDomain_nonempty L M,
    inferInstance, by simp, definableGraph_isFunction _ _ _, domain_definableGraph _ _ _, ?_, ?_⟩
  · intro f hf
    exact False.elim (not_mem_empty hf)
  · intro r hr
    rw [satisfactionCodeRelations, satisfactionCodeArities,
      value_definableGraph _ _ _ hr, value_definableGraph _ _ _ hr]
    exact fun s hs ↦ ((mem_satisfactionCodeRelation_iff L M T r s).mp hs).1

theorem finiteSatisfactionCode_relation {L M T r s : V} (hr : r ∈ (7 : V)) :
    s ∈ (structureRelations (finiteSatisfactionCode L M T)) ‘ r ↔
      s ∈ satisfactionCodeDomain L M ^ satisfactionCodeArity r ∧
        SatisfactionCodeHolds L M T r s := by
  simp only [finiteSatisfactionCode, structureRelations_code, satisfactionCodeRelations]
  rw [value_definableGraph _ _ _ hr]
  exact mem_satisfactionCodeRelation_iff L M T r s

private theorem satisfactionNumeral_eq (m n : ℕ) :
    (SetTheory.ofNat m : V) = SetTheory.ofNat n ↔ m = n := natCast_eq_iff m n

private theorem satisfactionNumeral_mem (m n : ℕ) :
    (SetTheory.ofNat m : V) ∈ (SetTheory.ofNat n : V) ↔ m < n := natCast_mem_iff m n

theorem satisfactionCodeArity_cast (r : ℕ) :
    satisfactionCodeArity (r : V) = (if r < 3 then (1 : V) else if r = 5 then 3 else 2) := by
  change satisfactionCodeArity (SetTheory.ofNat r) = _
  simp only [satisfactionCodeArity, OfNat.ofNat, satisfactionNumeral_mem, satisfactionNumeral_eq]

theorem element_mem_satisfactionCodeDomain_iff (L M a : V) :
    (⟨1, a⟩ₖ : V) ∈ satisfactionCodeDomain L M ↔ a ∈ structureDomain M := by
  simp [satisfactionCodeDomain, kpair_mem_iff, OfNat.ofNat, satisfactionNumeral_eq]

theorem label_mem_satisfactionCodeDomain_iff (L M b : V) :
    (⟨0, b⟩ₖ : V) ∈ satisfactionCodeDomain L M ↔ b ∈ satisfactionLabels L := by
  simp [satisfactionCodeDomain, kpair_mem_iff, OfNat.ofNat, satisfactionNumeral_eq]

theorem assignment_mem_satisfactionCodeDomain_iff (L M t : V) :
    (⟨2, t⟩ₖ : V) ∈ satisfactionCodeDomain L M ↔ t ∈ finiteSequences (structureDomain M) := by
  simp [satisfactionCodeDomain, kpair_mem_iff, OfNat.ofNat, satisfactionNumeral_eq]

theorem domain_eq_of_finiteSatisfactionCode_eq {L M N T S : V}
    (h : finiteSatisfactionCode L M T = finiteSatisfactionCode L N S) :
    structureDomain M = structureDomain N := by
  have hd := congrArg structureDomain h
  simp only [finiteSatisfactionCode_domain] at hd
  apply mem_ext
  intro a
  rw [← element_mem_satisfactionCodeDomain_iff L M a,
    ← element_mem_satisfactionCodeDomain_iff L N a, hd]

theorem satisfactionCodeHolds_labels (L M T s : V) :
    SatisfactionCodeHolds L M T 0 s ↔ s ‘ (0 : V) ∈ ({0} : V) ×ˢ satisfactionLabels L := by
  simp [SatisfactionCodeHolds, OfNat.ofNat, satisfactionNumeral_eq]

theorem satisfactionCodeHolds_elements (L M T s : V) :
    SatisfactionCodeHolds L M T 1 s ↔ s ‘ (0 : V) ∈ ({1} : V) ×ˢ structureDomain M := by
  simp [SatisfactionCodeHolds, OfNat.ofNat, satisfactionNumeral_eq]

theorem satisfactionCodeHolds_assignments (L M T s : V) :
    SatisfactionCodeHolds L M T 2 s ↔
      s ‘ (0 : V) ∈ ({2} : V) ×ˢ finiteSequences (structureDomain M) := by
  simp [SatisfactionCodeHolds, OfNat.ofNat, satisfactionNumeral_eq]

theorem satisfactionCodeHolds_labelRelation (L M T s : V) :
    SatisfactionCodeHolds L M T 3 s ↔
      ∃ b ∈ satisfactionLabels L, ∃ c ∈ satisfactionLabels L,
        s ‘ (0 : V) = ⟨0, b⟩ₖ ∧ s ‘ (1 : V) = ⟨0, c⟩ₖ ∧ ⟨b, c⟩ₖ ∈ T := by
  simp [SatisfactionCodeHolds, OfNat.ofNat, satisfactionNumeral_eq]

theorem satisfactionCodeHolds_length (L M T s : V) :
    SatisfactionCodeHolds L M T 4 s ↔
      ∃ t ∈ finiteSequences (structureDomain M), ∃ n ∈ (ω : V),
        s ‘ (0 : V) = ⟨2, t⟩ₖ ∧ s ‘ (1 : V) = ⟨0, ⟨0, n⟩ₖ⟩ₖ ∧ domain t = n := by
  simp [SatisfactionCodeHolds, OfNat.ofNat, satisfactionNumeral_eq]

theorem satisfactionCodeHolds_evaluation (L M T s : V) :
    SatisfactionCodeHolds L M T 5 s ↔
      ∃ t ∈ finiteSequences (structureDomain M), ∃ i ∈ domain t,
        ∃ a ∈ structureDomain M, s ‘ (0 : V) = ⟨2, t⟩ₖ ∧
          s ‘ (1 : V) = ⟨0, ⟨0, i⟩ₖ⟩ₖ ∧ s ‘ (2 : V) = ⟨1, a⟩ₖ ∧ t ‘ i = a := by
  simp [SatisfactionCodeHolds, OfNat.ofNat, satisfactionNumeral_eq]

theorem satisfactionCodeHolds_satisfaction (L M T s : V) :
    SatisfactionCodeHolds L M T 6 s ↔
      ∃ n ∈ (ω : V), ∃ φ ∈ formulaSet L ∅ n, ∃ t ∈ structureDomain M ^ n,
        s ‘ (0 : V) = ⟨0, ⟨1, ⟨n, φ⟩ₖ⟩ₖ⟩ₖ ∧ s ‘ (1 : V) = ⟨2, t⟩ₖ ∧
          Satisfies L ∅ M ∅ n φ t := by
  simp [SatisfactionCodeHolds, OfNat.ofNat, satisfactionNumeral_eq]

theorem finiteSatisfactionCode_labelRelation {L M T b c : V}
    (hb : b ∈ satisfactionLabels L) (hc : c ∈ satisfactionLabels L) :
    standardTuple ![⟨0, b⟩ₖ, ⟨0, c⟩ₖ] ∈
      (structureRelations (finiteSatisfactionCode L M T)) ‘ (3 : V) ↔ ⟨b, c⟩ₖ ∈ T := by
  have har : satisfactionCodeArity (3 : V) = (2 : V) := by
    simp [satisfactionCodeArity, OfNat.ofNat, satisfactionNumeral_eq]
  have ha : standardTuple ![⟨0, b⟩ₖ, ⟨0, c⟩ₖ] ∈
      satisfactionCodeDomain L M ^ satisfactionCodeArity (3 : V) := by
    rw [har]
    apply standardTuple_mem_function
    simp only [Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.forall_fin_zero, and_true]
    exact ⟨label_mem_satisfactionCodeDomain hb, label_mem_satisfactionCodeDomain hc⟩
  have h3 : (3 : V) ∈ (7 : V) := natCast_mem_of_lt (show 3 < 7 by decide)
  rw [finiteSatisfactionCode_relation h3, and_iff_right ha, satisfactionCodeHolds_labelRelation]
  have hv := standardTuple_equality_values (⟨0, b⟩ₖ : V) (⟨0, c⟩ₖ : V)
  rw [hv.1, hv.2]
  constructor
  · rintro ⟨x, hx, y, hy, hb', hc', hT⟩
    have hbx := (kpair_iff.mp hb').2
    have hcy := (kpair_iff.mp hc').2
    rwa [← hbx, ← hcy] at hT
  · intro hT
    exact ⟨b, hb, c, hc, rfl, rfl, hT⟩

theorem finiteSatisfactionCode_length {L M T t n : V}
    (ht : t ∈ finiteSequences (structureDomain M)) (hn : n ∈ (ω : V)) :
    standardTuple ![⟨2, t⟩ₖ, ⟨0, ⟨0, n⟩ₖ⟩ₖ] ∈
      (structureRelations (finiteSatisfactionCode L M T)) ‘ (4 : V) ↔ domain t = n := by
  have har : satisfactionCodeArity (4 : V) = (2 : V) := by
    simp [satisfactionCodeArity, OfNat.ofNat, satisfactionNumeral_mem, satisfactionNumeral_eq]
  have ha : standardTuple ![⟨2, t⟩ₖ, ⟨0, ⟨0, n⟩ₖ⟩ₖ] ∈
      satisfactionCodeDomain L M ^ satisfactionCodeArity (4 : V) := by
    rw [har]
    apply standardTuple_mem_function
    simp only [Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.forall_fin_zero, and_true]
    exact ⟨assignment_mem_satisfactionCodeDomain ht,
      label_mem_satisfactionCodeDomain (natural_mem_satisfactionLabels hn)⟩
  have h4 : (4 : V) ∈ (7 : V) := natCast_mem_of_lt (show 4 < 7 by decide)
  rw [finiteSatisfactionCode_relation h4, and_iff_right ha, satisfactionCodeHolds_length]
  have hv := standardTuple_equality_values (⟨2, t⟩ₖ : V) (⟨0, ⟨0, n⟩ₖ⟩ₖ : V)
  rw [hv.1, hv.2]
  constructor
  · rintro ⟨u, hu, m, hm, ht', hn', hd⟩
    have htu := (kpair_iff.mp ht').2
    have hnm := (kpair_iff.mp (kpair_iff.mp hn').2).2
    rwa [← htu, ← hnm] at hd
  · intro hd
    exact ⟨t, ht, n, hn, rfl, rfl, hd⟩

theorem finiteSatisfactionCode_evaluation {L M T t i a : V}
    (ht : t ∈ finiteSequences (structureDomain M)) (hi : i ∈ domain t)
    (ha : a ∈ structureDomain M) :
    standardTuple ![⟨2, t⟩ₖ, ⟨0, ⟨0, i⟩ₖ⟩ₖ, ⟨1, a⟩ₖ] ∈
      (structureRelations (finiteSatisfactionCode L M T)) ‘ (5 : V) ↔ t ‘ i = a := by
  have hn := ((mem_finiteSequences_iff_domain _ _).mp ht).1
  have hiω : i ∈ (ω : V) := IsTransitive.transitive _ hn i hi
  have har : satisfactionCodeArity (5 : V) = (3 : V) := by
    simp [satisfactionCodeArity, OfNat.ofNat, satisfactionNumeral_mem]
  have hb : standardTuple ![⟨2, t⟩ₖ, ⟨0, ⟨0, i⟩ₖ⟩ₖ, ⟨1, a⟩ₖ] ∈
      satisfactionCodeDomain L M ^ satisfactionCodeArity (5 : V) := by
    rw [har]
    apply standardTuple_mem_function
    simp only [Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.forall_fin_zero, and_true]
    exact ⟨assignment_mem_satisfactionCodeDomain ht,
      label_mem_satisfactionCodeDomain (natural_mem_satisfactionLabels hiω),
      element_mem_satisfactionCodeDomain ha⟩
  have h5 : (5 : V) ∈ (7 : V) := natCast_mem_of_lt (show 5 < 7 by decide)
  rw [finiteSatisfactionCode_relation h5, and_iff_right hb, satisfactionCodeHolds_evaluation]
  have h0 : (standardTuple ![⟨2, t⟩ₖ, ⟨0, ⟨0, i⟩ₖ⟩ₖ, ⟨1, a⟩ₖ]) ‘ (0 : V) = ⟨2, t⟩ₖ :=
    value_standardTuple _ (0 : Fin 3)
  have h1 : (standardTuple ![⟨2, t⟩ₖ, ⟨0, ⟨0, i⟩ₖ⟩ₖ, ⟨1, a⟩ₖ]) ‘ (1 : V) = ⟨0, ⟨0, i⟩ₖ⟩ₖ :=
    value_standardTuple _ (1 : Fin 3)
  have h2 : (standardTuple ![⟨2, t⟩ₖ, ⟨0, ⟨0, i⟩ₖ⟩ₖ, ⟨1, a⟩ₖ]) ‘ (2 : V) = ⟨1, a⟩ₖ :=
    value_standardTuple _ (2 : Fin 3)
  rw [h0, h1, h2]
  constructor
  · rintro ⟨u, hu, j, hj, b, hb', ht', hi', ha', hv⟩
    have htu := (kpair_iff.mp ht').2
    have hij := (kpair_iff.mp (kpair_iff.mp hi').2).2
    have hab := (kpair_iff.mp ha').2
    rwa [← htu, ← hij, ← hab] at hv
  · intro hv
    exact ⟨t, ht, i, hi, a, ha, rfl, rfl, rfl, hv⟩

/-- The satisfaction relation of the finite code reads the original internal truth predicate. -/
theorem finiteSatisfactionCode_satisfaction {L M T n φ t : V}
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet L ∅ n) (ht : t ∈ structureDomain M ^ n) :
    standardTuple ![⟨0, ⟨1, ⟨n, φ⟩ₖ⟩ₖ⟩ₖ, ⟨2, t⟩ₖ] ∈
      (structureRelations (finiteSatisfactionCode L M T)) ‘ (6 : V) ↔
        Satisfies L ∅ M ∅ n φ t := by
  have ha : standardTuple ![⟨0, ⟨1, ⟨n, φ⟩ₖ⟩ₖ⟩ₖ, ⟨2, t⟩ₖ] ∈
      satisfactionCodeDomain L M ^ satisfactionCodeArity (6 : V) := by
    have har : satisfactionCodeArity (6 : V) = (2 : V) := by
      simp [satisfactionCodeArity, OfNat.ofNat, satisfactionNumeral_mem, satisfactionNumeral_eq]
    rw [har]
    apply standardTuple_mem_function
    simp only [Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.forall_fin_zero, and_true]
    exact ⟨label_mem_satisfactionCodeDomain (formula_mem_satisfactionLabels hφ),
      assignment_mem_satisfactionCodeDomain ((mem_finiteSequences_iff _ _).mpr ⟨n, hn, ht⟩)⟩
  have h6 : (6 : V) ∈ (7 : V) := natCast_mem_of_lt (show 6 < 7 by decide)
  rw [finiteSatisfactionCode_relation h6,
    and_iff_right ha, satisfactionCodeHolds_satisfaction]
  have hv := standardTuple_equality_values (⟨0, ⟨1, ⟨n, φ⟩ₖ⟩ₖ⟩ₖ : V) (⟨2, t⟩ₖ : V)
  rw [hv.1, hv.2]
  constructor
  · rintro ⟨m, hm, ψ, hψ, u, hu, he, ht', hs⟩
    obtain ⟨rfl, rfl⟩ := (kpair_iff.mp (kpair_iff.mp (kpair_iff.mp he).2).2)
    have heu := (kpair_iff.mp ht').2
    rwa [← heu] at hs
  · intro hs
    exact ⟨n, hn, φ, hφ, t, ht, rfl, rfl, hs⟩

end ZFVP
