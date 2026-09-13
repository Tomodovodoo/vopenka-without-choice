import ZFVP.ModelTheory.SchmerlCodedInfinitarySemantics
import ZFVP.ModelTheory.SchmerlInfinitaryClassSentence
import ZFVP.ModelTheory.BinaryRelationStructure

/-! The fixed class language has an actual finite language code. Its expansion
retains the supplied binary relation and interprets selected ranks and colors
by actual sets in the ambient model. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def classRelationArity (r : V) : V := by
  classical
  exact if r = 2 then 1 else 2

instance classRelationArity_definable : ℒₛₑₜ-function₁[V] classRelationArity := by
  have h : ℒₛₑₜ-relation[V] (fun a r ↦ (r = 2 ∧ a = 1) ∨ (r ≠ 2 ∧ a = 2)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = classRelationArity (v 1) ↔ _
  unfold classRelationArity
  split <;> simp_all

noncomputable def classLanguageCode : V :=
  languageCode ∅ (4 : V) (constantGraph ∅ ∅)
    (definableGraph (4 : V) classRelationArity (by definability))

theorem classLanguageCode_valid : IsLanguageCode (classLanguageCode : V) := by
  rw [classLanguageCode, isLanguageCode_iff]
  refine ⟨?_, ?_⟩
  · exact constantGraph_mem_function ∅ ω ∅ (by simp)
  · apply mem_function_of_mem_function_of_subset (definableGraph_mem_function _ _ _)
    intro a ha
    obtain ⟨r, _, rfl⟩ := (repl_spec (by definability)).mp ha
    unfold classRelationArity
    split <;> simp

def classFunctionSymbol {k : ℕ} (f : classLanguage.Func k) : V := by
  cases f with
  | inl f => exact Empty.elim f
  | inr f => exact Empty.elim f

noncomputable def classRelationSymbol {k : ℕ} (r : classLanguage.Rel k) : V :=
  match r with
  | Sum.inl r => membershipSymbol r
  | Sum.inr ClassExtraRelation.selected => 2
  | Sum.inr ClassExtraRelation.color => 3

theorem classFunctionSymbol_valid {k : ℕ} (f : classLanguage.Func k) :
    classFunctionSymbol (V := V) f ∈ functionSymbols (classLanguageCode : V) ∧
      (functionArities (classLanguageCode : V)) ‘ (classFunctionSymbol (V := V) f) = (k : V) := by
  cases f with
  | inl f => exact Empty.elim f
  | inr f => exact Empty.elim f

theorem classRelationSymbol_valid {k : ℕ} (r : classLanguage.Rel k) :
    classRelationSymbol (V := V) r ∈ relationSymbols (classLanguageCode : V) ∧
      (relationArities (classLanguageCode : V)) ‘ (classRelationSymbol (V := V) r) = (k : V) := by
  have h02 : (0 : V) ≠ 2 := natCast_injective.ne (by decide)
  have h12 : (1 : V) ≠ 2 := natCast_injective.ne (by decide)
  have h32 : (3 : V) ≠ 2 := natCast_injective.ne (by decide)
  have h0 : (0 : V) ∈ (4 : V) := natCast_mem_of_lt (by decide : 0 < 4)
  have h1 : (1 : V) ∈ (4 : V) := natCast_mem_of_lt (by decide : 1 < 4)
  have h2 : (2 : V) ∈ (4 : V) := natCast_mem_of_lt (by decide : 2 < 4)
  have h3 : (3 : V) ∈ (4 : V) := natCast_mem_of_lt (by decide : 3 < 4)
  cases r with
  | inl r => cases r <;> simp [classRelationSymbol, membershipSymbol, classLanguageCode, value_definableGraph,
      classRelationArity, h02, h12, h0, h1]
  | inr r => cases r <;> simp [classRelationSymbol, classLanguageCode, value_definableGraph,
      classRelationArity, h32, h2, h3]

noncomputable def classSelectedTuples (D A : V) : V :=
  {s ∈ D ^ (1 : V) ; s ‘ (0 : V) ∈ A}

noncomputable def classColorTuples (D g : V) : V :=
  {s ∈ D ^ (2 : V) ; s ‘ (0 : V) = g ‘ (s ‘ (1 : V))}

instance classSelectedTuples_definable : ℒₛₑₜ-function₂[V] classSelectedTuples := by
  have h : ℒₛₑₜ-relation₃[V] (fun R D A ↦ ∀ s, s ∈ R ↔ s ∈ D ^ (1 : V) ∧ s ‘ (0 : V) ∈ A) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [classSelectedTuples, mem_sep_iff]
  rfl

instance classColorTuples_definable : ℒₛₑₜ-function₂[V] classColorTuples := by
  have h : ℒₛₑₜ-relation₃[V] (fun R D g ↦ ∀ s, s ∈ R ↔
      s ∈ D ^ (2 : V) ∧ s ‘ (0 : V) = g ‘ (s ‘ (1 : V))) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [classColorTuples, mem_sep_iff]
  rfl

noncomputable def classRelationInterpretation (D E A g r : V) : V := by
  classical
  exact if r = 0 then equalityRelation D else if r = 1 then binaryTupleRelation D E
    else if r = 2 then classSelectedTuples D A else classColorTuples D g

instance classRelationInterpretation_definable (D E A g : V) :
    ℒₛₑₜ-function₁[V] (classRelationInterpretation D E A g) := by
  have h : ℒₛₑₜ-relation[V] (fun X r ↦
      (r = 0 ∧ X = equalityRelation D) ∨ (r ≠ 0 ∧ r = 1 ∧ X = binaryTupleRelation D E) ∨
      (r ≠ 0 ∧ r ≠ 1 ∧ r = 2 ∧ X = classSelectedTuples D A) ∨
      (r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 2 ∧ X = classColorTuples D g)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = classRelationInterpretation D E A g (v 1) ↔ _
  unfold classRelationInterpretation
  split_ifs <;> simp_all

noncomputable def codedClassExpansion (D E A g : V) : V :=
  structureCode D (constantGraph ∅ ∅)
    (definableGraph (4 : V) (classRelationInterpretation D E A g) (by definability))

@[simp] theorem codedClassExpansion_domain (D E A g : V) :
    structureDomain (codedClassExpansion D E A g) = D := by simp [codedClassExpansion]

theorem codedClassExpansion_valid {D : V} (hD : IsNonempty D) (E A g : V) :
    IsStructureCode classLanguageCode (codedClassExpansion D E A g) := by
  simp only [IsStructureCode, codedClassExpansion, classLanguageCode,
    structureDomain_code, structureFunctions_code, structureRelations_code,
    functionSymbols_code, relationSymbols_code, functionArities_code, relationArities_code]
  refine ⟨classLanguageCode_valid, True.intro, hD, inferInstance, domain_constantGraph _ _,
    inferInstance, domain_definableGraph _ _ _, ?_, ?_⟩
  · intro f hf
    exact False.elim (not_mem_empty hf)
  · intro r hr
    rw [value_definableGraph _ _ _ hr, value_definableGraph _ _ _ hr]
    classical
    have h02 : (0 : V) ≠ 2 := natCast_injective.ne (by decide)
    have h12 : (1 : V) ≠ 2 := natCast_injective.ne (by decide)
    by_cases h0 : r = 0
    · subst r
      simpa [classRelationInterpretation, classRelationArity, h02] using equalityRelation_subset D
    by_cases h1 : r = 1
    · subst r
      simpa [classRelationInterpretation, classRelationArity, h12] using binaryTupleRelation_subset D E
    by_cases h2 : r = 2
    · subst r
      simp only [classRelationInterpretation, Ne.symm h02, Ne.symm h12, ite_false, ite_true, classRelationArity]
      exact fun s hs ↦ (mem_sep_iff.mp hs).1
    · simp only [classRelationInterpretation, h0, h1, h2, ite_false, classRelationArity]
      exact fun s hs ↦ (mem_sep_iff.mp hs).1

theorem codedClassExpansion_relation {k : ℕ} (D E A g : V) (r : classLanguage.Rel k) :
    (structureRelations (codedClassExpansion D E A g)) ‘ (classRelationSymbol r) =
      classRelationInterpretation D E A g (classRelationSymbol r) := by
  rw [codedClassExpansion, structureRelations_code]
  apply value_definableGraph
  simpa only [classLanguageCode, relationSymbols_code] using (classRelationSymbol_valid (V := V) r).1

def codedClassExpansionEquiv (D E A g : V) :
    CodedDomain (codedClassExpansion D E A g) ≃ BinaryRelationDomain D E where
  toFun x := ⟨x.val, by simpa using x.property⟩
  invFun x := ⟨x.val, by simpa using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def classColorFunction {D E g : V} (hg : g ∈ D ^ D)
    (x : BinaryRelationDomain D E) : BinaryRelationDomain D E :=
  ⟨g ‘ x.val, function_value_mem hg x.property⟩

theorem codedClassExpansion_eval {D E A g : V} (hD : IsNonempty D) (hg : g ∈ D ^ D)
    {ξ : Type*} {n : ℕ} (φ : Semiformula classLanguage ξ n)
    (a : ξ → CodedDomain (codedClassExpansion D E A g))
    (b : Fin n → CodedDomain (codedClassExpansion D E A g)) :
    φ.EvalAux (codedFoundationStructure (codedClassExpansion_valid hD E A g)
      (fun {k} ↦ classFunctionSymbol (V := V) (k := k)) classRelationSymbol
      (fun _ f ↦ classFunctionSymbol_valid f)) a b ↔
    φ.EvalAux (classExpansion (fun x : BinaryRelationDomain D E ↦ x.val ∈ A) (classColorFunction hg))
      (fun x ↦ codedClassExpansionEquiv D E A g (a x))
      (fun i ↦ codedClassExpansionEquiv D E A g (b i)) := by
  let : Structure classLanguage (CodedDomain (codedClassExpansion D E A g)) :=
    codedFoundationStructure (codedClassExpansion_valid hD E A g)
      (fun {k} ↦ classFunctionSymbol (V := V) (k := k)) classRelationSymbol
      (fun _ f ↦ classFunctionSymbol_valid f)
  let : Structure classLanguage (BinaryRelationDomain D E) :=
    classExpansion (fun x : BinaryRelationDomain D E ↦ x.val ∈ A) (classColorFunction hg)
  apply Structure.ElementaryEquiv.eval_iff_of_equiv (codedClassExpansionEquiv D E A g)
    (fun _ ↦ rfl) (fun _ ↦ rfl)
  · intro k r v w hvw
    have h20 : (2 : V) ≠ 0 := natCast_injective.ne (by decide)
    have h21 : (2 : V) ≠ 1 := natCast_injective.ne (by decide)
    have h30 : (3 : V) ≠ 0 := natCast_injective.ne (by decide)
    have h31 : (3 : V) ≠ 1 := natCast_injective.ne (by decide)
    have h32 : (3 : V) ≠ 2 := natCast_injective.ne (by decide)
    have hv : ∀ i, (v i).val = (w i).val := fun i ↦ congrArg Subtype.val (hvw i)
    have hvm : ∀ i, (v i).val ∈ D := fun i ↦ by simpa using (v i).property
    change standardTuple (fun i ↦ (v i).val) ∈
      (structureRelations (codedClassExpansion D E A g)) ‘ (classRelationSymbol r) ↔ _
    rw [codedClassExpansion_relation]
    cases r with
    | inl r =>
      cases r
      · simp only [classRelationSymbol, membershipSymbol, classRelationInterpretation, ite_true]
        rw [standardTuple_mem_equalityRelation _ hvm, hv 0, hv 1]
        exact Subtype.val_injective.eq_iff
      · simp only [classRelationSymbol, membershipSymbol, classRelationInterpretation]
        simp only [show (1 : V) ≠ 0 by simp, ite_false, ite_true]
        rw [standardTuple_mem_binaryTupleRelation _ hvm, hv 0, hv 1]
        rfl
    | inr r =>
      cases r
      · simp only [classRelationSymbol, classRelationInterpretation]
        simp only [h20, h21, ite_false, ite_true,
          classSelectedTuples, mem_sep_iff]
        change (standardTuple (fun i ↦ (v i).val) ∈ D ^ (1 : V) ∧
          (standardTuple (fun i ↦ (v i).val)) ‘ (0 : V) ∈ A) ↔ (w 0).val ∈ A
        have ht : standardTuple (fun i ↦ (v i).val) ∈ D ^ (1 : V) := by
          simpa using standardTuple_mem_function _ hvm
        rw [and_iff_right ht]
        change (standardTuple (fun i ↦ (v i).val)) ‘ (((0 : Fin 1).val : ℕ) : V) ∈ A ↔ (w 0).val ∈ A
        rw [value_standardTuple, hv 0]
      · simp only [classRelationSymbol, classRelationInterpretation]
        simp only [h30, h31, h32,
          ite_false, classColorTuples, mem_sep_iff]
        change (standardTuple (fun i ↦ (v i).val) ∈ D ^ (2 : V) ∧
          (standardTuple (fun i ↦ (v i).val)) ‘ (0 : V) =
            g ‘ ((standardTuple (fun i ↦ (v i).val)) ‘ (1 : V))) ↔ w 0 = classColorFunction hg (w 1)
        have ht : standardTuple (fun i ↦ (v i).val) ∈ D ^ (2 : V) := by
          simpa using standardTuple_mem_function _ hvm
        rw [and_iff_right ht]
        change (standardTuple (fun i ↦ (v i).val)) ‘ (((0 : Fin 2).val : ℕ) : V) =
          g ‘ ((standardTuple (fun i ↦ (v i).val)) ‘ (((1 : Fin 2).val : ℕ) : V)) ↔ _
        rw [value_standardTuple, value_standardTuple, hv 0, hv 1]
        constructor
        · intro he
          exact Subtype.ext he
        · intro he
          exact congrArg (fun x : BinaryRelationDomain D E ↦ x.val) he
  · intro k f
    cases f with
    | inl f => exact Empty.elim f
    | inr f => exact Empty.elim f

end ZFVP.Schmerl
