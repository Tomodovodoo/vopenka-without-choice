import ZFVP.ModelTheory.SchmerlCodedClassExpansion
import ZFVP.ModelTheory.SchmerlInfinitaryExpansion

/-! Actual finite coding for the uniform class and function-tree expansion. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def deadEndRelationArity (r : V) : V := by
  classical
  exact if r = 5 then 3 else classRelationArity r

instance deadEndRelationArity_definable : ℒₛₑₜ-function₁[V] deadEndRelationArity := by
  have h : ℒₛₑₜ-relation[V] (fun a r ↦ (r = 5 ∧ a = 3) ∨
      (r ≠ 5 ∧ a = classRelationArity r)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = deadEndRelationArity (v 1) ↔ _
  unfold deadEndRelationArity
  split <;> simp_all

noncomputable def deadEndLanguageCode : V :=
  languageCode ∅ (6 : V) (constantGraph ∅ ∅)
    (definableGraph (6 : V) deadEndRelationArity (by definability))

theorem deadEndLanguageCode_valid : IsLanguageCode (deadEndLanguageCode : V) := by
  rw [deadEndLanguageCode, isLanguageCode_iff]
  refine ⟨constantGraph_mem_function ∅ ω ∅ (by simp), ?_⟩
  apply mem_function_of_mem_function_of_subset (definableGraph_mem_function _ _ _)
  intro a ha
  obtain ⟨r, _, rfl⟩ := (repl_spec (by definability)).mp ha
  unfold deadEndRelationArity classRelationArity
  split_ifs <;> first | exact ofNat_mem_ω 3 | exact ofNat_mem_ω 1 | exact ofNat_mem_ω 2

def deadEndFunctionSymbol {k : ℕ} (f : deadEndLanguage.Func k) : V := by
  cases f with
  | inl f => exact classFunctionSymbol f
  | inr f => exact Empty.elim f

noncomputable def deadEndRelationSymbol {k : ℕ} (r : deadEndLanguage.Rel k) : V :=
  match r with
  | .inl r => classRelationSymbol r
  | .inr .selected => 4
  | .inr .color => 5

theorem deadEndFunctionSymbol_valid {k : ℕ} (f : deadEndLanguage.Func k) :
    deadEndFunctionSymbol (V := V) f ∈ functionSymbols (deadEndLanguageCode : V) ∧
      (functionArities (deadEndLanguageCode : V)) ‘ (deadEndFunctionSymbol (V := V) f) = (k : V) := by
  cases f with
  | inl f => cases f with
    | inl f => exact Empty.elim f
    | inr f => exact Empty.elim f
  | inr f => exact Empty.elim f

theorem deadEndRelationSymbol_valid {k : ℕ} (r : deadEndLanguage.Rel k) :
    deadEndRelationSymbol (V := V) r ∈ relationSymbols (deadEndLanguageCode : V) ∧
      (relationArities (deadEndLanguageCode : V)) ‘ (deadEndRelationSymbol (V := V) r) = (k : V) := by
  have h0 : (0 : V) ∈ (6 : V) := natCast_mem_of_lt (by decide : 0 < 6)
  have h1 : (1 : V) ∈ (6 : V) := natCast_mem_of_lt (by decide : 1 < 6)
  have h2 : (2 : V) ∈ (6 : V) := natCast_mem_of_lt (by decide : 2 < 6)
  have h3 : (3 : V) ∈ (6 : V) := natCast_mem_of_lt (by decide : 3 < 6)
  have h4 : (4 : V) ∈ (6 : V) := natCast_mem_of_lt (by decide : 4 < 6)
  have h5 : (5 : V) ∈ (6 : V) := natCast_mem_of_lt (by decide : 5 < 6)
  have h02 : (0 : V) ≠ 2 := natCast_injective.ne (by decide)
  have h12 : (1 : V) ≠ 2 := natCast_injective.ne (by decide)
  have h32 : (3 : V) ≠ 2 := natCast_injective.ne (by decide)
  have h42 : (4 : V) ≠ 2 := natCast_injective.ne (by decide)
  have h05 : (0 : V) ≠ 5 := natCast_injective.ne (by decide)
  have h15 : (1 : V) ≠ 5 := natCast_injective.ne (by decide)
  have h25 : (2 : V) ≠ 5 := natCast_injective.ne (by decide)
  have h35 : (3 : V) ≠ 5 := natCast_injective.ne (by decide)
  have h45 : (4 : V) ≠ 5 := natCast_injective.ne (by decide)
  cases r with
  | inl r => cases r with
    | inl r => cases r <;>
      simp [deadEndRelationSymbol, classRelationSymbol, membershipSymbol, deadEndLanguageCode,
        value_definableGraph, deadEndRelationArity, classRelationArity, h0, h1, h02, h12, h05, h15]
    | inr r => cases r <;>
      simp [deadEndRelationSymbol, classRelationSymbol, deadEndLanguageCode,
        value_definableGraph, deadEndRelationArity, classRelationArity, h2, h3, h32, h25, h35]
  | inr r => cases r <;>
    simp [deadEndRelationSymbol, deadEndLanguageCode,
      value_definableGraph, deadEndRelationArity, classRelationArity, h4, h5, h42, h45]

noncomputable def functionColorTuples (D G : V) : V :=
  {t ∈ D ^ (3 : V) ; t ‘ (1 : V) = G ‘ ⟨t ‘ (0 : V), t ‘ (2 : V)⟩ₖ}

instance functionColorTuples_definable : ℒₛₑₜ-function₂[V] functionColorTuples := by
  have h : ℒₛₑₜ-relation₃[V] (fun R D G ↦ ∀ t, t ∈ R ↔
      t ∈ D ^ (3 : V) ∧ t ‘ (1 : V) = G ‘ ⟨t ‘ (0 : V), t ‘ (2 : V)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [functionColorTuples, mem_sep_iff]
  rfl

noncomputable def deadEndRelationInterpretation (D E A g S G r : V) : V := by
  classical
  exact if r = 4 then binaryTupleRelation D S else if r = 5 then functionColorTuples D G
    else classRelationInterpretation D E A g r

instance deadEndRelationInterpretation_definable (D E A g S G : V) :
    ℒₛₑₜ-function₁[V] (deadEndRelationInterpretation D E A g S G) := by
  have h : ℒₛₑₜ-relation[V] (fun X r ↦
      (r = 4 ∧ X = binaryTupleRelation D S) ∨
      (r ≠ 4 ∧ r = 5 ∧ X = functionColorTuples D G) ∨
      (r ≠ 4 ∧ r ≠ 5 ∧ X = classRelationInterpretation D E A g r)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = deadEndRelationInterpretation D E A g S G (v 1) ↔ _
  unfold deadEndRelationInterpretation
  split_ifs <;> simp_all

noncomputable def codedDeadEndExpansion (D E A g S G : V) : V :=
  structureCode D (constantGraph ∅ ∅)
    (definableGraph (6 : V) (deadEndRelationInterpretation D E A g S G) (by definability))

@[simp] theorem codedDeadEndExpansion_domain (D E A g S G : V) :
    structureDomain (codedDeadEndExpansion D E A g S G) = D := by simp [codedDeadEndExpansion]

theorem codedDeadEndExpansion_valid {D : V} (hD : IsNonempty D) (E A g S G : V) :
    IsStructureCode deadEndLanguageCode (codedDeadEndExpansion D E A g S G) := by
  simp only [IsStructureCode, codedDeadEndExpansion, deadEndLanguageCode,
    structureDomain_code, structureFunctions_code, structureRelations_code,
    functionSymbols_code, relationSymbols_code, functionArities_code, relationArities_code]
  refine ⟨deadEndLanguageCode_valid, True.intro, hD, inferInstance, domain_constantGraph _ _,
    inferInstance, domain_definableGraph _ _ _, ?_, ?_⟩
  · intro f hf
    exact False.elim (not_mem_empty hf)
  · intro r hr
    rw [value_definableGraph _ _ _ hr, value_definableGraph _ _ _ hr]
    classical
    have h02 : (0 : V) ≠ 2 := natCast_injective.ne (by decide)
    have h12 : (1 : V) ≠ 2 := natCast_injective.ne (by decide)
    have h42 : (4 : V) ≠ 2 := natCast_injective.ne (by decide)
    have h45 : (4 : V) ≠ 5 := natCast_injective.ne (by decide)
    by_cases h4 : r = 4
    · subst r
      simpa [deadEndRelationInterpretation, deadEndRelationArity, classRelationArity, h42, h45]
        using binaryTupleRelation_subset D S
    by_cases h5 : r = 5
    · subst r
      simp only [deadEndRelationInterpretation, h4, ite_false, ite_true, deadEndRelationArity]
      exact fun t ht ↦ (mem_sep_iff.mp ht).1
    simp only [deadEndRelationInterpretation, h4, h5, ite_false, deadEndRelationArity]
    by_cases h0 : r = 0
    · subst r
      simpa [classRelationInterpretation, classRelationArity, h02] using equalityRelation_subset D
    by_cases h1 : r = 1
    · subst r
      simpa [classRelationInterpretation, classRelationArity, h12] using binaryTupleRelation_subset D E
    by_cases h2 : r = 2
    · subst r
      simp only [classRelationInterpretation, h0, h1, ite_false, ite_true, classRelationArity]
      exact fun t ht ↦ (mem_sep_iff.mp ht).1
    · simp only [classRelationInterpretation, h0, h1, h2, ite_false, classRelationArity]
      exact fun t ht ↦ (mem_sep_iff.mp ht).1

theorem codedDeadEndExpansion_relation {k : ℕ} (D E A g S G : V) (r : deadEndLanguage.Rel k) :
    (structureRelations (codedDeadEndExpansion D E A g S G)) ‘ (deadEndRelationSymbol r) =
      deadEndRelationInterpretation D E A g S G (deadEndRelationSymbol r) := by
  rw [codedDeadEndExpansion, structureRelations_code]
  apply value_definableGraph
  simpa only [deadEndLanguageCode, relationSymbols_code] using (deadEndRelationSymbol_valid (V := V) r).1

def codedDeadEndExpansionEquiv (D E A g S G : V) :
    CodedDomain (codedDeadEndExpansion D E A g S G) ≃ BinaryRelationDomain D E where
  toFun x := ⟨x.val, by simpa using x.property⟩
  invFun x := ⟨x.val, by simpa using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def functionColorFunction {D E G : V} (hG : G ∈ D ^ (D ×ˢ D))
    (s x : BinaryRelationDomain D E) : BinaryRelationDomain D E :=
  ⟨G ‘ ⟨s.val, x.val⟩ₖ, function_value_mem hG (by simp [s.property, x.property])⟩

theorem codedDeadEndExpansion_eval {D E A g S G : V} (hD : IsNonempty D)
    (hg : g ∈ D ^ D) (hG : G ∈ D ^ (D ×ˢ D))
    {ξ : Type*} {n : ℕ} (φ : Semiformula deadEndLanguage ξ n)
    (a : ξ → CodedDomain (codedDeadEndExpansion D E A g S G))
    (b : Fin n → CodedDomain (codedDeadEndExpansion D E A g S G)) :
    φ.EvalAux (codedFoundationStructure (codedDeadEndExpansion_valid hD E A g S G)
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol
      (fun _ f ↦ deadEndFunctionSymbol_valid f)) a b ↔
    φ.EvalAux (deadEndExpansion (fun x : BinaryRelationDomain D E ↦ x.val ∈ A)
      (classColorFunction hg) (fun s d ↦ ⟨s.val, d.val⟩ₖ ∈ S) (functionColorFunction hG))
      (fun x ↦ codedDeadEndExpansionEquiv D E A g S G (a x))
      (fun i ↦ codedDeadEndExpansionEquiv D E A g S G (b i)) := by
  let : Structure deadEndLanguage (CodedDomain (codedDeadEndExpansion D E A g S G)) :=
    codedFoundationStructure (codedDeadEndExpansion_valid hD E A g S G)
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol
      (fun _ f ↦ deadEndFunctionSymbol_valid f)
  let : Structure deadEndLanguage (BinaryRelationDomain D E) :=
    deadEndExpansion (fun x : BinaryRelationDomain D E ↦ x.val ∈ A)
      (classColorFunction hg) (fun s d ↦ ⟨s.val, d.val⟩ₖ ∈ S) (functionColorFunction hG)
  apply Structure.ElementaryEquiv.eval_iff_of_equiv (codedDeadEndExpansionEquiv D E A g S G)
    (fun _ ↦ rfl) (fun _ ↦ rfl)
  · intro k r v w hvw
    have hv : ∀ i, (v i).val = (w i).val := fun i ↦ congrArg Subtype.val (hvw i)
    have hvm : ∀ i, (v i).val ∈ D := fun i ↦ by simpa using (v i).property
    change standardTuple (fun i ↦ (v i).val) ∈
      (structureRelations (codedDeadEndExpansion D E A g S G)) ‘ (deadEndRelationSymbol r) ↔ _
    rw [codedDeadEndExpansion_relation]
    cases r with
    | inl r =>
      have hr4 : classRelationSymbol (V := V) r ≠ 4 := by
        cases r with
        | inl r => cases r <;> exact natCast_injective.ne (by decide)
        | inr r => cases r <;> exact natCast_injective.ne (by decide)
      have hr5 : classRelationSymbol (V := V) r ≠ 5 := by
        cases r with
        | inl r => cases r <;> exact natCast_injective.ne (by decide)
        | inr r => cases r <;> exact natCast_injective.ne (by decide)
      simp only [deadEndRelationSymbol, deadEndRelationInterpretation, hr4, hr5, ite_false]
      let v' : Fin k → CodedDomain (codedClassExpansion D E A g) :=
        fun i ↦ ⟨(v i).val, by simpa using hvm i⟩
      have he := codedClassExpansion_eval hD hg
        (Semiformula.rel r (fun i ↦ Semiterm.bvar i)) (Empty.elim : Empty → _) v'
      have hw : (fun i ↦ codedClassExpansionEquiv D E A g (v' i)) = w := by
        funext i
        exact hvw i
      change standardTuple (fun i ↦ (v i).val) ∈
        (structureRelations (codedClassExpansion D E A g)) ‘ (classRelationSymbol r) ↔
        (classExpansion (fun x : BinaryRelationDomain D E ↦ x.val ∈ A)
          (classColorFunction hg)).rel r (fun i ↦ codedClassExpansionEquiv D E A g (v' i)) at he
      rw [codedClassExpansion_relation, hw] at he
      exact he
    | inr r =>
      cases r
      · simp only [deadEndRelationSymbol, deadEndRelationInterpretation, ite_true]
        rw [standardTuple_mem_binaryTupleRelation _ hvm, hv 0, hv 1]
        rfl
      · have h54 : (5 : V) ≠ 4 := natCast_injective.ne (by decide)
        simp only [deadEndRelationSymbol, deadEndRelationInterpretation, h54,
          ite_false, ite_true, functionColorTuples, mem_sep_iff]
        change (standardTuple (fun i ↦ (v i).val) ∈ D ^ (3 : V) ∧
          (standardTuple (fun i ↦ (v i).val)) ‘ (1 : V) =
            G ‘ ⟨(standardTuple (fun i ↦ (v i).val)) ‘ (0 : V),
              (standardTuple (fun i ↦ (v i).val)) ‘ (2 : V)⟩ₖ) ↔
          w 1 = functionColorFunction hG (w 0) (w 2)
        have ht : standardTuple (fun i ↦ (v i).val) ∈ D ^ (3 : V) := by
          simpa using standardTuple_mem_function _ hvm
        rw [and_iff_right ht]
        change (standardTuple (fun i ↦ (v i).val)) ‘ (((1 : Fin 3).val : ℕ) : V) =
          G ‘ ⟨(standardTuple (fun i ↦ (v i).val)) ‘ (((0 : Fin 3).val : ℕ) : V),
            (standardTuple (fun i ↦ (v i).val)) ‘ (((2 : Fin 3).val : ℕ) : V)⟩ₖ ↔ _
        rw [value_standardTuple, value_standardTuple, value_standardTuple, hv 0, hv 1, hv 2]
        exact ⟨fun he ↦ Subtype.ext he, fun he ↦ congrArg Subtype.val he⟩
  · intro k f
    cases f with
    | inl f => cases f with
      | inl f => exact Empty.elim f
      | inr f => exact Empty.elim f
    | inr f => exact Empty.elim f

end ZFVP.Schmerl
