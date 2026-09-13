import ZFVP.ModelTheory.InternalJointRealizationFormula
import ZFVP.ModelTheory.InternalNamedQueryContext
import ZFVP.ModelTheory.FiniteJointQueryFormula

/-! Uniform first-order formulas for extending a finite condition by a unary
query or its negation at a varying old source element. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_jointNamedQueryFormula_of_context (hω : Schmerl.HasStandardOmega V)
    {D R I j k A t χ : V} {N p : ℕ} (hD : IsNonempty D)
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ I) (hki : Injective k)
    (hdis : ∀ i ∈ range j, i ∉ range k)
    (ht : t ∈ (namedUnaryDefinitionQueries : V))
    (hbound : range (Schmerl.definitionTuple t) ⊆ (N : V))
    (hχ : χ ∈ formulaSet membershipLanguageCode ∅ (N : V))
    (heq : ∀ f ∈ D ^ (ω : V),
      ((∀ q ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f q) ↔
        Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D R) ∅ (N : V) χ (f ↾ (N : V))))
    (indices : Fin p → V) (his : ∀ z, indices z ∈ I)
    (hcover : ∀ i ∈ I, k ‘ i ∈ (N : V) → ∃ z, indices z = i) :
    ∃ Φ : SetTheorySemiformula (BinaryRelationDomain D R) (p + 1),
      ∀ (x : BinaryRelationDomain D R) (c : V) (hc : c ∈ D ^ I),
        Semiformula.Eval (M := BinaryRelationDomain D R)
          (x :> fun z ↦ (⟨c ‘ (indices z), function_value_mem hc (his z)⟩ : BinaryRelationDomain D R)) id Φ ↔
        ∃ f, SourceNaming (binaryRelationStructureCode D R) j f ∧
          (∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i) ∧
          (∀ q ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f q) ∧
          NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f
            (namedUnaryQueryInstance t (j ‘ x.val)) := by
  have hn : (N : V) ∈ (ω : V) := by simp
  have hnω : (N : V) ⊆ (ω : V) := IsTransitive.ω.transitive (N : V) hn
  have hM := binaryRelationStructureCode_valid hD R
  have hjM : j ∈ (ω : V) ^ structureDomain (binaryRelationStructureCode D R) := by simpa using hj
  have hχcode : IsMembershipFormulaCode (N : V) χ := (mem_formulaSet_iff _ _ _ _).mp hχ
  obtain ⟨ψ, hψ⟩ := binary_formula_representable_of_standardOmega hω hχcode
  have hθcode : IsMembershipFormulaCode ((N + 1 : ℕ) : V) (namedQueryCodeInContext (N : V) t) := by
    simpa only [num_succ_def, IsMembershipFormulaCode] using
      (mem_formulaSet_iff _ _ _ _).mp (namedQueryCodeInContext_mem ht hn hbound)
  obtain ⟨θ, hθ⟩ := binary_formula_representable_of_standardOmega hω hθcode
  have hθeval (x : BinaryRelationDomain D R) (a : Fin N → BinaryRelationDomain D R) :
      Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D R) ∅ (succ (N : V))
        (namedQueryCodeInContext (N : V) t)
        (assignmentPrepend (N : V) (standardTuple (fun z ↦ (a z).val)) x.val) ↔ θ.Evalb (x :> a) := by
    have htuple : standardTuple (fun z ↦ ((x :> a) z).val) =
        assignmentPrepend (N : V) (standardTuple (fun z ↦ (a z).val)) x.val := by
      simp only [standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ]
    simpa only [num_succ_def, htuple] using hθ D R hD (x :> a)
  refine ⟨finiteJointQueryFormula ψ θ (finiteInternalSourceNames D R j N)
    (finiteInternalUpperSlots k indices N), ?_⟩
  intro x c hc
  let u : Fin p → BinaryRelationDomain D R :=
    fun z ↦ ⟨c ‘ (indices z), function_value_mem hc (his z)⟩
  change Semiformula.Eval (x :> u) id (finiteJointQueryFormula ψ θ
    (finiteInternalSourceNames D R j N) (finiteInternalUpperSlots k indices N)) ↔ _
  rw [eval_finiteJointQueryFormula]
  constructor
  · rintro ⟨a, haψ, haθ, has, hak⟩
    have hb := standardTuple_mem_function (fun z ↦ (a z).val) (fun z ↦ (a z).property)
    have hbs := (finiteInternalSourceNames_constraints hj hji a).mp has
    have hbk := (finiteInternalUpperSlots_constraints indices his hcover hc a).mp hak
    obtain ⟨f, hf, hfj, hfk, hfb⟩ :=
      exists_jointSourceAssignment_extending hD hj hji hk hki hdis hc hnω hb hbs hbk
    have hsource : SourceNaming (binaryRelationStructureCode D R) j f := by
      simpa only [SourceNaming, binaryRelationStructureCode_domain] using And.intro hf hfj
    refine ⟨f, hsource, hfk, (heq f hf).mpr ?_, ?_⟩
    · rw [hfb]
      exact (hψ D R hD a).mpr haψ
    · apply (namedQueryCodeInContext_satisfies hM hjM hsource ht hn hbound
        (by simpa using x.property)).mp
      rw [hfb]
      exact (hθeval x a).mpr haθ
  · rintro ⟨f, hsource, hfk, hAf, hqf⟩
    have hf : f ∈ D ^ (ω : V) := by simpa using hsource.1
    have hfb : f ↾ (N : V) ∈ D ^ (N : V) := function_restrict_mem hf hnω
    have : IsFunction f := IsFunction.of_mem hf
    obtain ⟨a, ha⟩ := exists_binaryStandardTuple (R := R) hfb
    have haχ := (heq f hf).mp hAf
    have haθ := (namedQueryCodeInContext_satisfies hM hjM hsource ht hn hbound
      (by simpa using x.property)).mpr hqf
    rw [ha] at haχ haθ
    refine ⟨a, (hψ D R hD a).mp haχ, (hθeval x a).mp haθ,
      (finiteInternalSourceNames_constraints hj hji a).mpr ?_,
      (finiteInternalUpperSlots_constraints indices his hcover hc a).mpr ?_⟩
    · intro y hy hyn
      rw [← ha, value_restrict (by rw [domain_eq_of_mem_function hf]; exact function_value_mem hj hy) hyn]
      exact hsource.2 y (by simpa using hy)
    · intro i hi hin
      rw [← ha, value_restrict (by rw [domain_eq_of_mem_function hf]; exact function_value_mem hk hi) hin]
      exact hfk i hi

theorem exists_jointNamedQueryFormulas (hω : Schmerl.HasStandardOmega V)
    {D R I j k A t : V} (hD : IsNonempty D)
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ I) (hki : Injective k)
    (hdis : ∀ i ∈ range j, i ∉ range k)
    (hA : IsInternallyFinite A) (hsub : A ⊆ namedFormulaSet membershipLanguageCode (ω : V))
    (ht : t ∈ (namedUnaryDefinitionQueries : V)) :
    ∃ N : ℕ, namedTheorySupport A ⊆ (N : V) ∧ range (Schmerl.definitionTuple t) ⊆ (N : V) ∧
      ∀ (p : ℕ) (indices : Fin p → V) (his : ∀ z, indices z ∈ I),
        (∀ i ∈ I, k ‘ i ∈ (N : V) → ∃ z, indices z = i) →
        ∃ Φpositive Φnegative : SetTheorySemiformula (BinaryRelationDomain D R) (p + 1),
          ∀ (x : BinaryRelationDomain D R) (c : V) (hc : c ∈ D ^ I),
            (Semiformula.Eval (M := BinaryRelationDomain D R)
              (x :> fun z ↦ (⟨c ‘ (indices z), function_value_mem hc (his z)⟩ : BinaryRelationDomain D R))
              id Φpositive ↔
              ∃ f, SourceNaming (binaryRelationStructureCode D R) j f ∧
                (∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i) ∧
                (∀ q ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f q) ∧
                NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f
                  (namedUnaryQueryInstance t (j ‘ x.val))) ∧
            (Semiformula.Eval (M := BinaryRelationDomain D R)
              (x :> fun z ↦ (⟨c ‘ (indices z), function_value_mem hc (his z)⟩ : BinaryRelationDomain D R))
              id Φnegative ↔
              ∃ f, SourceNaming (binaryRelationStructureCode D R) j f ∧
                (∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i) ∧
                (∀ q ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f q) ∧
                NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f
                  (namedNegation membershipLanguageCode (namedUnaryQueryInstance t (j ‘ x.val)))) := by
  obtain ⟨n, hn, hs, htbound, χ, hχ, heq⟩ := exists_internal_namedQueryConjunction hA hsub ht
  obtain ⟨N, rfl⟩ := hω n hn
  have heq' : ∀ f ∈ D ^ (ω : V),
      ((∀ q ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f q) ↔
        Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D R) ∅ (N : V) χ (f ↾ (N : V))) := by
    intro f hf
    exact heq _ (binaryRelationStructureCode_valid hD R) f (by simpa using hf)
  refine ⟨N, hs, htbound, ?_⟩
  intro p indices his hcover
  obtain ⟨Φpositive, hpos⟩ := exists_jointNamedQueryFormula_of_context hω hD hj hji hk hki hdis
    ht htbound hχ heq' indices his hcover
  obtain ⟨Φnegative, hneg⟩ := exists_jointNamedQueryFormula_of_context hω hD hj hji hk hki hdis
    (namedUnaryQueryNegation_valid ht) (by simpa using htbound) hχ heq' indices his hcover
  refine ⟨Φpositive, Φnegative, fun x c hc ↦ ⟨hpos x c hc, ?_⟩⟩
  simpa only [namedUnaryQueryNegation_instance] using hneg x c hc

end ZFVP
