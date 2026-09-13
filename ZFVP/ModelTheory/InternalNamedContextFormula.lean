import ZFVP.ModelTheory.InternalJointRealizationFormula

/-! A fixed internal context can be reused to compile several realization
conditions over the same upper-coordinate list. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_jointNamingFormula_of_context (hω : Schmerl.HasStandardOmega V)
    {D R I j k χ : V} {N p : ℕ} (hD : IsNonempty D)
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ I) (hki : Injective k)
    (hdis : ∀ i ∈ range j, i ∉ range k)
    (hχ : χ ∈ formulaSet membershipLanguageCode ∅ (N : V))
    (P : V → Prop) (heq : ∀ f ∈ D ^ (ω : V),
      (P f ↔ Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D R) ∅ (N : V) χ (f ↾ (N : V))))
    (indices : Fin p → V) (his : ∀ z, indices z ∈ I)
    (hcover : ∀ i ∈ I, k ‘ i ∈ (N : V) → ∃ z, indices z = i) :
    ∃ Φ : SetTheorySemiformula (BinaryRelationDomain D R) p,
      ∀ (c : V) (hc : c ∈ D ^ I),
        Semiformula.Eval (M := BinaryRelationDomain D R)
          (fun z ↦ (⟨c ‘ (indices z), function_value_mem hc (his z)⟩ : BinaryRelationDomain D R)) id Φ ↔
        ∃ f, SourceNaming (binaryRelationStructureCode D R) j f ∧
          (∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i) ∧ P f := by
  have hn : (N : V) ∈ (ω : V) := by simp
  have hnω : (N : V) ⊆ (ω : V) := IsTransitive.ω.transitive (N : V) hn
  have hχcode : IsMembershipFormulaCode (N : V) χ := (mem_formulaSet_iff _ _ _ _).mp hχ
  obtain ⟨ψ, hψ⟩ := binary_formula_representable_of_standardOmega hω hχcode
  refine ⟨finiteJointNamingFormula ψ (finiteInternalSourceNames D R j N)
    (finiteInternalUpperSlots k indices N), ?_⟩
  intro c hc
  let u : Fin p → BinaryRelationDomain D R :=
    fun z ↦ ⟨c ‘ (indices z), function_value_mem hc (his z)⟩
  change Semiformula.Eval u id (finiteJointNamingFormula ψ (finiteInternalSourceNames D R j N)
    (finiteInternalUpperSlots k indices N)) ↔ _
  rw [eval_finiteJointNamingFormula]
  constructor
  · rintro ⟨a, haψ, has, hak⟩
    have hb := standardTuple_mem_function (fun z ↦ (a z).val) (fun z ↦ (a z).property)
    obtain ⟨f, hf, hfj, hfk, hfb⟩ := exists_jointSourceAssignment_extending hD hj hji hk hki hdis hc hnω hb
      ((finiteInternalSourceNames_constraints hj hji a).mp has)
      ((finiteInternalUpperSlots_constraints indices his hcover hc a).mp hak)
    refine ⟨f, ?_, hfk, (heq f hf).mpr ?_⟩
    · simpa only [SourceNaming, binaryRelationStructureCode_domain] using And.intro hf hfj
    · rw [hfb]
      exact (hψ D R hD a).mpr haψ
  · rintro ⟨f, hsource, hfk, hPf⟩
    have hf : f ∈ D ^ (ω : V) := by simpa using hsource.1
    have hfb := function_restrict_mem hf hnω
    have : IsFunction f := IsFunction.of_mem hf
    obtain ⟨a, ha⟩ := exists_binaryStandardTuple (R := R) hfb
    have haχ := (heq f hf).mp hPf
    rw [ha] at haχ
    refine ⟨a, (hψ D R hD a).mp haχ,
      (finiteInternalSourceNames_constraints hj hji a).mpr ?_,
      (finiteInternalUpperSlots_constraints indices his hcover hc a).mpr ?_⟩
    · intro y hy hyn
      rw [← ha, value_restrict (by rw [domain_eq_of_mem_function hf]; exact function_value_mem hj hy) hyn]
      exact hsource.2 y (by simpa using hy)
    · intro i hi hin
      rw [← ha, value_restrict (by rw [domain_eq_of_mem_function hf]; exact function_value_mem hk hi) hin]
      exact hfk i hi

end ZFVP
