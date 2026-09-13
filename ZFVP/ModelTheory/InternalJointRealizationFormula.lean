import ZFVP.ModelTheory.InternalFiniteNamingData

/-! With standard omega, a finite named realization condition is a first-order
formula in the independently named upper values, with source parameters. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_binaryStandardTuple {D R b : V} {N : ℕ} (hb : b ∈ D ^ (N : V)) :
    ∃ a : Fin N → BinaryRelationDomain D R, b = standardTuple (fun t ↦ (a t).val) := by
  let a : Fin N → BinaryRelationDomain D R :=
    fun t ↦ ⟨b ‘ (t.val : V), function_value_mem hb (natCast_mem_of_lt t.isLt)⟩
  refine ⟨a, ?_⟩
  apply function_eq_of_values hb (standardTuple_mem_function _ (fun t ↦ (a t).property))
  intro i hi
  obtain ⟨t, rfl⟩ := (mem_natCast_iff i N).mp hi
  rw [value_standardTuple]

theorem jointNamedRealization_iff_of_conjunction {D R I j k c A n χ : V}
    (hD : IsNonempty D) (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ I) (hki : Injective k)
    (hdis : ∀ i ∈ range j, i ∉ range k) (hc : c ∈ D ^ I) (hn : n ⊆ (ω : V))
    (heq : ∀ f ∈ D ^ (ω : V),
      ((∀ p ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f p) ↔
        Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D R) ∅ n χ (f ↾ n))) :
    (∃ f, SourceNaming (binaryRelationStructureCode D R) j f ∧
      (∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i) ∧
      ∀ p ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f p) ↔
    ∃ b ∈ D ^ n, Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D R) ∅ n χ b ∧
      (∀ x ∈ D, j ‘ x ∈ n → b ‘ (j ‘ x) = x) ∧
      ∀ i ∈ I, k ‘ i ∈ n → b ‘ (k ‘ i) = c ‘ i := by
  constructor
  · rintro ⟨f, hf, hfk, hAf⟩
    have hfD : f ∈ D ^ (ω : V) := by simpa using hf.1
    have : IsFunction f := IsFunction.of_mem hfD
    refine ⟨f ↾ n, function_restrict_mem hfD hn, (heq f hfD).mp hAf, ?_, ?_⟩
    · intro x hx hxn
      rw [value_restrict (by rw [domain_eq_of_mem_function hfD]; exact function_value_mem hj hx) hxn]
      exact hf.2 x (by simpa using hx)
    · intro i hi hin
      rw [value_restrict (by rw [domain_eq_of_mem_function hfD]; exact function_value_mem hk hi) hin]
      exact hfk i hi
  · rintro ⟨b, hb, hbχ, hbj, hbk⟩
    obtain ⟨f, hf, hfj, hfk, hfb⟩ :=
      exists_jointSourceAssignment_extending hD hj hji hk hki hdis hc hn hb hbj hbk
    refine ⟨f, ?_, hfk, (heq f hf).mpr ?_⟩
    · simpa only [SourceNaming, binaryRelationStructureCode_domain] using And.intro hf hfj
    · rwa [hfb]

theorem exists_jointNamedRealizationFormula (hω : Schmerl.HasStandardOmega V)
    {D R I j k A : V} (hD : IsNonempty D)
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ I) (hki : Injective k)
    (hdis : ∀ i ∈ range j, i ∉ range k)
    (hA : IsInternallyFinite A) (hsub : A ⊆ namedFormulaSet membershipLanguageCode (ω : V)) :
    ∃ N : ℕ, namedTheorySupport A ⊆ (N : V) ∧
      ∀ (p : ℕ) (indices : Fin p → V) (his : ∀ t, indices t ∈ I),
        (∀ i ∈ I, k ‘ i ∈ (N : V) → ∃ t, indices t = i) →
        ∃ Φ : SetTheorySemiformula (BinaryRelationDomain D R) p,
          ∀ (c : V) (hc : c ∈ D ^ I),
            Semiformula.Eval (M := BinaryRelationDomain D R)
              (fun t ↦ (⟨c ‘ (indices t), function_value_mem hc (his t)⟩ : BinaryRelationDomain D R))
              id Φ ↔
            ∃ f, SourceNaming (binaryRelationStructureCode D R) j f ∧
              (∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i) ∧
              ∀ q ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f q := by
  obtain ⟨n, hn, hs, χ, hχ, heq⟩ := exists_internal_namedConjunction hA hsub
  obtain ⟨N, rfl⟩ := hω n hn
  have hχcode : IsMembershipFormulaCode (N : V) χ :=
    (mem_formulaSet_iff _ _ _ _).mp hχ
  obtain ⟨ψ, hψ⟩ := binary_formula_representable_of_standardOmega hω hχcode
  refine ⟨N, hs, ?_⟩
  intro p indices his hcover
  refine ⟨finiteJointNamingFormula ψ (finiteInternalSourceNames D R j N)
    (finiteInternalUpperSlots k indices N), ?_⟩
  intro c hc
  let u : Fin p → BinaryRelationDomain D R :=
    fun t ↦ ⟨c ‘ (indices t), function_value_mem hc (his t)⟩
  change Semiformula.Eval u id (finiteJointNamingFormula ψ (finiteInternalSourceNames D R j N)
    (finiteInternalUpperSlots k indices N)) ↔ _
  have hcrit := jointNamedRealization_iff_of_conjunction (R := R) (A := A) (χ := χ)
    hD hj hji hk hki hdis hc (IsTransitive.ω.transitive (N : V) hn) (by
      intro f hf
      exact heq _ (binaryRelationStructureCode_valid hD R) f (by simpa using hf))
  rw [hcrit, eval_finiteJointNamingFormula]
  constructor
  · rintro ⟨a, haψ, has, hak⟩
    refine ⟨standardTuple (fun t ↦ (a t).val),
      standardTuple_mem_function _ (fun t ↦ (a t).property), (hψ D R hD a).mpr haψ,
      (finiteInternalSourceNames_constraints hj hji a).mp has,
      (finiteInternalUpperSlots_constraints indices his hcover hc a).mp hak⟩
  · rintro ⟨b, hb, hbχ, hbs, hbk⟩
    obtain ⟨a, rfl⟩ := exists_binaryStandardTuple (R := R) hb
    exact ⟨a, (hψ D R hD a).mp hbχ,
      (finiteInternalSourceNames_constraints hj hji a).mpr hbs,
      (finiteInternalUpperSlots_constraints indices his hcover hc a).mpr hbk⟩

end ZFVP
