import ZFVP.ModelTheory.SchmerlNamedBlockCriterion
import ZFVP.ModelTheory.InternalJointQueryFormula
import ZFVP.ModelTheory.SchmerlBinaryInseparability

/-! The actual separation-omission candidate sets are dense. The cofinal
exclusion formulas retain the old element as one bound variable. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem namedHolds_union_singleton (L M f A q : V) :
    (∀ r ∈ A ∪ {q}, NamedHolds L M f r) ↔
      (∀ r ∈ A, NamedHolds L M f r) ∧ NamedHolds L M f q := by
  constructor
  · intro h
    exact ⟨fun r hr ↦ h r (mem_union_iff.mpr (Or.inl hr)), h q (by simp)⟩
  · rintro ⟨hA, hq⟩ r hr
    rcases mem_union_iff.mp hr with hr | hr
    · exact hA r hr
    · simpa only [mem_singleton_iff.mp hr] using hq

theorem namedSeparationOmissionDense_dense (hAC : InternalChoice V) (hω : HasStandardOmega V)
    {D E j k U W t : V} (hD : IsNonempty D)
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ codedDirectedPosetIndex (binaryRelationStructureCode D E)) (hki : Injective k)
    (hdis : ∀ n ∈ range j, n ∉ range k)
    (hUW : IsCodedInseparable (binaryRelationStructureCode D E) U W)
    (ht : t ∈ (namedUnaryDefinitionQueries : V)) :
    ForcingDense
      (namedFiniteConditions membershipLanguageCode (binaryRelationStructureCode D E) j
        (namedUpperBackground (binaryRelationStructureCode D E) j k))
      (reverseInclusionOrder (namedFiniteConditions membershipLanguageCode (binaryRelationStructureCode D E) j
        (namedUpperBackground (binaryRelationStructureCode D E) j k)))
      (namedSeparationOmissionDense
        (namedFiniteConditions membershipLanguageCode (binaryRelationStructureCode D E) j
          (namedUpperBackground (binaryRelationStructureCode D E) j k)) j U W t) := by
  classical
  let : Nonempty (BinaryRelationDomain D E) := binaryRelationDomain_nonempty hD
  refine ⟨namedSeparationOmissionDense_subset _ _ _ _ _, fun A hA ↦ ?_⟩
  obtain ⟨hAv, hAfin, hAf⟩ := (mem_namedFiniteConditions _ _ _ _ _).mp hA
  obtain ⟨N, _, _, hform⟩ := exists_jointNamedQueryFormulas hω hD hj hji hk hki hdis hAfin hAv ht
  obtain ⟨p, indices, hinj, hi, hcoverI, _⟩ := exists_finiteUpperIndices hk hki N
  obtain ⟨Φpos, Φneg, hΦ⟩ := hform p indices hi hcoverI
  choose δ ρ hδ hρ hdir using fun z ↦ codedDirectedPoset_sourceFormulas hω hD (hi z)
  let B : SetTheorySemiformula (BinaryRelationDomain D E) p := ∃¹ (Φpos ⋎ Φneg)
  have hv (x : BinaryRelationDomain D E) : namedUnaryQueryInstance t (j ‘ x.val) ∈
      namedFormulaSet membershipLanguageCode (ω : V) := namedUnaryQueryInstance_valid ht (function_value_mem hj x.property)
  have hB : ∀ (c : V) (hc : c ∈ D ^ codedDirectedPosetIndex (binaryRelationStructureCode D E)),
      B.Eval (fun z ↦ ⟨c ‘ (indices z), function_value_mem hc (hi z)⟩) id ↔
        ∃ f, ZFVP.SourceNaming (binaryRelationStructureCode D E) j f ∧
          (∀ i ∈ codedDirectedPosetIndex (binaryRelationStructureCode D E), f ‘ (k ‘ i) = c ‘ i) ∧
          ∀ q ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D E) f q := by
    intro c hc
    change (∃ x, Φpos.Eval (x :> _) id ∨ Φneg.Eval (x :> _) id) ↔ _
    constructor
    · rintro ⟨x, hx | hx⟩
      · obtain ⟨f, hf, hfk, hAf, _⟩ := (hΦ x c hc).1.mp hx
        exact ⟨f, hf, hfk, hAf⟩
      · obtain ⟨f, hf, hfk, hAf, _⟩ := (hΦ x c hc).2.mp hx
        exact ⟨f, hf, hfk, hAf⟩
    · rintro ⟨f, hf, hfk, hAf⟩
      let x : BinaryRelationDomain D E := Classical.choice inferInstance
      by_cases hq : NamedHolds membershipLanguageCode (binaryRelationStructureCode D E) f (namedUnaryQueryInstance t (j ‘ x.val))
      · exact ⟨x, Or.inl ((hΦ x c hc).1.mpr ⟨f, hf, hfk, hAf, hq⟩)⟩
      · exact ⟨x, Or.inr ((hΦ x c hc).2.mpr ⟨f, hf, hfk, hAf,
          (namedHolds_negation membershipLanguageCode_valid hf.1 (hv x)).mpr hq⟩)⟩
  have hcover : ∀ x s, B.Eval s id → Φneg.Eval (x :> s) id ∨ Φpos.Eval (x :> s) id := by
    intro x s hs
    obtain ⟨c, hc, rfl⟩ := exists_upperTupleAssignment hD indices hi hinj s
    obtain ⟨f, hf, hfk, hAf⟩ := (hB c hc).mp hs
    by_cases hq : NamedHolds membershipLanguageCode (binaryRelationStructureCode D E) f (namedUnaryQueryInstance t (j ‘ x.val))
    · exact Or.inr ((hΦ x c hc).1.mpr ⟨f, hf, hfk, hAf, hq⟩)
    · exact Or.inl ((hΦ x c hc).2.mpr ⟨f, hf, hfk, hAf,
        (namedHolds_negation membershipLanguageCode_valid hf.1 (hv x)).mpr hq⟩)
  have hblock := (finiteSource_iff_finiteBlock hAC hD hj hji hk hki hdis hAfin hAv
    indices hi hinj δ ρ hδ hρ (fun s ↦ B.Eval s id) hB).mp hAf
  have hext (q : V) (hq : q ∈ namedFormulaSet membershipLanguageCode (ω : V))
      (Ψ : SetTheorySemiformula (BinaryRelationDomain D E) p)
      (hΨ : ∀ (c : V) (hc : c ∈ D ^ codedDirectedPosetIndex (binaryRelationStructureCode D E)),
        Ψ.Eval (fun z ↦ ⟨c ‘ (indices z), function_value_mem hc (hi z)⟩) id ↔
          ∃ f, ZFVP.SourceNaming (binaryRelationStructureCode D E) j f ∧
            (∀ i ∈ codedDirectedPosetIndex (binaryRelationStructureCode D E), f ‘ (k ‘ i) = c ‘ i) ∧
            (∀ r ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D E) f r) ∧
            NamedHolds membershipLanguageCode (binaryRelationStructureCode D E) f q)
      (hΨblock : FiniteBlockEx δ ρ fun s ↦ Ψ.Eval s id) :
      A ∪ {q} ∈ namedFiniteConditions membershipLanguageCode (binaryRelationStructureCode D E) j
        (namedUpperBackground (binaryRelationStructureCode D E) j k) := by
    have hfin : IsInternallyFinite (A ∪ {q}) := internallyFinite_union hAfin (by
      simpa using internallyFinite_insert internallyFinite_empty q)
    have hsub : A ∪ {q} ⊆ namedFormulaSet membershipLanguageCode (ω : V) := by
      intro r hr
      rcases mem_union_iff.mp hr with hr | hr
      · exact hAv r hr
      · exact (mem_singleton_iff.mp hr) ▸ hq
    apply (mem_namedFiniteConditions _ _ _ _ _).mpr
    refine ⟨hsub, hfin, (finiteSource_iff_finiteBlock hAC hD hj hji hk hki hdis hfin hsub
      indices hi hinj δ ρ hδ hρ (fun s ↦ Ψ.Eval s id) ?_).mpr hΨblock⟩
    intro c hc
    rw [hΨ c hc]
    apply exists_congr
    intro f
    exact and_congr Iff.rfl (and_congr Iff.rfl (namedHolds_union_singleton _ _ _ _ _).symm)
  rcases rubin_finiteIndex_inseparable_cons_split δ ρ hdir hUW.binary_inseparable B Φneg Φpos hcover hblock with
    ⟨x, hx, hxblock⟩ | ⟨x, hx, hxblock⟩
  · let q := namedNegation membershipLanguageCode (namedUnaryQueryInstance t (j ‘ x.val))
    let Ψ : SetTheorySemiformula (BinaryRelationDomain D E) p :=
      Rew.bind (&x :> fun z ↦ #z) Semiterm.fvar ▹ Φneg
    have heval (s : Fin p → BinaryRelationDomain D E) : Ψ.Eval s id ↔ Φneg.Eval (x :> s) id := by
      simp only [Ψ, Semiformula.eval_rew]
      have he : Semiterm.val (L := ℒₛₑₜ) s id ∘ (&x :> fun z ↦ #z) = x :> s := by
        funext z
        refine Fin.cases ?_ (fun i ↦ ?_) z <;> simp
      simpa only [Rew.bind_bvar, Rew.bind_fvar, Function.comp_def, Semiterm.val_fvar] using
        iff_of_eq (congrArg (fun b ↦ Φneg.Eval b id) he)
    have hnew := hext q (namedNegation_mem membershipLanguageCode_valid (hv x)) Ψ
      (fun c hc ↦ (heval _).trans (hΦ x c hc).2) (by simpa only [heval] using hxblock)
    exact ⟨A ∪ {q}, (mem_namedSeparationOmissionDense _ _ _ _ _ _).mpr
      ⟨hnew, Or.inl ⟨x.val, hx, by simp [q]⟩⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hnew, hA, fun _ hr ↦ mem_union_iff.mpr (Or.inl hr)⟩⟩
  · let q := namedUnaryQueryInstance t (j ‘ x.val)
    let Ψ : SetTheorySemiformula (BinaryRelationDomain D E) p :=
      Rew.bind (&x :> fun z ↦ #z) Semiterm.fvar ▹ Φpos
    have heval (s : Fin p → BinaryRelationDomain D E) : Ψ.Eval s id ↔ Φpos.Eval (x :> s) id := by
      simp only [Ψ, Semiformula.eval_rew]
      have he : Semiterm.val (L := ℒₛₑₜ) s id ∘ (&x :> fun z ↦ #z) = x :> s := by
        funext z
        refine Fin.cases ?_ (fun i ↦ ?_) z <;> simp
      simpa only [Rew.bind_bvar, Rew.bind_fvar, Function.comp_def, Semiterm.val_fvar] using
        iff_of_eq (congrArg (fun b ↦ Φpos.Eval b id) he)
    have hnew := hext q (hv x) Ψ (fun c hc ↦ (heval _).trans (hΦ x c hc).1)
      (by simpa only [heval] using hxblock)
    exact ⟨A ∪ {q}, (mem_namedSeparationOmissionDense _ _ _ _ _ _).mpr
      ⟨hnew, Or.inr ⟨x.val, hx, by simp [q]⟩⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hnew, hA, fun _ hr ↦ mem_union_iff.mpr (Or.inl hr)⟩⟩

end ZFVP.Schmerl
