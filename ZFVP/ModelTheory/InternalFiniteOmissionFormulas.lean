import ZFVP.ModelTheory.InternalNamedContextFormula
import ZFVP.ModelTheory.InternalNamedEqualityQuery
import ZFVP.ModelTheory.InternalJointQueryFormula

/-! Three formulas over one finite context express a condition, an outside
witness, and identification with a varying old member. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_finiteOmissionFormulas (hω : Schmerl.HasStandardOmega V)
    {D R I j k A l a : V} (hD : IsNonempty D)
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ I) (hki : Injective k)
    (hdis : ∀ i ∈ range j, i ∉ range k)
    (hA : IsInternallyFinite A) (hsub : A ⊆ namedFormulaSet membershipLanguageCode (ω : V))
    (hl : l ∈ (ω : V)) (ha : a ∈ D) :
    ∃ N : ℕ, namedTheorySupport A ⊆ (N : V) ∧ l ∈ (N : V) ∧ j ‘ a ∈ (N : V) ∧
      ∀ (p : ℕ) (indices : Fin p → V) (his : ∀ z, indices z ∈ I),
        (∀ i ∈ I, k ‘ i ∈ (N : V) → ∃ z, indices z = i) →
        ∃ (B Outside : SetTheorySemiformula (BinaryRelationDomain D R) p)
          (Member : SetTheorySemiformula (BinaryRelationDomain D R) (p + 1)),
          ∀ (c : V) (hc : c ∈ D ^ I),
            let u : Fin p → BinaryRelationDomain D R :=
              fun z ↦ ⟨c ‘ (indices z), function_value_mem hc (his z)⟩
            let old : BinaryRelationDomain D R := ⟨a, ha⟩
            (Semiformula.Eval u id B ↔
              ∃ f, SourceNaming (binaryRelationStructureCode D R) j f ∧
                (∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i) ∧
                ∀ q ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f q) ∧
            (Semiformula.Eval u id Outside ↔
              ∃ f, SourceNaming (binaryRelationStructureCode D R) j f ∧
                (∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i) ∧
                (∀ q ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f q) ∧
                NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f
                  (namedNegation membershipLanguageCode (namedMembershipEntry l (j ‘ a)))) ∧
            (∀ m : BinaryRelationDomain D R, Semiformula.Eval (m :> u) id Member ↔
              ∃ f, SourceNaming (binaryRelationStructureCode D R) j f ∧
                (∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i) ∧
                (∀ q ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f q) ∧
                NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f
                  (namedEqualityEntry l (j ‘ m.val))) ∧
            (Semiformula.Eval u id B → Semiformula.Eval u id Outside ∨
              ∃ m : BinaryRelationDomain D R, m ∈ old ∧
                Semiformula.Eval (m :> u) id Member) := by
  classical
  have hM := binaryRelationStructureCode_valid hD R
  have hja : j ‘ a ∈ (ω : V) := function_value_mem hj ha
  have hb : standardTuple ![l, j ‘ a] ∈ (ω : V) ^ (2 : V) :=
    standardTuple_mem_function _ (by simp [hl, hja])
  let t : V := ⟨⟨(2 : V), truthCode⟩ₖ, standardTuple ![l, j ‘ a]⟩ₖ
  have ht : t ∈ (namedUnaryDefinitionQueries : V) := pair_mem_namedUnaryDefinitionQueries.mpr
    ⟨by simp, (formulaSet_constants membershipLanguageCode_valid (ω_succ_closed (by simp)) ∅).1, hb⟩
  obtain ⟨n, hn, hs, hbound, χ, hχ, heq⟩ := exists_internal_namedQueryConjunction hA hsub ht
  obtain ⟨N, rfl⟩ := hω n hn
  have hnω : (N : V) ⊆ (ω : V) := IsTransitive.ω.transitive (N : V) hn
  have hrange : range (standardTuple ![l, j ‘ a]) ⊆ (N : V) := by
    simpa only [t, Schmerl.definitionTuple_pair] using hbound
  have hlN : l ∈ (N : V) := hrange l (by
    have he : (standardTuple ![l, j ‘ a]) ‘ (0 : V) = l := value_standardTuple _ 0
    have hh := value_mem_range hb (by simp : (0 : V) ∈ (2 : V))
    rwa [he] at hh)
  have hjaN : j ‘ a ∈ (N : V) := hrange (j ‘ a) (by
    have he : (standardTuple ![l, j ‘ a]) ‘ (1 : V) = j ‘ a := value_standardTuple _ 1
    have hh := value_mem_range hb (by simp : (1 : V) ∈ (2 : V))
    rwa [he] at hh)
  let P : V → Prop := fun f ↦ ∀ q ∈ A,
    NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f q
  have heq' : ∀ f ∈ D ^ (ω : V),
      (P f ↔ Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D R) ∅ (N : V) χ (f ↾ (N : V))) := by
    intro f hf
    exact heq _ hM f (by simpa using hf)
  let out : V := namedNegation membershipLanguageCode (namedMembershipEntry l (j ‘ a))
  have hout : out ∈ namedFormulaSet membershipLanguageCode (ω : V) :=
    namedNegation_mem membershipLanguageCode_valid (namedMembershipEntry_valid hl hja)
  have houtSupport : namedFormulaSupport out ⊆ (N : V) := by
    simpa only [out, namedFormulaSupport, namedNegation, namedMembershipEntry,
      kpair.π₁_kpair, kpair.π₂_kpair] using hrange
  have houtφ := namedFormulaInContext_mem hn hout houtSupport
  have hχout := (formulaSet_binary membershipLanguageCode_valid hn hχ houtφ).1
  have heqout : ∀ f ∈ D ^ (ω : V),
      ((P f ∧ NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f out) ↔
        Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D R) ∅ (N : V)
          (andCode χ (namedFormulaInContext (N : V) out)) (f ↾ (N : V))) := by
    intro f hf
    have hfM : f ∈ structureDomain (binaryRelationStructureCode D R) ^ (ω : V) := by simpa using hf
    rw [satisfies_and membershipLanguageCode_valid hn hχ houtφ (function_restrict_mem hfM hnω),
      ← heq' f hf, namedFormulaInContext_satisfies hM hfM hn hout houtSupport]
  have hEqBound : range (Schmerl.definitionTuple (namedEqualityQuery l)) ⊆ (N : V) := by
    have hb' : standardTuple ![l] ∈ (N : V) ^ (1 : V) := standardTuple_mem_function _ (by simp [hlN])
    simpa only [namedEqualityQuery, Schmerl.definitionTuple_pair] using range_subset_of_mem_function hb'
  refine ⟨N, hs, hlN, hjaN, ?_⟩
  intro p indices his hcover
  obtain ⟨B, hB⟩ := exists_jointNamingFormula_of_context hω hD hj hji hk hki hdis hχ P heq' indices his hcover
  obtain ⟨Outside, hOutside⟩ := exists_jointNamingFormula_of_context hω hD hj hji hk hki hdis hχout
    (fun f ↦ P f ∧ NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f out)
    heqout indices his hcover
  obtain ⟨Member, hMemberQuery⟩ := exists_jointNamedQueryFormula_of_context hω hD hj hji hk hki hdis
    (namedEqualityQuery_valid hl) hEqBound hχ heq' indices his hcover
  have hMember (m : BinaryRelationDomain D R) (c : V) (hc : c ∈ D ^ I) :
      Semiformula.Eval (M := BinaryRelationDomain D R)
        (m :> fun z ↦ (⟨c ‘ (indices z), function_value_mem hc (his z)⟩ : BinaryRelationDomain D R)) id Member ↔
      ∃ f, SourceNaming (binaryRelationStructureCode D R) j f ∧
        (∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i) ∧ P f ∧
        NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f (namedEqualityEntry l (j ‘ m.val)) := by
    have hjm : j ‘ m.val ∈ (ω : V) := function_value_mem hj m.property
    constructor
    · intro hm
      obtain ⟨f, hf, hfk, hPf, he⟩ := (hMemberQuery m c hc).mp hm
      exact ⟨f, hf, hfk, hPf, (namedEqualityQuery_holds hM hf.1 hl hjm).mp he⟩
    · rintro ⟨f, hf, hfk, hPf, he⟩
      exact (hMemberQuery m c hc).mpr ⟨f, hf, hfk, hPf, (namedEqualityQuery_holds hM hf.1 hl hjm).mpr he⟩
  refine ⟨B, Outside, Member, ?_⟩
  intro c hc
  dsimp only
  refine ⟨hB c hc, hOutside c hc, fun m ↦ hMember m c hc, ?_⟩
  intro hBc
  obtain ⟨f, hf, hfk, hPf⟩ := (hB c hc).mp hBc
  by_cases hmem : NamedHolds membershipLanguageCode (binaryRelationStructureCode D R) f (namedMembershipEntry l (j ‘ a))
  · right
    have hfD : f ∈ D ^ (ω : V) := by simpa using hf.1
    let m : BinaryRelationDomain D R := ⟨f ‘ l, function_value_mem hfD hl⟩
    refine ⟨m, ?_, (hMember m c hc).mpr ⟨f, hf, hfk, hPf, ?_⟩⟩
    · have hmem' := (namedMembershipEntry_holds hf.1 hl hja).mp hmem
      rw [hf.2 a (by simpa using ha)] at hmem'
      exact (Schmerl.codedMember_binary_iff hD m.property ha).mp hmem'
    · apply (namedEqualityEntry_holds hM hf.1 hl (function_value_mem hj m.property)).mpr
      rw [hf.2 m.val (by simpa using m.property)]
  · left
    exact (hOutside c hc).mpr ⟨f, hf, hfk, hPf,
      (namedHolds_negation membershipLanguageCode_valid hf.1 (namedMembershipEntry_valid hl hja)).mpr hmem⟩

end ZFVP
