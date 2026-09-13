import ZFVP.ModelTheory.NamedMembershipStructure
import ZFVP.ModelTheory.SchmerlNamedDiagram
import ZFVP.ModelTheory.SchmerlCodedDeadEndLanguageTransport

set_option autoImplicit false
namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary.Internal

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def namedDeadEndLanguageCode : V :=
  languageCode ω (relationSymbols (deadEndLanguageCode : V)) (constantGraph ω 0)
    (relationArities (deadEndLanguageCode : V))

theorem namedDeadEndLanguageCode_valid : IsLanguageCode (namedDeadEndLanguageCode : V) := by
  rw [namedDeadEndLanguageCode, isLanguageCode_iff]
  exact ⟨constantGraph_mem_function ω ω 0 (ofNat_mem_ω 0), deadEndLanguageCode_valid.2.2⟩

noncomputable def namedDeadEndFunctionSymbol {k : ℕ} (f : namedDeadEndLanguage.Func k) : V :=
  match f with
  | .inl f => deadEndFunctionSymbol f
  | .inr (.const n) => (n : V)

noncomputable def namedDeadEndRelationSymbol {k : ℕ} (r : namedDeadEndLanguage.Rel k) : V :=
  match r with
  | .inl r => deadEndRelationSymbol r
  | .inr r => r.elim

theorem namedDeadEndFunctionSymbol_valid {k : ℕ} (f : namedDeadEndLanguage.Func k) :
    namedDeadEndFunctionSymbol (V := V) f ∈ functionSymbols (namedDeadEndLanguageCode : V) ∧
    (functionArities (namedDeadEndLanguageCode : V)) ‘ (namedDeadEndFunctionSymbol f) = (k : V) := by
  cases f with
  | inl f =>
      have hh := (deadEndFunctionSymbol_valid (V := V) f).1
      simp [deadEndLanguageCode] at hh
  | inr f =>
      cases f with
      | const n =>
          simp only [namedDeadEndFunctionSymbol, namedDeadEndLanguageCode,
            functionSymbols_code, functionArities_code]
          exact ⟨by simp, value_constantGraph _ _ (by simp)⟩

theorem namedDeadEndRelationSymbol_valid {k : ℕ} (r : namedDeadEndLanguage.Rel k) :
    namedDeadEndRelationSymbol (V := V) r ∈ relationSymbols (namedDeadEndLanguageCode : V) ∧
    (relationArities (namedDeadEndLanguageCode : V)) ‘ (namedDeadEndRelationSymbol r) = (k : V) := by
  cases r with
  | inl r => simpa only [namedDeadEndRelationSymbol, namedDeadEndLanguageCode, relationSymbols_code, relationArities_code] using deadEndRelationSymbol_valid (V := V) r
  | inr r => exact r.elim

noncomputable def codedNamedDeadEndExpansion (D E A g S G t : V) : V :=
  structureCode D (namedMembershipFunctions ω D t)
    (structureRelations (codedDeadEndExpansion D E A g S G))

@[simp] theorem codedNamedDeadEndExpansion_domain (D E A g S G t : V) :
    structureDomain (codedNamedDeadEndExpansion D E A g S G t) = D := by
  simp [codedNamedDeadEndExpansion]

theorem codedNamedDeadEndExpansion_valid {D : V} (hD : IsNonempty D)
    (E A g S G : V) {t : V} (ht : t ∈ D ^ (ω : V)) :
    IsStructureCode namedDeadEndLanguageCode (codedNamedDeadEndExpansion D E A g S G t) := by
  have hold := codedDeadEndExpansion_valid hD E A g S G
  simp only [IsStructureCode, codedNamedDeadEndExpansion, namedDeadEndLanguageCode,
    structureDomain_code, structureFunctions_code, structureRelations_code, namedMembershipFunctions,
    functionSymbols_code, relationSymbols_code, functionArities_code, relationArities_code]
  refine ⟨namedDeadEndLanguageCode_valid, True.intro, hD, inferInstance,
    domain_definableGraph _ _ _, hold.2.2.2.2.2.1, hold.2.2.2.2.2.2.1, ?_, ?_⟩
  · intro n hn
    rw [value_definableGraph _ _ _ hn, value_constantGraph _ _ hn]
    exact constantGraph_mem_function _ D _ (function_value_mem ht hn)
  · simpa only [codedDeadEndExpansion_domain] using hold.2.2.2.2.2.2.2.2

theorem codedNamedDeadEndExpansion_structureEq {D : V} (hD : IsNonempty D)
    (E A g S G : V) {t : V} (ht : t ∈ D ^ (ω : V)) :
    @Structure.Eq namedDeadEndLanguage (CodedDomain (codedNamedDeadEndExpansion D E A g S G t))
      (codedFoundationStructure (codedNamedDeadEndExpansion_valid hD E A g S G ht)
        (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol
        (fun _ f ↦ namedDeadEndFunctionSymbol_valid f)) inferInstance := by
  let : Structure namedDeadEndLanguage (CodedDomain (codedNamedDeadEndExpansion D E A g S G t)) :=
    codedFoundationStructure (codedNamedDeadEndExpansion_valid hD E A g S G ht)
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol
      (fun _ f ↦ namedDeadEndFunctionSymbol_valid f)
  constructor
  intro a b
  change standardTuple ![a.val, b.val] ∈
    (structureRelations (codedNamedDeadEndExpansion D E A g S G t)) ‘ (0 : V) ↔ a = b
  simp only [codedNamedDeadEndExpansion, structureRelations_code]
  have h04 : (0 : V) ≠ 4 := natCast_injective.ne (by decide)
  have h05 : (0 : V) ≠ 5 := natCast_injective.ne (by decide)
  have hr := codedDeadEndExpansion_relation D E A g S G
    (Sum.inl (Sum.inl Language.Set.Rel.eq))
  change (structureRelations (codedDeadEndExpansion D E A g S G)) ‘ (0 : V) = _ at hr
  rw [hr]
  simp only [deadEndRelationSymbol, classRelationSymbol, membershipSymbol,
    deadEndRelationInterpretation, h04, h05, ite_false, classRelationInterpretation, ite_true]
  rw [standardTuple_mem_equalityRelation]
  · exact Subtype.val_injective.eq_iff
  · intro i
    fin_cases i
    · simpa using a.property
    · simpa using b.property

end ZFVP.Schmerl


