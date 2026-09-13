import ZFVP.ModelTheory.SchmerlCodedWeaklyRubinExpansion
import ZFVP.ModelTheory.SchmerlCodedNamedSemantics

set_option autoImplicit false
namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary.Internal
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {M : Type} [SetStructure M] [Nonempty M]
variable {D E : V} (X : CodedWeaklyRubinExpansion D E)

noncomputable abbrev CodedWeaklyRubinExpansion.namedCode (t : V) : V :=
  codedNamedDeadEndExpansion D E X.classSelection X.classColor X.selectedDomains X.functionColor t

theorem CodedWeaklyRubinExpansion.realizes_namedTheory (c : ℕ → M)
    (j : ElementaryMap M (BinaryRelationDomain D E)) {t : V} (ht : t ∈ D ^ (ω : V))
    (hnames : ∀ n : ℕ, t ‘ (n : V) = (j (c n)).val) :
    ∀ φ ∈ namedWeaklyRubinTheory c,
      @Infinitary.Formula.EvalWithQ namedDeadEndLanguage (CodedDomain (X.namedCode t))
        (codedFoundationStructure (codedNamedDeadEndExpansion_valid X.carrier_nonempty E
          X.classSelection X.classColor X.selectedDomains X.functionColor ht)
          (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol
          (fun _ f ↦ namedDeadEndFunctionSymbol_valid f))
        (InternalQ (X.namedCode t)) 0 φ ![] := by
  let : Nonempty (BinaryRelationDomain D E) := binaryRelationDomain_nonempty X.carrier_nonempty
  have hd : namedConstantValue (E := E) ht = j ∘ c := funext fun n ↦ Subtype.ext (hnames n)
  intro φ hφ
  rcases hφ with ⟨σ, hσ, rfl⟩ | rfl
  · have hσ' := Semantics.modelsSet_iff.mp (models_enumeratedDiagram_of_elementaryMap j c) hσ
    change σ.EvalAux (setConstStructure (BinaryRelationDomain D E) (j ∘ c)) Empty.elim ![] at hσ'
    have he := codedNamedExpansion_namedSet_eval (E := E) (A := X.classSelection)
      (g := X.classColor) (S := X.selectedDomains) (G := X.functionColor) X.carrier_nonempty ht σ
      (Empty.elim : Empty → CodedDomain (X.namedCode t)) ![]
    have hh : σ.EvalAux (setConstStructure (BinaryRelationDomain D E) (namedConstantValue ht))
        (codedNamedBinaryEquiv D E X.classSelection X.classColor X.selectedDomains X.functionColor t ∘ Empty.elim)
        (codedNamedBinaryEquiv D E X.classSelection X.classColor X.selectedDomains X.functionColor t ∘ ![]) := by
      rw [hd]
      simpa only [Empty.eq_elim, Matrix.empty_eq] using hσ'
    exact he.mpr hh
  · have hh := (codedNamedExpansion_reduct_eval X.carrier_nonempty ht weaklyRubinSentence ![]).mp X.realizes
    simpa only [Matrix.empty_eq] using hh

theorem CodedWeaklyRubinExpansion.holds_namedTheory (c : ℕ → M)
    (j : ElementaryMap M (BinaryRelationDomain D E)) {t : V} (ht : t ∈ D ^ (ω : V))
    (hnames : ∀ n : ℕ, t ‘ (n : V) = (j (c n)).val)
    (hω : HasStandardOmega V)
    {H : V} {C : {n : ℕ} → Infinitary.Formula namedDeadEndLanguage n → V}
    {A : Set (Σ n, Infinitary.Formula namedDeadEndLanguage n)}
    (hcode : IsFragmentCoding (namedDeadEndLanguageCode : V) H
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A)
    (hroots : ∀ φ ∈ namedWeaklyRubinTheory c, ⟨0, φ⟩ ∈ A) :
    ∀ φ ∈ namedWeaklyRubinTheory c, Holds (namedDeadEndLanguageCode : V) H (X.namedCode t) 0 (C φ) ∅ := by
  intro φ hφ
  have hh := (hcode.holds_iff_evalWithQ hω
    (codedNamedDeadEndExpansion_valid X.carrier_nonempty E X.classSelection X.classColor
      X.selectedDomains X.functionColor ht)
    (fun _ f ↦ namedDeadEndFunctionSymbol_valid f) (fun _ r ↦ namedDeadEndRelationSymbol_valid r)
    φ (hroots φ hφ) (![] : Fin 0 → CodedDomain (X.namedCode t))).mpr
      (X.realizes_namedTheory c j ht hnames φ hφ)
  simpa [standardTuple] using hh

end ZFVP.Schmerl




