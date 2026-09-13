import ZFVP.ModelTheory.SchmerlCodedNamedLanguage
import ZFVP.ModelTheory.ElementaryLanguageSymbols

set_option autoImplicit false
namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary.Internal
variable {V U : Type*} [SetStructure V] [SetStructure U]
  [Nonempty V] [Nonempty U] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_namedDeadEndLanguageCode (j : MembershipEndExtension V U) :
    j (namedDeadEndLanguageCode : V) = (namedDeadEndLanguageCode : U) := by
  unfold namedDeadEndLanguageCode
  rw [j.map_languageCode, j.map_omega, j.map_relationSymbols, j.map_relationArities,
    map_deadEndLanguageCode, j.map_constantGraph, j.map_omega, (show j (0 : V) = (0 : U) from j.map_numeral 0)]

theorem elementary_map_namedDeadEndLanguageCode (j : ZFVP.ElementaryMap V U) :
    j (namedDeadEndLanguageCode : V) = (namedDeadEndLanguageCode : U) := by
  have hc : j (constantGraph (ω : V) 0) = constantGraph (ω : U) 0 := by
    have hh := j.map_definedFunction constantGraphFormula (fun v ↦ constantGraph (v 0) (v 1))
      (fun v ↦ constantGraph (v 0) (v 1)) ![(ω : V), 0]
    simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one,
      j.map_omega, (show j (0 : V) = (0 : U) from j.map_numeral 0)] using hh
  unfold namedDeadEndLanguageCode languageCode
  rw [j.map_kpair, j.map_kpair, j.map_kpair, j.map_omega, hc,
    j.map_relationSymbols, j.map_relationArities, elementary_map_deadEndLanguageCode]

theorem map_namedDeadEndFunctionSymbol (j : MembershipEndExtension V U) {k : ℕ}
    (f : namedDeadEndLanguage.Func k) :
    j (namedDeadEndFunctionSymbol (V := V) f) = namedDeadEndFunctionSymbol (V := U) f := by
  cases f with
  | inl f => exact map_deadEndFunctionSymbol j f
  | inr f => cases f; exact j.map_numeral _

theorem elementary_map_namedDeadEndFunctionSymbol (j : ZFVP.ElementaryMap V U) {k : ℕ}
    (f : namedDeadEndLanguage.Func k) :
    j (namedDeadEndFunctionSymbol (V := V) f) = namedDeadEndFunctionSymbol (V := U) f := by
  cases f with
  | inl f => exact elementary_map_deadEndFunctionSymbol j f
  | inr f => cases f; exact j.map_numeral _

theorem map_namedDeadEndRelationSymbol (j : MembershipEndExtension V U) {k : ℕ}
    (r : namedDeadEndLanguage.Rel k) :
    j (namedDeadEndRelationSymbol (V := V) r) = namedDeadEndRelationSymbol (V := U) r := by
  cases r with
  | inl r => exact map_deadEndRelationSymbol j r
  | inr r => exact r.elim

theorem elementary_map_namedDeadEndRelationSymbol (j : ZFVP.ElementaryMap V U) {k : ℕ}
    (r : namedDeadEndLanguage.Rel k) :
    j (namedDeadEndRelationSymbol (V := V) r) = namedDeadEndRelationSymbol (V := U) r := by
  cases r with
  | inl r => exact elementary_map_deadEndRelationSymbol j r
  | inr r => exact r.elim

theorem namedDeadEndFragmentCoding_endExtension (j : MembershipEndExtension V U) {H : V}
    {C : {n : ℕ} → Infinitary.Formula namedDeadEndLanguage n → V}
    {A : Set (Σ n, Infinitary.Formula namedDeadEndLanguage n)}
    (h : IsFragmentCoding (namedDeadEndLanguageCode : V) H
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A) :
    IsFragmentCoding (namedDeadEndLanguageCode : U) (j H)
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := U) (k := k)) namedDeadEndRelationSymbol (fun φ ↦ j (C φ)) A := by
  have h' := h.map_endExtension j
  simpa only [map_namedDeadEndLanguageCode j, map_namedDeadEndFunctionSymbol j, map_namedDeadEndRelationSymbol j] using h'

theorem namedDeadEndFragmentCoding_elementary (j : ZFVP.ElementaryMap V U) {H : V}
    {C : {n : ℕ} → Infinitary.Formula namedDeadEndLanguage n → V}
    {A : Set (Σ n, Infinitary.Formula namedDeadEndLanguage n)}
    (h : IsFragmentCoding (namedDeadEndLanguageCode : V) H
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A) :
    IsFragmentCoding (namedDeadEndLanguageCode : U) (j H)
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := U) (k := k)) namedDeadEndRelationSymbol (fun φ ↦ j (C φ)) A := by
  have h' := h.map_elementary j
  simpa only [elementary_map_namedDeadEndLanguageCode j, elementary_map_namedDeadEndFunctionSymbol j,
    elementary_map_namedDeadEndRelationSymbol j] using h'

abbrev NamedDeadEndCodingHull (H : V) (C : {n : ℕ} → Infinitary.Formula namedDeadEndLanguage n → V)
    (A : Set (Σ n, Infinitary.Formula namedDeadEndLanguage n)) (S : Set V) :=
  CodingHull (namedDeadEndLanguageCode : V) H
    (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A S

variable (H : V) (C : {n : ℕ} → Infinitary.Formula namedDeadEndLanguage n → V)
  (A : Set (Σ n, Infinitary.Formula namedDeadEndLanguage n)) (S : Set V)

theorem codingHullLanguage_namedDeadEnd :
    codingHullLanguage (namedDeadEndLanguageCode : V) H
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A S =
      (namedDeadEndLanguageCode : NamedDeadEndCodingHull H C A S) := by
  let j := codingHullMap (namedDeadEndLanguageCode : V) H
    (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A S
  apply j.injective
  change (namedDeadEndLanguageCode : V) = j (namedDeadEndLanguageCode : NamedDeadEndCodingHull H C A S)
  exact (elementary_map_namedDeadEndLanguageCode j).symm

theorem codingHullFunction_namedDeadEnd {k : ℕ} (f : namedDeadEndLanguage.Func k) :
    codingHullFunction (namedDeadEndLanguageCode : V) H
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A S f =
      namedDeadEndFunctionSymbol (V := NamedDeadEndCodingHull H C A S) f := by
  let j := codingHullMap (namedDeadEndLanguageCode : V) H
    (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A S
  apply j.injective
  exact (elementary_map_namedDeadEndFunctionSymbol j f).symm

theorem codingHullRelation_namedDeadEnd {k : ℕ} (r : namedDeadEndLanguage.Rel k) :
    codingHullRelation (namedDeadEndLanguageCode : V) H
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A S r =
      namedDeadEndRelationSymbol (V := NamedDeadEndCodingHull H C A S) r := by
  let j := codingHullMap (namedDeadEndLanguageCode : V) H
    (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A S
  apply j.injective
  exact (elementary_map_namedDeadEndRelationSymbol j r).symm

theorem namedDeadEndFragmentCoding_codingHull
    (h : IsFragmentCoding (namedDeadEndLanguageCode : V) H
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A) :
    IsFragmentCoding (namedDeadEndLanguageCode : NamedDeadEndCodingHull H C A S)
      (codingHullFragment (namedDeadEndLanguageCode : V) H
        (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A S)
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := NamedDeadEndCodingHull H C A S) (k := k))
      namedDeadEndRelationSymbol
      (codingHullFormula (namedDeadEndLanguageCode : V) H
        (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A S) A := by
  have hh := codingHull_coding (namedDeadEndLanguageCode : V) H
    (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A S h
  have hF : (fun {k} (f : namedDeadEndLanguage.Func k) ↦ codingHullFunction (namedDeadEndLanguageCode : V) H
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A S f) =
      (fun {k} (f : namedDeadEndLanguage.Func k) ↦ namedDeadEndFunctionSymbol (V := NamedDeadEndCodingHull H C A S) f) := by
    funext k f
    exact codingHullFunction_namedDeadEnd H C A S f
  have hR : (fun {k} (r : namedDeadEndLanguage.Rel k) ↦ codingHullRelation (namedDeadEndLanguageCode : V) H
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A S r) =
      (fun {k} (r : namedDeadEndLanguage.Rel k) ↦ namedDeadEndRelationSymbol (V := NamedDeadEndCodingHull H C A S) r) := by
    funext k r
    exact codingHullRelation_namedDeadEnd H C A S r
  simpa only [codingHullLanguage_namedDeadEnd, hF, hR] using hh

end ZFVP.Schmerl



