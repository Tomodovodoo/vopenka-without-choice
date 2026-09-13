import ZFVP.ModelTheory.SchmerlCodedDeadEndExpansion
import ZFVP.ModelTheory.SchmerlCodedClassLanguageTransport
import ZFVP.ModelTheory.SchmerlFragmentHull
import ZFVP.SetTheory.FunctionUnion

/-! The canonical finite dead-end language agrees across end extensions,
elementary maps, and the actual fragment coding hull. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary.Internal

variable {V U : Type*} [SetStructure V] [SetStructure U]
  [Nonempty V] [Nonempty U] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_deadEndRelationArity (j : MembershipEndExtension V U) (r : V) :
    j (deadEndRelationArity r) = deadEndRelationArity (j r) := by
  classical
  have hfive : j (5 : V) = (5 : U) := j.map_numeral 5
  unfold deadEndRelationArity
  by_cases hr : r = 5
  · simp only [hr, hfive, ite_true]
    exact j.map_numeral 3
  · have hjr : j r ≠ 5 := by rw [← hfive]; exact j.injective.ne hr
    simp only [hr, hjr, ite_false]
    exact map_classRelationArity j r

theorem map_deadEndLanguageCode (j : MembershipEndExtension V U) :
    j (deadEndLanguageCode : V) = (deadEndLanguageCode : U) := by
  have he := j.map_definableGraph (6 : V) deadEndRelationArity deadEndRelationArity
    (by definability) (by definability) (fun r _ ↦ map_deadEndRelationArity j r)
  unfold deadEndLanguageCode
  rw [j.map_languageCode, j.map_constantGraph, j.map_empty, he,
    show j (6 : V) = (6 : U) from j.map_numeral 6]

omit [Nonempty V] [Nonempty U] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem map_deadEndFunctionSymbol (j : MembershipEndExtension V U) {k : ℕ} (f : deadEndLanguage.Func k) :
    j (deadEndFunctionSymbol (V := V) f) = deadEndFunctionSymbol (V := U) f := by
  cases f with
  | inl f => exact map_classFunctionSymbol j f
  | inr f => exact Empty.elim f

theorem map_deadEndRelationSymbol (j : MembershipEndExtension V U) {k : ℕ} (r : deadEndLanguage.Rel k) :
    j (deadEndRelationSymbol (V := V) r) = deadEndRelationSymbol (V := U) r := by
  cases r with
  | inl r => exact map_classRelationSymbol j r
  | inr r => cases r <;> exact j.map_numeral _

theorem deadEndFragmentCoding_endExtension (j : MembershipEndExtension V U) {H : V}
    {C : {n : ℕ} → Infinitary.Formula deadEndLanguage n → V}
    {A : Set (Σ n, Infinitary.Formula deadEndLanguage n)}
    (h : IsFragmentCoding (deadEndLanguageCode : V) H
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A) :
    IsFragmentCoding (deadEndLanguageCode : U) (j H)
      (fun {k} ↦ deadEndFunctionSymbol (V := U) (k := k)) deadEndRelationSymbol (fun φ ↦ j (C φ)) A := by
  have h' := h.map_endExtension j
  simpa only [map_deadEndLanguageCode j, map_deadEndFunctionSymbol j, map_deadEndRelationSymbol j] using h'

theorem elementary_map_classRelationArity (j : ZFVP.ElementaryMap V U) (r : V) :
    j (classRelationArity r) = classRelationArity (j r) := by
  classical
  have htwo : j (2 : V) = (2 : U) := j.map_numeral 2
  unfold classRelationArity
  by_cases hr : r = 2
  · simp only [hr, htwo, ite_true]
    exact j.map_numeral 1
  · have hjr : j r ≠ 2 := by rw [← htwo]; exact j.injective.ne hr
    simp only [hr, hjr, ite_false]
    exact htwo

theorem elementary_map_deadEndRelationArity (j : ZFVP.ElementaryMap V U) (r : V) :
    j (deadEndRelationArity r) = deadEndRelationArity (j r) := by
  classical
  have hfive : j (5 : V) = (5 : U) := j.map_numeral 5
  unfold deadEndRelationArity
  by_cases hr : r = 5
  · simp only [hr, hfive, ite_true]
    exact j.map_numeral 3
  · have hjr : j r ≠ 5 := by rw [← hfive]; exact j.injective.ne hr
    simp only [hr, hjr, ite_false]
    exact elementary_map_classRelationArity j r

private theorem deadEndArityGraph_eq_tuple :
    definableGraph (6 : V) deadEndRelationArity (by definability) =
      standardTuple (fun i : Fin 6 ↦ deadEndRelationArity (i.val : V)) := by
  apply functions_eq_of_domain_values
  · rw [domain_definableGraph, domain_standardTuple]
    rfl
  · intro r hr
    rw [domain_definableGraph] at hr
    obtain ⟨i, rfl⟩ := (mem_natCast_iff r 6).mp hr
    rw [value_definableGraph _ _ _ hr, value_standardTuple]

theorem elementary_map_deadEndLanguageCode (j : ZFVP.ElementaryMap V U) :
    j (deadEndLanguageCode : V) = (deadEndLanguageCode : U) := by
  have he : j (definableGraph (6 : V) deadEndRelationArity (by definability)) =
      definableGraph (6 : U) deadEndRelationArity (by definability) := by
    rw [deadEndArityGraph_eq_tuple, deadEndArityGraph_eq_tuple, j.map_standardTuple]
    congr 1
    funext i
    exact (elementary_map_deadEndRelationArity j (i.val : V)).trans (congrArg deadEndRelationArity (j.map_numeral i.val))
  have hc : j (constantGraph (∅ : V) ∅) = constantGraph (∅ : U) ∅ := by
    have hh := j.map_definedFunction constantGraphFormula (fun v ↦ constantGraph (v 0) (v 1))
      (fun v ↦ constantGraph (v 0) (v 1)) ![(∅ : V), ∅]
    simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, j.map_empty] using hh
  unfold deadEndLanguageCode languageCode
  rw [j.map_kpair, j.map_kpair, j.map_kpair, j.map_empty, hc, he,
    show j (6 : V) = (6 : U) from j.map_numeral 6]

omit [Nonempty V] [Nonempty U] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem elementary_map_deadEndFunctionSymbol (j : ZFVP.ElementaryMap V U) {k : ℕ} (f : deadEndLanguage.Func k) :
    j (deadEndFunctionSymbol (V := V) f) = deadEndFunctionSymbol (V := U) f := by
  cases f with
  | inl f => cases f with
    | inl f => exact Empty.elim f
    | inr f => exact Empty.elim f
  | inr f => exact Empty.elim f

theorem elementary_map_deadEndRelationSymbol (j : ZFVP.ElementaryMap V U) {k : ℕ} (r : deadEndLanguage.Rel k) :
    j (deadEndRelationSymbol (V := V) r) = deadEndRelationSymbol (V := U) r := by
  cases r with
  | inl r => cases r with
    | inl r => cases r <;> exact j.map_numeral _
    | inr r => cases r <;> exact j.map_numeral _
  | inr r => cases r <;> exact j.map_numeral _

theorem deadEndFragmentCoding_elementary (j : ZFVP.ElementaryMap V U) {H : V}
    {C : {n : ℕ} → Infinitary.Formula deadEndLanguage n → V}
    {A : Set (Σ n, Infinitary.Formula deadEndLanguage n)}
    (h : IsFragmentCoding (deadEndLanguageCode : V) H
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A) :
    IsFragmentCoding (deadEndLanguageCode : U) (j H)
      (fun {k} ↦ deadEndFunctionSymbol (V := U) (k := k)) deadEndRelationSymbol (fun φ ↦ j (C φ)) A := by
  have h' := h.map_elementary j
  simpa only [elementary_map_deadEndLanguageCode j, elementary_map_deadEndFunctionSymbol j,
    elementary_map_deadEndRelationSymbol j] using h'

abbrev DeadEndCodingHull (H : V) (C : {n : ℕ} → Infinitary.Formula deadEndLanguage n → V)
    (A : Set (Σ n, Infinitary.Formula deadEndLanguage n)) (S : Set V) :=
  CodingHull (deadEndLanguageCode : V) H
    (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A S

variable (H : V) (C : {n : ℕ} → Infinitary.Formula deadEndLanguage n → V)
  (A : Set (Σ n, Infinitary.Formula deadEndLanguage n)) (S : Set V)

theorem codingHullLanguage_deadEnd :
    codingHullLanguage (deadEndLanguageCode : V) H
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A S =
      (deadEndLanguageCode : DeadEndCodingHull H C A S) := by
  let j := codingHullMap (deadEndLanguageCode : V) H
    (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A S
  apply j.injective
  change (deadEndLanguageCode : V) = j (deadEndLanguageCode : DeadEndCodingHull H C A S)
  exact (elementary_map_deadEndLanguageCode j).symm

theorem codingHullFunction_deadEnd {k : ℕ} (f : deadEndLanguage.Func k) :
    codingHullFunction (deadEndLanguageCode : V) H
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A S f =
      deadEndFunctionSymbol (V := DeadEndCodingHull H C A S) f := by
  let j := codingHullMap (deadEndLanguageCode : V) H
    (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A S
  apply j.injective
  exact (elementary_map_deadEndFunctionSymbol j f).symm

theorem codingHullRelation_deadEnd {k : ℕ} (r : deadEndLanguage.Rel k) :
    codingHullRelation (deadEndLanguageCode : V) H
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A S r =
      deadEndRelationSymbol (V := DeadEndCodingHull H C A S) r := by
  let j := codingHullMap (deadEndLanguageCode : V) H
    (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A S
  apply j.injective
  exact (elementary_map_deadEndRelationSymbol j r).symm

theorem deadEndFragmentCoding_codingHull
    (h : IsFragmentCoding (deadEndLanguageCode : V) H
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A) :
    IsFragmentCoding (deadEndLanguageCode : DeadEndCodingHull H C A S)
      (codingHullFragment (deadEndLanguageCode : V) H
        (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A S)
      (fun {k} ↦ deadEndFunctionSymbol (V := DeadEndCodingHull H C A S) (k := k))
      deadEndRelationSymbol
      (codingHullFormula (deadEndLanguageCode : V) H
        (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A S) A := by
  have hh := codingHull_coding (deadEndLanguageCode : V) H
    (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A S h
  have hF : (fun {k} (f : deadEndLanguage.Func k) ↦ codingHullFunction (deadEndLanguageCode : V) H
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A S f) =
      (fun {k} (f : deadEndLanguage.Func k) ↦ deadEndFunctionSymbol (V := DeadEndCodingHull H C A S) f) := by
    funext k f
    exact codingHullFunction_deadEnd H C A S f
  have hR : (fun {k} (r : deadEndLanguage.Rel k) ↦ codingHullRelation (deadEndLanguageCode : V) H
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A S r) =
      (fun {k} (r : deadEndLanguage.Rel k) ↦ deadEndRelationSymbol (V := DeadEndCodingHull H C A S) r) := by
    funext k r
    exact codingHullRelation_deadEnd H C A S r
  simpa only [codingHullLanguage_deadEnd, hF, hR] using hh

end ZFVP.Schmerl
