import ZFVP.ModelTheory.SchmerlCodedClassExpansion
import ZFVP.ModelTheory.SchmerlEndExtensionFragmentCoding
import ZFVP.Syntax.EndExtensionMembershipSyntax

/-! The finite class language and its symbol map agree across end extensions,
so the ground fragment code remains a code for the same fixed sentence. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary.Internal

variable {V U : Type*} [SetStructure V] [SetStructure U]
  [Nonempty V] [Nonempty U] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (j : MembershipEndExtension V U)

theorem map_classRelationArity (r : V) : j (classRelationArity r) = classRelationArity (j r) := by
  classical
  have htwo : j (2 : V) = (2 : U) := j.map_numeral 2
  unfold classRelationArity
  by_cases hr : r = 2
  · simp only [hr, htwo, ite_true]
    exact j.map_numeral 1
  · have hjr : j r ≠ 2 := by rw [← htwo]; exact j.injective.ne hr
    simp only [hr, hjr, ite_false]
    exact htwo

theorem map_classLanguageCode : j (classLanguageCode : V) = (classLanguageCode : U) := by
  have he := j.map_definableGraph (4 : V) classRelationArity classRelationArity
    (by definability) (by definability) (fun r _ ↦ map_classRelationArity j r)
  unfold classLanguageCode
  rw [j.map_languageCode, j.map_constantGraph, j.map_empty, he,
    show j (4 : V) = (4 : U) from j.map_numeral 4]

omit [Nonempty V] [Nonempty U] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem map_classFunctionSymbol {k : ℕ} (f : classLanguage.Func k) :
    j (classFunctionSymbol (V := V) f) = classFunctionSymbol (V := U) f := by
  cases f with
  | inl f => exact Empty.elim f
  | inr f => exact Empty.elim f

theorem map_classRelationSymbol {k : ℕ} (r : classLanguage.Rel k) :
    j (classRelationSymbol (V := V) r) = classRelationSymbol (V := U) r := by
  cases r with
  | inl r => cases r <;> exact j.map_numeral _
  | inr r => cases r <;> exact j.map_numeral _

theorem classFragmentCoding_endExtension {H : V}
    {C : {n : ℕ} → Infinitary.Formula classLanguage n → V}
    {A : Set (Σ n, Infinitary.Formula classLanguage n)}
    (h : IsFragmentCoding (classLanguageCode : V) H
      (fun {k} ↦ classFunctionSymbol (V := V) (k := k)) classRelationSymbol C A) :
    IsFragmentCoding (classLanguageCode : U) (j H)
      (fun {k} ↦ classFunctionSymbol (V := U) (k := k)) classRelationSymbol (fun φ ↦ j (C φ)) A := by
  have h' := h.map_endExtension j
  simpa only [map_classLanguageCode j, map_classFunctionSymbol j, map_classRelationSymbol j] using h'

end ZFVP.Schmerl
