import ZFVP.ModelTheory.SchmerlCodedRefutation
import ZFVP.ModelTheory.SchmerlNamedDeadEndCodingGround

set_option autoImplicit false
namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary ZFVP.Infinitary.Internal
universe u

structure NamedDeadEndRefutationSupport
    (A : Set (Σ n, Infinitary.Formula namedDeadEndLanguage n))
    (Γ : Set (Infinitary.Sentence namedDeadEndLanguage)) : Prop where
  countable : A.Countable
  closed : SubformulaClosed A
  roots : ∀ φ ∈ Γ, ⟨0, φ⟩ ∈ A
  sound : KeislerSoundOn.{u} A Γ (.neg (.fo .verum : Infinitary.Sentence namedDeadEndLanguage))

theorem exists_namedDeadEndRefutationSupport {Γ : Set (Infinitary.Sentence namedDeadEndLanguage)}
    (hΓ : Γ.Countable)
    (d : KeislerDerivation Γ (.neg (.fo .verum : Infinitary.Sentence namedDeadEndLanguage))) :
    ∃ A, NamedDeadEndRefutationSupport.{u} A Γ := by
  obtain ⟨A, hA, hclosed, hroots, _, hs⟩ := d.exists_closed_countable_soundness_support hΓ
  exact ⟨A, hA, hclosed, hroots, hs⟩

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {A : Set (Σ n, Infinitary.Formula namedDeadEndLanguage n)}
  {Γ : Set (Infinitary.Sentence namedDeadEndLanguage)}

theorem NamedDeadEndRefutationSupport.false_of_codedRealization
    (hs : NamedDeadEndRefutationSupport.{u} A Γ)
    (hω : HasStandardOmega V) (hAC : InternalChoice V)
    {H : V} {C : {n : ℕ} → Infinitary.Formula namedDeadEndLanguage n → V}
    (hcode : IsFragmentCoding (namedDeadEndLanguageCode : V) H
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A)
    {D E S g T G t : V} (hD : IsNonempty D) (ht : t ∈ D ^ (ω : V))
    (hholds : ∀ φ ∈ Γ, Holds (namedDeadEndLanguageCode : V) H
      (codedNamedDeadEndExpansion D E S g T G t) 0 (C φ) ∅) : False := by
  exact hcode.false_of_refutation_support hω hAC (codedNamedDeadEndExpansion_valid hD E S g T G ht)
    (fun _ f ↦ namedDeadEndFunctionSymbol_valid f) (fun _ r ↦ namedDeadEndRelationSymbol_valid r)
    (codedNamedDeadEndExpansion_structureEq hD E S g T G ht) hs.sound hs.roots hholds

variable {U : Type u} [SetStructure U] [Nonempty U] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem NamedDeadEndRefutationSupport.false_of_endExtension_realization
    (hs : NamedDeadEndRefutationSupport.{u} A Γ) (j : MembershipEndExtension V U)
    (hω : HasStandardOmega V) (hACU : InternalChoice U)
    {H : V} {C : {n : ℕ} → Infinitary.Formula namedDeadEndLanguage n → V}
    (hcode : IsFragmentCoding (namedDeadEndLanguageCode : V) H
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A)
    {D E S g T G t : U} (hD : IsNonempty D) (ht : t ∈ D ^ (ω : U))
    (hholds : ∀ φ ∈ Γ, Holds (j (namedDeadEndLanguageCode : V)) (j H)
      (codedNamedDeadEndExpansion D E S g T G t) 0 (j (C φ)) ∅) : False := by
  apply hs.false_of_codedRealization (standardOmega_of_endExtension j hω) hACU
    (namedDeadEndFragmentCoding_endExtension j hcode) hD ht
  simpa only [map_namedDeadEndLanguageCode j] using hholds

end ZFVP.Schmerl
