import ZFVP.ModelTheory.SchmerlCodedRefutation
import ZFVP.ModelTheory.SchmerlCodedDeadEndEquality
import ZFVP.ModelTheory.SchmerlCodedDeadEndLanguageTransport

/-! A standard refutation supplies its own countable ground support. The
checked support contradicts an actual coded realization after forcing. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary ZFVP.Infinitary.Internal

universe u

structure DeadEndRefutationSupport
    (A : Set (Σ n, Infinitary.Formula deadEndLanguage n))
    (φ : Infinitary.Formula deadEndLanguage 0) : Prop where
  countable : A.Countable
  closed : SubformulaClosed A
  root : ⟨0, φ⟩ ∈ A
  sound : KeislerSoundOn.{u} A {φ} (.neg (.fo .verum : Infinitary.Sentence deadEndLanguage))

theorem exists_deadEndRefutationSupport {φ : Infinitary.Formula deadEndLanguage 0}
    (d : KeislerDerivation {φ} (.neg (.fo .verum : Infinitary.Sentence deadEndLanguage))) :
    ∃ A, DeadEndRefutationSupport.{u} A φ := by
  obtain ⟨A, hA, hclosed, hΓ, _, hs⟩ :=
    d.exists_closed_countable_soundness_support (Set.countable_singleton φ)
  exact ⟨A, hA, hclosed, hΓ φ (Set.mem_singleton φ), hs⟩

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {A : Set (Σ n, Infinitary.Formula deadEndLanguage n)} {φ : Infinitary.Formula deadEndLanguage 0}

theorem DeadEndRefutationSupport.false_of_codedRealization (hs : DeadEndRefutationSupport.{u} A φ)
    (hω : HasStandardOmega V) (hAC : InternalChoice V)
    {H : V} {C : {n : ℕ} → Infinitary.Formula deadEndLanguage n → V}
    (hcode : IsFragmentCoding (deadEndLanguageCode : V) H
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A)
    {D E S g T G : V} (hD : IsNonempty D)
    (hholds : Holds (deadEndLanguageCode : V) H (codedDeadEndExpansion D E S g T G) 0 (C φ) ∅) : False := by
  apply hcode.false_of_refutation_support hω hAC (codedDeadEndExpansion_valid hD E S g T G)
    (fun _ f ↦ deadEndFunctionSymbol_valid f) (fun _ r ↦ deadEndRelationSymbol_valid r)
    (codedDeadEndExpansion_structureEq hD E S g T G) hs.sound
  · intro ψ hψ
    have he : ψ = φ := Set.mem_singleton_iff.mp hψ
    exact he.symm ▸ hs.root
  · intro ψ hψ
    have he : ψ = φ := Set.mem_singleton_iff.mp hψ
    exact he.symm ▸ hholds

variable {U : Type u} [SetStructure U] [Nonempty U] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem DeadEndRefutationSupport.false_of_endExtension_realization
    (hs : DeadEndRefutationSupport.{u} A φ) (j : MembershipEndExtension V U)
    (hω : HasStandardOmega V) (hACU : InternalChoice U)
    {H : V} {C : {n : ℕ} → Infinitary.Formula deadEndLanguage n → V}
    (hcode : IsFragmentCoding (deadEndLanguageCode : V) H
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A)
    {D E S g T G : U} (hD : IsNonempty D)
    (hholds : Holds (j (deadEndLanguageCode : V)) (j H)
      (codedDeadEndExpansion D E S g T G) 0 (j (C φ)) ∅) : False := by
  apply hs.false_of_codedRealization (standardOmega_of_endExtension j hω) hACU
    (deadEndFragmentCoding_endExtension j hcode) hD
  simpa only [map_deadEndLanguageCode j] using hholds

end ZFVP.Schmerl
