import ZFVP.ModelTheory.SchmerlCodedSourceForcing
import ZFVP.ModelTheory.SchmerlCodedClassSemantics
import ZFVP.ModelTheory.SchmerlCodedClassLanguageTransport

/-! An actual coded Rubin source produces a concrete class-language expansion
in a forcing extension satisfying the checked fixed class-tree sentence code.
The fragment coding is explicit and transported from the ground model. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary.Internal

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCodedRubinFinSmallSource.exists_class_sentence_realization [Countable V]
    (hAC : InternalChoice V) (hω : HasStandardOmega V) {M : V} (hsource : IsCodedRubinFinSmallSource M)
    {H : V} {C : {n : ℕ} → Infinitary.Formula classLanguage n → V}
    {A : Set (Σ n, Infinitary.Formula classLanguage n)}
    (hcode : IsFragmentCoding (classLanguageCode : V) H
      (fun {k} ↦ classFunctionSymbol (V := V) (k := k)) classRelationSymbol C A)
    (hroot : ⟨0, classTreeSentence⟩ ∈ A) :
    ∃ F : ForcingContext V, InternalChoice F.Model ∧
      F.check (hartogsNumber (ω : V)) = hartogsNumber (ω : F.Model) ∧
      ∃ D E : V, M = binaryRelationStructureCode D E ∧
      ∃ S g : F.Model, g ∈ (F.check D) ^ (F.check D) ∧
        IsStructureCode (F.check (classLanguageCode : V)) (codedClassExpansion (F.check D) (F.check E) S g) ∧
        Holds (F.check (classLanguageCode : V)) (F.check H) (codedClassExpansion (F.check D) (F.check E) S g)
          0 (F.check (C classTreeSentence)) ∅ := by
  obtain ⟨c, hc, F, hACF, hκ, ⟨f, hf, hweak⟩, hpres⟩ :=
    hsource.exists_weak_specialization_extension hAC
  obtain ⟨⟨D, E, rfl, hE⟩, hZF, _, hRubin, _⟩ := hsource
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hZF.valid.domain_nonempty
  let R := binaryIdentityRepresentation hD hE
  let : Nonempty (BinaryRelationDomain D E) := binaryRelationDomain_nonempty hD
  let : (BinaryRelationDomain D E)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := R.models_zf_of_isCodedZFModel hZF
  let j := F.checkEmbedding
  let R' := R.endExtension j
  have hκj : j (hartogsNumber (ω : V)) = hartogsNumber (ω : F.Model) := hκ
  have hL : F.check (classLanguageCode : V) = (classLanguageCode : F.Model) := map_classLanguageCode j
  have hcR : IsInternalCofinalStrictChain (hartogsNumber (ω : V))
      (codedOrdinals R.code) (codedOrdinalOrder R.code) c := hc
  have hf' : f ∈ (ω : F.Model) ^ codedSelectedClassNodes R'.code (hartogsNumber (ω : F.Model)) (j c) := by
    have he := R.endExtension_codedSelectedClassNodes j (hartogsNumber (ω : V)) c
    rw [hκj] at he
    change f ∈ (ω : F.Model) ^ j (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c) at hf
    rwa [he] at hf
  have hweak' : InternallyWeakSpecialization
      (codedSelectedClassNodes R'.code (hartogsNumber (ω : F.Model)) (j c))
      (codedSelectedClassOrder R'.code (hartogsNumber (ω : F.Model)) (j c)) f := by
    have heT := R.endExtension_codedSelectedClassNodes j (hartogsNumber (ω : V)) c
    have heS := R.endExtension_codedSelectedClassOrder j (hartogsNumber (ω : V)) c
    rw [hκj] at heT heS
    change InternallyWeakSpecialization (j (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c))
      (j (codedSelectedClassOrder R.code (hartogsNumber (ω : V)) c)) f at hweak
    rwa [heT, heS] at hweak
  have hpres' : ∀ B : F.Model,
      IsInternalCofinalBranch (j (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c))
        (j (codedSelectedClassOrder R.code (hartogsNumber (ω : V)) c))
        (j (hartogsNumber (ω : V))) (j (codedSelectedClassRank R.code (hartogsNumber (ω : V)) c)) B →
      ∃ C : V, IsInternalCofinalBranch (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c)
        (codedSelectedClassOrder R.code (hartogsNumber (ω : V)) c) (hartogsNumber (ω : V))
        (codedSelectedClassRank R.code (hartogsNumber (ω : V)) c) C ∧ j C = B := by
    intro B hB
    apply hpres B
    change IsInternalCofinalBranch (j (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c))
      (j (codedSelectedClassOrder R.code (hartogsNumber (ω : V)) c))
      (hartogsNumber (ω : F.Model)) (j (codedSelectedClassRank R.code (hartogsNumber (ω : V)) c)) B
    simpa only [hκj] using hB
  obtain ⟨g, hg, hreal⟩ := R.endExtension_classTreeSentenceWithQ hcR j hκ hRubin hpres' hω hf' hweak'
  have hcode' := classFragmentCoding_endExtension j hcode
  have hholds := R'.codedClassExpansion_holds hg (j c) (standardOmega_of_endExtension j hω) hcode' hroot hreal
  refine ⟨F, hACF, hκ, D, E, rfl, range (j c), g, hg, ?_, ?_⟩
  · rw [hL]
    exact codedClassExpansion_valid R'.carrier_nonempty R'.relation (range (j c)) g
  · rw [hL]
    exact hholds

end ZFVP.Schmerl
