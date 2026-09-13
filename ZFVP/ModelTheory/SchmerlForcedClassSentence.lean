import ZFVP.ModelTheory.SchmerlForcedRubinConstruction
import ZFVP.ModelTheory.SchmerlCodedSourceClassSentence
import ZFVP.ModelTheory.ForcingCheckedTruth
import ZFVP.ModelTheory.EndExtensionBinaryRelation

/-! The two forcing steps produce the checked fixed class-tree sentence
from an actual countable original model and an actual fragment coding. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary.Internal
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]

theorem exists_forced_class_sentence_realization
    (hAC : InternalChoice V) (hω : HasStandardOmega V) {D E : V}
    (hM : IsCodedZFModel (binaryRelationStructureCode D E)) (hE : E ⊆ D ×ˢ D)
    (hcount : IsInternallyCountable D)
    {H : V} {C : {n : ℕ} → Infinitary.Formula classLanguage n → V}
    {A : Set (Σ n, Infinitary.Formula classLanguage n)}
    (hcode : IsFragmentCoding (classLanguageCode : V) H
      (fun {k} ↦ classFunctionSymbol (V := V) (k := k)) classRelationSymbol C A)
    (hroot : ⟨0, classTreeSentence⟩ ∈ A) :
    ∃ F : ForcingContext V, InternalChoice F.Model ∧
      F.check (hartogsNumber (ω : V)) = hartogsNumber (ω : F.Model) ∧
      ∃ N e : F.Model, IsCodedRubinFinSmallSource N ∧
        IsCodedElementaryEmbedding membershipLanguageCode
          (binaryRelationStructureCode (F.check D) (F.check E)) N e ∧
        ∃ G : ForcingContext F.Model, InternalChoice G.Model ∧
          G.check (F.check (hartogsNumber (ω : V))) = hartogsNumber (ω : G.Model) ∧
          ∃ B R : F.Model, N = binaryRelationStructureCode B R ∧
            IsCodedElementaryEmbedding membershipLanguageCode
              (binaryRelationStructureCode (G.check (F.check D)) (G.check (F.check E)))
              (binaryRelationStructureCode (G.check B) (G.check R)) (G.check e) ∧
            ∃ S g : G.Model, g ∈ (G.check B) ^ (G.check B) ∧
              IsStructureCode (G.check (F.check (classLanguageCode : V)))
                (codedClassExpansion (G.check B) (G.check R) S g) ∧
              Holds (G.check (F.check (classLanguageCode : V))) (G.check (F.check H))
                (codedClassExpansion (G.check B) (G.check R) S g)
                0 (G.check (F.check (C classTreeSentence))) ∅ := by
  obtain ⟨F, hACF, hκF, N, e, hsource, he, _⟩ :=
    exists_forced_codedRubinFinSmall_extension hAC hω hM hE hcount
  have hωF := standardOmega_of_endExtension F.checkEmbedding hω
  have hcodeF := classFragmentCoding_endExtension F.checkEmbedding hcode
  have hLF : F.check (classLanguageCode : V) = (classLanguageCode : F.Model) :=
    map_classLanguageCode F.checkEmbedding
  have hcheck : ∀ x : V, F.checkEmbedding.toFun x = F.check x := fun _ ↦ rfl
  obtain ⟨G, hACG, hκG, B, R, hN, S, g, hg, hvalid, hholds⟩ :=
    hsource.exists_class_sentence_realization hACF hωF hcodeF hroot
  have heB : IsCodedElementaryEmbedding membershipLanguageCode
      (binaryRelationStructureCode (F.check D) (F.check E)) (binaryRelationStructureCode B R) e := by
    simpa only [hN] using he
  refine ⟨F, hACF, hκF, N, e, hsource, he, G, hACG, ?_, B, R, hN,
    G.checkEmbedding.map_codedBinaryElementaryEmbedding heB, S, g, hg, ?_, ?_⟩
  · rw [hκF, hκG]
  · simpa only [hLF] using hvalid
  · simpa only [hLF, hcheck] using hholds

end ZFVP.Schmerl
