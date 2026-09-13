import ZFVP.ModelTheory.SchmerlForcedRubinConstruction
import ZFVP.ModelTheory.SchmerlCodedWeaklyRubinExpansion
import ZFVP.ModelTheory.ForcingCheckedTruth
import ZFVP.ModelTheory.EndExtensionBinaryRelation

/-! Starting from the actual countable coded model, construct both forcing
extensions and a full weakly Rubin expansion. The original elementary map is
retained after the second forcing; no diamond or specialization input remains. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]

theorem exists_forced_weaklyRubin_extension
    (hAC : InternalChoice V) (hω : HasStandardOmega V) {D E : V}
    (hM : IsCodedZFModel (binaryRelationStructureCode D E)) (hE : E ⊆ D ×ˢ D)
    (hcount : IsInternallyCountable D) :
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
            Nonempty (CodedWeaklyRubinExpansion (G.check B) (G.check R)) := by
  obtain ⟨F, hACF, hκF, N, e, hsource, he, _⟩ :=
    exists_forced_codedRubinFinSmall_extension hAC hω hM hE hcount
  have hωF := standardOmega_of_endExtension F.checkEmbedding hω
  obtain ⟨G, hACG, hκG, B, R, hN, hreal⟩ := hsource.exists_weaklyRubin_expansion hACF hωF
  have heB : IsCodedElementaryEmbedding membershipLanguageCode
      (binaryRelationStructureCode (F.check D) (F.check E)) (binaryRelationStructureCode B R) e := by
    simpa only [hN] using he
  exact ⟨F, hACF, hκF, N, e, hsource, he, G, hACG,
    by rw [hκF, hκG], B, R, hN, G.checkEmbedding.map_codedBinaryElementaryEmbedding heB, hreal⟩

end ZFVP.Schmerl
