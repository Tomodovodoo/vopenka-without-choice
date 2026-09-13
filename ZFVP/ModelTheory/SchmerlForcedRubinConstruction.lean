import ZFVP.ModelTheory.SchmerlInternalRubinConstruction
import ZFVP.ModelTheory.SchmerlCodedRepresentedDefinitions
import ZFVP.ModelTheory.SemanticStandardCodedZFModel
import ZFVP.Syntax.StandardOmegaMembershipSyntax

/-! Force diamond over the actual ambient model, then apply the internal
Rubin construction there to the checked original model. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem codedBinaryZF_endExtension (j : MembershipEndExtension V W) (hω : HasStandardOmega V)
    {D E : V} (hM : IsCodedZFModel (binaryRelationStructureCode D E)) (hE : E ⊆ D ×ˢ D) :
    IsCodedZFModel (binaryRelationStructureCode (j D) (j E)) := by
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hM.valid.domain_nonempty
  let R := binaryIdentityRepresentation hD hE
  let : Nonempty (BinaryRelationDomain D E) := binaryRelationDomain_nonempty hD
  let : (BinaryRelationDomain D E)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := R.models_zf_of_isCodedZFModel hM
  exact (R.endExtension j).isCodedZFModel_of_semanticStandardSyntax
    (semanticStandardMembershipSyntax_of_standardOmega (standardOmega_of_endExtension j hω))

theorem internallyCountable_endExtension (j : MembershipEndExtension V W) {D : V}
    (hD : IsInternallyCountable D) : IsInternallyCountable (j D) := by
  simpa only [IsInternallyCountable, j.map_omega] using j.map_cardLE hD

theorem exists_forced_codedRubinFinSmall_extension [Countable V]
    (hAC : InternalChoice V) (hω : HasStandardOmega V) {D E : V}
    (hM : IsCodedZFModel (binaryRelationStructureCode D E)) (hE : E ⊆ D ×ˢ D)
    (hcount : IsInternallyCountable D) :
    ∃ F : ForcingContext V, InternalChoice F.Model ∧
      F.check (hartogsNumber (ω : V)) = hartogsNumber (ω : F.Model) ∧
      ∃ N e : F.Model, IsCodedRubinFinSmallSource N ∧
        IsCodedElementaryEmbedding membershipLanguageCode
          (binaryRelationStructureCode (F.check D) (F.check E)) N e ∧
        structureDomain N = hartogsNumber (ω : F.Model) := by
  obtain ⟨F, hACF, hκ, hdiamond⟩ := exists_internalDiamond_forcingExtension hAC
  have hωF := standardOmega_of_endExtension F.checkEmbedding hω
  have hMF := codedBinaryZF_endExtension F.checkEmbedding hω hM hE
  have hcountF := internallyCountable_endExtension F.checkEmbedding hcount
  exact ⟨F, hACF, hκ, exists_codedRubinFinSmall_extension_of_internalDiamond hACF hωF
    (eval_internalDiamondSentence.mp hdiamond) hMF hcountF⟩

end ZFVP.Schmerl
