import ZFVP.ModelTheory.SchmerlNamedForcedRefutation
import ZFVP.ModelTheory.SchmerlNamedRefutationTransport
import ZFVP.ModelTheory.SchmerlNamedWeaklyRubinRealization
import ZFVP.ModelTheory.SchmerlForcedWeaklyRubinConstruction
import ZFVP.ModelTheory.CodedBinaryElementaryMap

set_option autoImplicit false
namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary.Internal

/-- The explicit countable named theory has no refutation. The argument puts
an actual refutation support and all original names into one countable ground,
then uses the two proved forcing constructions and internal-Q soundness. -/
theorem namedWeaklyRubinTheory_consistent {M : Type}
    [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M] (c : ℕ → M) :
    Infinitary.KeislerDerivation.Consistent (namedWeaklyRubinTheory c) := by
  intro d
  obtain ⟨A, hs⟩ := exists_namedDeadEndRefutationSupport (namedWeaklyRubinTheory_countable c) d
  let V₀ := NamedDeadEndCodingGround M c A hs.countable
  let R₀ : BinaryRelationRepresentation (V := V₀) M :=
    namedDeadEndCodingGroundRepresentation M c A hs.countable
  have hω₀ : HasStandardOmega V₀ := namedDeadEndCodingGround_standardOmega M c A hs.countable
  have hAC₀ : InternalChoice V₀ := namedDeadEndCodingGround_choice M c A hs.countable
  have hcode₀ := namedDeadEndCodingGround_coding M c A hs.countable hs.closed
  have hM : IsCodedZFModel R₀.code :=
    namedDeadEndCodingGroundRepresentation_isCodedZFModel M c A hs.countable
  exact hs.false_of_forcedNamedTheory hAC₀ hω₀ R₀ hM
    (namedDeadEndCodingGroundRepresentation_countable M c A hs.countable)
    (namedDeadEndCodingGroundNames_function M c A hs.countable)
    (fun n ↦ namedDeadEndCodingGroundNames_value M c A hs.countable n) hcode₀

/-- Every countable ZF model has an elementary weakly Rubin extension of
cardinality exactly aleph-one, using the actual forcing and completeness proofs. -/
theorem exists_alephOneWeaklyRubinExtension (M : Type)
    [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M] :
    Nonempty (AlephOneWeaklyRubinExtension M) := by
  obtain ⟨c, hc⟩ := exists_surjective_nat M
  exact elementary_extension_of_named_consistency c hc (namedWeaklyRubinTheory_consistent c)

end ZFVP.Schmerl


