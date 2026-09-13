import ZFVP.ModelTheory.InfinitaryAdequateModel
import ZFVP.ModelTheory.InfinitaryGenericWeakExtension

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}

/-- The initial Henkin model satisfies every adequacy schema under all parameter
assignments, using its proved theorem semantics. -/
theorem asWeakModel_adequate
    (H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))) :
    H.asWeakModel.Adequate S where
  twoPoints i j b := H.weakEval_theorem (Formula.qTwoPoints i j)
    (qTwoPoints_closed i j) (.qSmall i j) b
  finiteUnion φ ψ hφ hψ b := H.weakEval_theorem (Formula.qFiniteUnion φ ψ)
    (qFiniteUnion_closed hφ hψ) (KeislerDerivation.qBinaryUnion φ ψ) b
  countableUnion f hf b := H.weakEval_theorem (Formula.qCountableUnion f)
    (qCountableUnion_closed hf) (.boolean (.qUnion f)) b
  interchange φ hφ b := H.weakEval_theorem (Formula.qInterchange φ)
    (qInterchange_closed hφ) (.qInterchange φ) b

namespace GenericConditionChain
variable {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition}

/-- The actual generic quotient is adequate at every tuple of its new domain. -/
theorem asWeakModel_adequate (C : GenericConditionChain H p₀) : C.asWeakModel.Adequate S :=
  H.asWeakModel_adequate.of_elementary C.elementaryMap

end GenericConditionChain
end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary
