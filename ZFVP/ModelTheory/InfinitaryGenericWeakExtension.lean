import ZFVP.ModelTheory.InfinitaryGenericElementarity
import ZFVP.ModelTheory.InfinitaryWeakChain

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}

noncomputable def asWeakModel
    (H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))) : WeakModel (limit L) where
  Domain := H.Domain
  str := H.termStructure
  eq := H.termStructure_eq
  nonempty := inferInstance
  countable := inferInstance
  Q := H.weakQuantifier
  mono := fun _ _ h ↦ H.weakQuantifier_mono h

namespace GenericConditionChain
variable {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

noncomputable def asWeakModel : WeakModel (limit L) where
  Domain := C.ExtensionDomain
  str := C.extensionStructure
  eq := C.extensionStructure_eq
  nonempty := inferInstance
  countable := inferInstance
  Q := C.extensionQuantifier
  mono := C.extensionQuantifier_mono

theorem oldEmbedding_func {n} (f : (limit L).Func n) (b : Fin n → H.Domain) :
    C.oldEmbedding (Structure.func f b) =
      Structure.func (self := C.extensionStructure) f (C.oldEmbedding ∘ b) := by
  let φ : Formula (limit L) (n + 1) :=
    Formula.termEqual (.bvar 0) (.func f (fun i ↦ .bvar i.succ))
  have hf : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) := fo_in_fragment _
  have hold : Formula.WeakEval H.weakQuantifier φ (Structure.func f b :> b) := by
    rw [Formula.weakEval_termEqual]
    rfl
  have hnew := (C.extension_elementary φ hf (Structure.func f b :> b)).mpr hold
  rw [Formula.weakEval_termEqual] at hnew
  change C.oldEmbedding (Structure.func f b) = _ at hnew
  exact hnew

theorem oldEmbedding_rel {n} (r : (limit L).Rel n) (b : Fin n → H.Domain) :
    Structure.rel (self := C.extensionStructure) r (C.oldEmbedding ∘ b) ↔ Structure.rel r b := by
  exact C.extension_elementary (atom r) (fo_in_fragment _) b

noncomputable def elementaryMap :
    WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) H.asWeakModel C.asWeakModel where
  toFun := C.oldEmbedding
  injective := C.oldEmbedding_injective
  func := C.oldEmbedding_func
  rel := C.oldEmbedding_rel
  elementary := C.extension_elementary

end GenericConditionChain
end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary

