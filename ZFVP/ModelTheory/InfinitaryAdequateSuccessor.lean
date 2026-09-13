import ZFVP.ModelTheory.InfinitaryAdequateParameterizedFibers
import ZFVP.ModelTheory.InfinitaryAdequateLimits

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel.AdequateGenericChain
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}
  {p₀ : AdequateFiniteCondition M S} (C : AdequateGenericChain M S p₀)

noncomputable def asWeakModel : WeakModel.{u,0} L where
  Domain := C.Domain
  str := C.extensionStructure
  eq := C.extensionStructure_eq
  nonempty := inferInstance
  countable := inferInstance
  Q := C.extensionQuantifier
  mono := C.extensionQuantifier_mono

theorem oldEmbedding_func {n} (f : L.Func n) (b : Fin n → M.Domain) :
    C.oldEmbedding (Structure.func f b) =
      Structure.func (self := C.extensionStructure) f (C.oldEmbedding ∘ b) := by
  let φ : Formula L (n + 1) := Formula.termEqual (.bvar 0) (.func f (fun i ↦ .bvar i.succ))
  have hf : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) := FragmentClosure.fo_closed _
  have hold : Formula.WeakEval M.Q φ (Structure.func f b :> b) := by
    rw [Formula.weakEval_termEqual]
    rfl
  have hnew := (C.extension_elementary φ hf (Structure.func f b :> b)).mpr hold
  rw [Formula.weakEval_termEqual] at hnew
  exact hnew

theorem oldEmbedding_rel {n} (r : L.Rel n) (b : Fin n → M.Domain) :
    Structure.rel (self := C.extensionStructure) r (C.oldEmbedding ∘ b) ↔ Structure.rel r b :=
  C.extension_elementary (.fo (.rel r (fun i ↦ .bvar i))) (FragmentClosure.fo_closed _) b

noncomputable def elementaryMap :
    WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) M C.asWeakModel where
  toFun := C.oldEmbedding
  injective := C.oldEmbedding_injective
  func := C.oldEmbedding_func
  rel := C.oldEmbedding_rel
  elementary := C.extension_elementary

theorem asWeakModel_adequate : C.asWeakModel.Adequate S := C.adequate.of_elementary C.elementaryMap

theorem elementaryMap_freezes : C.elementaryMap.FreezesSmallFibers := by
  intro n φ hφ b hs
  exact C.parameterized_small_fiber_eq_oldImage φ hφ b hs

end WeakModel.AdequateGenericChain

namespace WeakModel
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

/-- The semantic construction supplies an adequate elementary successor for every
positive old definable fiber, with exact freezing of all old negative fibers. -/
theorem exists_adequate_successor_smallDomain (hM : M.Adequate S) (hS : S.Countable)
    {n} (φ : Formula L (n + 1))
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (b : Fin n → M.Domain) (hq : M.Q {x | Formula.WeakEval M.Q φ (x :> b)}) :
    ∃ N : WeakModel.{u,0} L,
      ∃ e : WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) M N,
        N.Adequate S ∧ e.FreezesSmallFibers ∧
          ∃ a : N.Domain, a ∉ Set.range e ∧ Formula.WeakEval N.Q φ (a :> e ∘ b) := by
  let p := ParameterInstance.unaryInstance φ hφ b
  have hp : M.Q (ParameterInstance.projection (k := 0) p) := by
    simpa only [p, ParameterInstance.projection, ParameterInstance.exsN,
      ParameterInstance.eval_unaryInstance, Matrix.cons_val_zero] using hq
  let p₀ : AdequateFiniteCondition M S := ⟨0, ⟨p, hp⟩⟩
  obtain ⟨C⟩ := AdequateGenericChain.exists_chain hM hS p₀
  refine ⟨C.asWeakModel, C.elementaryMap, C.asWeakModel_adequate, C.elementaryMap_freezes,
    C.classOf 0, C.newPoint_not_oldImage, ?_⟩
  have hi : C.Eval p (0 :> Fin.elim0) := by
    convert C.initial_truth using 1
    funext i
    fin_cases i
    rfl
  have ht := (C.eval_unaryInstance φ hφ b 0).mp hi
  have hnew := (C.extension_truth φ hφ (0 :> C.oldCoordinate ∘ b)).mpr ht
  change Formula.WeakEval C.extensionQuantifier φ (C.classOf 0 :> C.oldEmbedding ∘ b)
  simpa only [C.classOf_cons, AdequateGenericChain.oldEmbedding, Function.comp_def] using hnew

end WeakModel
end ZFVP.Infinitary


