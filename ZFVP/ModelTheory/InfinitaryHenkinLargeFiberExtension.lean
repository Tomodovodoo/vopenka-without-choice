import ZFVP.ModelTheory.InfinitaryGenericWeakExtension
import ZFVP.ModelTheory.InfinitaryGenericParameterizedFreezing

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage FragmentClosure FiniteCondition
universe u
variable {L : Language.{u}} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  (H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S)))

/-- The constructed successor adds a point to any specified old positive unary
fiber, is fully fragment-elementary, and preserves every old negative fiber with finite old parameters
exactly. Iteration still requires the adequate-model successor invariant. -/
theorem exists_large_fiber_extension (hS : S.Countable) {χ : Formula (limit L) 1}
    (hχ : ⟨1, χ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hq : .q χ ∈ H.carrier) :
    ∃ N : WeakModel.{u,u} (limit L),
      ∃ e : WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) H.asWeakModel N,
      ∃ a : N.Domain,
        a ∉ Set.range e ∧ Formula.WeakEval N.Q χ (a :> Fin.elim0) ∧
        ∀ n (ψ : Formula (limit L) (n + 1)),
          ⟨n + 1, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) →
          ∀ b : Fin n → H.Domain,
          ¬H.weakQuantifier {x | Formula.WeakEval H.weakQuantifier ψ (x :> b)} →
          {y : N.Domain | Formula.WeakEval N.Q ψ (y :> (e ∘ b))} =
            e '' {x : H.Domain | Formula.WeakEval H.weakQuantifier ψ (x :> b)} := by
  let p : H.FiniteCondition := ⟨0, ⟨χ, hχ, hq⟩⟩
  obtain ⟨C⟩ := GenericConditionChain.exists_genericConditionChain hS p
  refine ⟨C.asWeakModel, C.elementaryMap, C.newPoint, C.newPoint_not_mem_oldRange, ?_, ?_⟩
  · have ht := C.initial_truth
    change Formula.WeakEval C.extensionQuantifier χ
      (fun i : Fin 1 ↦ C.termClass ⟨1, .bvar i⟩) at ht
    have he : (fun i : Fin 1 ↦ C.termClass ⟨1, .bvar i⟩) = (C.newPoint :> Fin.elim0) := by
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact i.elim0
    exact he ▸ ht
  · intro n ψ hψ b hs
    exact C.parameterized_small_fiber_eq_oldImage hψ b hs

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary


