import ZFVP.ModelTheory.InfinitaryAdequateSuccessor
import ZFVP.ModelTheory.InfinitaryWeakModelLift
import ZFVP.ModelTheory.InfinitaryWeakMapComposition

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

/-- A successor in the same domain universe, ready for repeated construction. -/
theorem exists_adequate_successor (hM : M.Adequate S) (hS : S.Countable)
    {n} (φ : Formula L (n + 1))
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (b : Fin n → M.Domain) (hq : M.Q {x | Formula.WeakEval M.Q φ (x :> b)}) :
    ∃ N : WeakModel.{u,v} L,
      ∃ e : WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) M N,
        N.Adequate S ∧ e.FreezesSmallFibers ∧
          ∃ a : N.Domain, a ∉ Set.range e ∧ Formula.WeakEval N.Q φ (a :> e ∘ b) := by
  obtain ⟨N, e, hN, he, a, ha, ht⟩ := exists_adequate_successor_smallDomain hM hS φ hφ b hq
  let f := N.uliftEmbedding.{u,0,v} (FragmentClosure.carrier (SequenceClosure.carrier S))
  refine ⟨N.ulift.{u,0,v}, f.comp e, N.ulift_adequate hN,
    e.comp_freezes f he (N.uliftEmbedding_freezes _), ULift.up a, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    exact ha ⟨x, ULift.up_injective hx⟩
  · have h := (N.ulift_weakEval_up.{u,0,v} φ (a :> e ∘ b)).mpr ht
    have hb : (ULift.up ∘ (a :> e ∘ b) : Fin (n + 1) → N.ulift.{u,0,v}.Domain) =
        ULift.up a :> (f.comp e) ∘ b := by
      funext i
      cases i using Fin.cases <;> rfl
    exact hb ▸ h

end WeakModel
end ZFVP.Infinitary
