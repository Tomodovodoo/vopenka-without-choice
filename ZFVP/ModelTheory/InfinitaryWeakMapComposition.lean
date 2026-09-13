import ZFVP.ModelTheory.InfinitaryAdequateLimits

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v w z
namespace WeakElementaryMap
variable {L : Language.{u}} [L.Eq] {T : Set (TaggedFormula L)}
  {M : WeakModel.{u,v} L} {N : WeakModel.{u,w} L} {P : WeakModel.{u,z} L}

def id (M : WeakModel.{u,v} L) : WeakElementaryMap T M M where
  toFun := fun x ↦ x
  injective := Function.injective_id
  func := fun _ _ ↦ rfl
  rel := fun _ _ ↦ Iff.rfl
  elementary := fun _ _ _ ↦ Iff.rfl

def comp (f : WeakElementaryMap T N P) (e : WeakElementaryMap T M N) :
    WeakElementaryMap T M P where
  toFun := f ∘ e
  injective := f.injective.comp e.injective
  func := fun g b ↦ by
    change f (e (Structure.func g b)) = _
    rw [e.func, f.func]
    rfl
  rel := fun r b ↦ (f.rel r (e ∘ b)).trans (e.rel r b)
  elementary := fun φ hφ b ↦ (f.elementary φ hφ (e ∘ b)).trans (e.elementary φ hφ b)

theorem id_freezes (M : WeakModel.{u,v} L) : (id (T := T) M).FreezesSmallFibers := by
  intro n φ hφ b hs
  exact (Set.image_id _).symm

theorem comp_freezes [L.Encodable] {S : Set (TaggedFormula L)}
    (e : WeakElementaryMap (FragmentClosure.carrier S) M N)
    (f : WeakElementaryMap (FragmentClosure.carrier S) N P)
    (he : e.FreezesSmallFibers) (hf : f.FreezesSmallFibers) :
    (f.comp e).FreezesSmallFibers := by
  intro n φ hφ b hs
  have hn : ¬N.Q {x | Formula.WeakEval N.Q φ (x :> e ∘ b)} := by
    exact fun h ↦ hs ((e.elementary (.q φ) (FragmentClosure.q_closed hφ) b).mp h)
  change {y | Formula.WeakEval P.Q φ (y :> f ∘ (e ∘ b))} = _
  rw [hf φ hφ (e ∘ b) hn, he φ hφ b hs, Set.image_image]
  rfl

end WeakElementaryMap
end ZFVP.Infinitary
