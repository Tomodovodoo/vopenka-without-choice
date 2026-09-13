import ZFVP.ModelTheory.InfinitaryAdequateLimits
import Mathlib.Tactic.FinCases

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v w
namespace WeakModel
variable {L : Language.{u}} [L.Eq] (M : WeakModel.{u,v} L)

/-- Raise the domain universe, transporting the structure and the quantifier
along the canonical bijection. -/
def ulift : WeakModel.{u, max v w} L where
  Domain := ULift.{w} M.Domain
  str := Structure.ofEquiv (Equiv.ulift.symm : M.Domain ≃ ULift.{w} M.Domain)
  eq := ⟨fun a b ↦ by
    refine (Structure.operator_val_ofEquiv_iff
      (Equiv.ulift.symm : M.Domain ≃ ULift.{w} M.Domain)).trans ?_
    have he : (Equiv.ulift.symm : M.Domain ≃ ULift.{w} M.Domain).symm ∘ ![a, b] =
        ![a.down, b.down] := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    exact (Structure.Eq.eq (L := L) a.down b.down).trans ULift.down_injective.eq_iff⟩
  nonempty := inferInstance
  countable := inferInstance
  Q := fun A ↦ M.Q (ULift.up ⁻¹' A)
  mono := fun _ _ h ↦ M.mono (Set.preimage_mono h)

theorem ulift_down_cons {n} (x : ULift.{w} M.Domain) (b : Fin n → ULift.{w} M.Domain) :
    ULift.down ∘ (x :> b) = x.down :> (ULift.down ∘ b) := by
  funext i
  cases i using Fin.cases <;> rfl

theorem ulift_up_cons {n} (x : M.Domain) (b : Fin n → M.Domain) :
    ULift.up ∘ (x :> b) = (ULift.up x : ULift.{w} M.Domain) :> (ULift.up ∘ b) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- Transport preserves every infinitary formula, without a fragment restriction. -/
theorem ulift_weakEval {n} (φ : Formula L n) (b : Fin n → M.ulift.{u,v,w}.Domain) :
    Formula.WeakEval M.ulift.Q φ b ↔ Formula.WeakEval M.Q φ (ULift.down ∘ b) := by
  induction φ with
  | fo φ =>
    have h := Structure.eval_ofEquiv_iff (Θ := (Equiv.ulift.symm : M.Domain ≃ ULift.{w} M.Domain))
      (b := b) (f := Empty.elim) (φ := φ)
    have he : (Equiv.ulift.symm : M.Domain ≃ ULift.{w} M.Domain).symm ∘
        (Empty.elim : Empty → ULift.{w} M.Domain) = Empty.elim := Subsingleton.elim _ _
    rw [he] at h
    exact h
  | neg φ ih => exact not_congr (ih b)
  | conj f ih => exact forall_congr' fun i ↦ ih i b
  | exs φ ih =>
    change (∃ x : ULift.{w} M.Domain, Formula.WeakEval M.ulift.Q φ (x :> b)) ↔ _
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.down, (M.ulift_down_cons x b) ▸ (ih (x :> b)).mp hx⟩
    · rintro ⟨x, hx⟩
      refine ⟨ULift.up x, (ih (ULift.up x :> b)).mpr ?_⟩
      exact (M.ulift_down_cons (ULift.up x) b).symm ▸ hx
  | q φ ih =>
    change M.Q (ULift.up ⁻¹' {x : ULift.{w} M.Domain | Formula.WeakEval M.ulift.Q φ (x :> b)}) ↔ _
    have he : ULift.up ⁻¹' {x : ULift.{w} M.Domain | Formula.WeakEval M.ulift.Q φ (x :> b)} =
        {x : M.Domain | Formula.WeakEval M.Q φ (x :> ULift.down ∘ b)} := by
      ext x
      change Formula.WeakEval M.ulift.Q φ (ULift.up x :> b) ↔ _
      exact (ih (ULift.up x :> b)).trans
        (Iff.of_eq (congrArg (Formula.WeakEval M.Q φ) (M.ulift_down_cons (ULift.up x) b)))
    exact Iff.of_eq (congrArg M.Q he)

theorem ulift_weakEval_up {n} (φ : Formula L n) (b : Fin n → M.Domain) :
    Formula.WeakEval M.ulift.{u,v,w}.Q φ (ULift.up ∘ b) ↔ Formula.WeakEval M.Q φ b := by
  have he : ULift.down ∘ (ULift.up ∘ b : Fin n → ULift.{w} M.Domain) = b := rfl
  exact (M.ulift_weakEval φ (ULift.up ∘ b)).trans (Iff.of_eq (congrArg (Formula.WeakEval M.Q φ) he))

def uliftEmbedding (T : Set (TaggedFormula L)) : WeakElementaryMap T M M.ulift.{u,v,w} where
  toFun := ULift.up
  injective := ULift.up_injective
  func := fun _ _ ↦ rfl
  rel := fun _ _ ↦ Iff.rfl
  elementary := fun φ _ b ↦ M.ulift_weakEval_up φ b

theorem uliftEmbedding_bijective (T : Set (TaggedFormula L)) :
    Function.Bijective (M.uliftEmbedding.{u,v,w} T) :=
  ⟨ULift.up_injective, fun x ↦ ⟨x.down, ULift.up_down x⟩⟩

/-- The lift preserves every fiber exactly, independently of its Q status. -/
theorem ulift_fiber_eq_image {n} (φ : Formula L (n + 1)) (b : Fin n → M.Domain) :
    {y : M.ulift.{u,v,w}.Domain | Formula.WeakEval M.ulift.Q φ (y :> ULift.up ∘ b)} =
      ULift.up '' {x : M.Domain | Formula.WeakEval M.Q φ (x :> b)} := by
  ext y
  constructor
  · intro hy
    refine ⟨y.down, ?_, ULift.up_down y⟩
    have h := (M.ulift_weakEval φ (y :> ULift.up ∘ b)).mp hy
    have he : ULift.down ∘ (y :> ULift.up ∘ b) = y.down :> b := by
      funext i
      cases i using Fin.cases <;> rfl
    exact (congrArg (Formula.WeakEval M.Q φ) he).mp h
  · rintro ⟨x, hx, rfl⟩
    have h := (M.ulift_weakEval_up φ (x :> b)).mpr hx
    exact (congrArg (Formula.WeakEval M.ulift.Q φ) (M.ulift_up_cons x b)).mp h

theorem uliftEmbedding_freezes (T : Set (TaggedFormula L)) :
    (M.uliftEmbedding.{u,v,w} T).FreezesSmallFibers := by
  intro n φ _ b _
  exact M.ulift_fiber_eq_image φ b

theorem ulift_adequate [L.Encodable] {S : Set (TaggedFormula L)} (hM : M.Adequate S) :
    M.ulift.{u,v,w}.Adequate S := hM.of_elementary (M.uliftEmbedding _)

end WeakModel
end ZFVP.Infinitary
