import ZFVP.ModelTheory.InfinitaryAdequateLimits
import Mathlib.Tactic.FinCases

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v w
namespace WeakModel
variable {L : Language.{u}} [L.Eq] (M : WeakModel.{u,v} L)
  {A : Type w} (e : M.Domain ≃ A)

/-- Transport the entire weak model along an actual bijection. -/
noncomputable def relabel : WeakModel.{u,w} L where
  Domain := A
  str := Structure.ofEquiv e
  eq := by
    let : Structure L A := Structure.ofEquiv e
    refine ⟨fun a b ↦ ?_⟩
    refine (Structure.operator_val_ofEquiv_iff e).trans ?_
    have he : e.symm ∘ ![a, b] = ![e.symm a, e.symm b] := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    exact (Structure.Eq.eq (L := L) (e.symm a) (e.symm b)).trans e.symm.injective.eq_iff
  nonempty := ⟨e (Classical.choice M.nonempty)⟩
  countable := e.symm.injective.countable
  Q := fun B ↦ M.Q (e ⁻¹' B)
  mono := fun _ _ h ↦ M.mono (Set.preimage_mono h)

theorem relabel_symm_cons {n} (x : A) (b : Fin n → A) :
    e.symm ∘ (x :> b) = e.symm x :> e.symm ∘ b := by
  funext i
  cases i using Fin.cases <;> rfl

theorem relabel_weakEval {n} (φ : Formula L n) (b : Fin n → A) :
    Formula.WeakEval (M.relabel e).Q φ b ↔ Formula.WeakEval M.Q φ (e.symm ∘ b) := by
  induction φ with
  | fo φ =>
    have h := Structure.eval_ofEquiv_iff (Θ := e) (b := b) (f := Empty.elim) (φ := φ)
    have he : e.symm ∘ (Empty.elim : Empty → A) = Empty.elim := Subsingleton.elim _ _
    rw [he] at h
    exact h
  | neg φ ih => exact not_congr (ih b)
  | conj f ih => exact forall_congr' fun i ↦ ih i b
  | exs φ ih =>
    change (∃ x : A, Formula.WeakEval (M.relabel e).Q φ (x :> b)) ↔ _
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨e.symm x, (M.relabel_symm_cons e x b) ▸ (ih (x :> b)).mp hx⟩
    · rintro ⟨x, hx⟩
      refine ⟨e x, (ih (e x :> b)).mpr ?_⟩
      rw [M.relabel_symm_cons, e.symm_apply_apply]
      exact hx
  | q φ ih =>
    change M.Q (e ⁻¹' {x : A | Formula.WeakEval (M.relabel e).Q φ (x :> b)}) ↔ _
    have he : e ⁻¹' {x : A | Formula.WeakEval (M.relabel e).Q φ (x :> b)} =
        {x : M.Domain | Formula.WeakEval M.Q φ (x :> e.symm ∘ b)} := by
      ext x
      change Formula.WeakEval (M.relabel e).Q φ (e x :> b) ↔
        Formula.WeakEval M.Q φ (x :> e.symm ∘ b)
      exact (ih (e x :> b)).trans (Iff.of_eq (congrArg (Formula.WeakEval M.Q φ)
        ((M.relabel_symm_cons e (e x) b).trans (by rw [e.symm_apply_apply]))))
    exact Iff.of_eq (congrArg M.Q he)

theorem relabel_weakEval_apply {n} (φ : Formula L n) (b : Fin n → M.Domain) :
    Formula.WeakEval (M.relabel e).Q φ (e ∘ b) ↔ Formula.WeakEval M.Q φ b := by
  have he : e.symm ∘ (e ∘ b) = b := funext fun i ↦ e.symm_apply_apply (b i)
  exact (M.relabel_weakEval e φ (e ∘ b)).trans (Iff.of_eq (congrArg (Formula.WeakEval M.Q φ) he))

noncomputable def relabelEmbedding (T : Set (TaggedFormula L)) :
    WeakElementaryMap T M (M.relabel e) where
  toFun := e
  injective := e.injective
  func := fun f b ↦ by
    change e (Structure.func f b) = e (Structure.func f (e.symm ∘ (e ∘ b)))
    congr 2
    funext i
    exact (e.symm_apply_apply (b i)).symm
  rel := fun r b ↦ by
    change Structure.rel r (e.symm ∘ (e ∘ b)) ↔ Structure.rel r b
    have he : e.symm ∘ (e ∘ b) = b := funext fun i ↦ e.symm_apply_apply (b i)
    rw [he]
  elementary := fun φ _ b ↦ M.relabel_weakEval_apply e φ b

theorem relabel_fiber_eq_image {n} (φ : Formula L (n + 1)) (b : Fin n → M.Domain) :
    {y : A | Formula.WeakEval (M.relabel e).Q φ (y :> e ∘ b)} =
      e '' {x | Formula.WeakEval M.Q φ (x :> b)} := by
  ext y
  have he : e.symm ∘ (y :> e ∘ b) = e.symm y :> b := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact e.symm_apply_apply (b i)
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change Formula.WeakEval M.Q φ (e.symm y :> b)
    exact he ▸ (M.relabel_weakEval e φ (y :> e ∘ b)).mp hy
  · rintro ⟨x, hx, rfl⟩
    change Formula.WeakEval M.Q φ (x :> b) at hx
    apply (M.relabel_weakEval e φ (e x :> e ∘ b)).mpr
    simpa only [he, e.symm_apply_apply] using hx

theorem relabelEmbedding_freezes (T : Set (TaggedFormula L)) :
    (M.relabelEmbedding e T).FreezesSmallFibers := by
  intro n φ hφ b hs
  exact M.relabel_fiber_eq_image e φ b

end WeakModel
end ZFVP.Infinitary
