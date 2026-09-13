import ZFVP.ModelTheory.InfinitaryRewritingLaws

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula

/-- Apply a language homomorphism to every first-order atom. -/
def lMap {L K : Language} (η : L →ᵥ K) : {n : ℕ} → Formula L n → Formula K n
  | _, .fo φ => .fo (φ.lMap η)
  | _, .neg φ => .neg (lMap η φ)
  | _, .conj φ => .conj fun i ↦ lMap η (φ i)
  | _, .exs φ => .exs (lMap η φ)
  | _, .q φ => .q (lMap η φ)

theorem eval_lMap {L K : Language} (η : L →ᵥ K)
    {M : Type*} (S : Structure K M) {n} (φ : Formula L n) (b : Fin n → M) :
    @Formula.Eval K M S n (lMap η φ) b ↔
      @Formula.Eval L M (S.lMap η) n φ b := by
  induction φ with
  | fo φ => exact Semiformula.eval_lMap
  | neg φ ih => exact not_congr (ih b)
  | conj φ ih => exact forall_congr' fun i ↦ ih i b
  | exs φ ih => exact exists_congr fun x ↦ ih (x :> b)
  | q φ ih =>
      have he : {x : M | @Formula.Eval K M S _ (lMap η φ) (x :> b)} =
          {x : M | @Formula.Eval L M (S.lMap η) _ φ (x :> b)} := by
        ext x
        exact ih (x :> b)
      change (¬ Set.Countable _) ↔ ¬ Set.Countable _
      rw [he]

end Formula
end ZFVP.Infinitary
