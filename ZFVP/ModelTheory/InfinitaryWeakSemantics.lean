import ZFVP.ModelTheory.InfinitarySyntax
import ZFVP.ModelTheory.InfinitaryLanguageMap

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula
variable {L : Language} {M : Type*} [Structure L M]

/-- Weak semantics permits an arbitrary quantifier on subsets of the domain.
Standard semantics is the special case of uncountability. -/
def WeakEval (Q : Set M → Prop) : {n : ℕ} → Formula L n → (Fin n → M) → Prop
  | _, .fo φ, b => φ.Evalb b
  | _, .neg φ, b => ¬WeakEval Q φ b
  | _, .conj φ, b => ∀ i, WeakEval Q (φ i) b
  | _, .exs φ, b => ∃ x, WeakEval Q φ (x :> b)
  | _, .q φ, b => Q {x | WeakEval Q φ (x :> b)}

theorem weakEval_standard {n} (φ : Formula L n) (b : Fin n → M) :
    WeakEval (fun A : Set M ↦ ¬A.Countable) φ b ↔ Eval φ b := by
  induction φ with
  | fo φ => rfl
  | neg φ ih => exact not_congr (ih b)
  | conj φ ih => exact forall_congr' fun i ↦ ih i b
  | exs φ ih => exact exists_congr fun x ↦ ih (x :> b)
  | q φ ih =>
    have he : {x : M | WeakEval (fun A : Set M ↦ ¬A.Countable) φ (x :> b)} =
        {x : M | Eval φ (x :> b)} := by ext x; exact ih (x :> b)
    change (¬Set.Countable _) ↔ ¬Set.Countable _
    rw [he]

end Formula

namespace Formula
theorem weakEval_lMap {L K : Language} (η : L →ᵥ K) {M : Type*}
    (s : Structure K M) (Q : Set M → Prop) {n} (φ : Formula L n) (b : Fin n → M) :
    @WeakEval K M s Q n (φ.lMap η) b ↔ @WeakEval L M (s.lMap η) Q n φ b := by
  induction φ with
  | fo φ => exact Semiformula.eval_lMap
  | neg φ ih => exact not_congr (ih b)
  | conj φ ih => exact forall_congr' fun i ↦ ih i b
  | exs φ ih => exact exists_congr fun x ↦ ih (x :> b)
  | q φ ih =>
    have he : {x : M | @WeakEval K M s Q _ (φ.lMap η) (x :> b)} =
        {x : M | @WeakEval L M (s.lMap η) Q _ φ (x :> b)} := by
      ext x
      exact ih (x :> b)
    change Q _ ↔ Q _
    rw [he]
end Formula
end ZFVP.Infinitary
