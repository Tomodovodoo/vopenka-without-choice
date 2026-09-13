import ZFVP.SetTheory.LeastOrdinalChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def leastOrdinalOrZeroFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  f“y x. (!IsOrdinal.dfn y ∧ !φ x y ∧ ∀ z, !IsOrdinal.dfn z → !φ x z → y ⊆ z) ∨
    ((¬∃ z, !IsOrdinal.dfn z ∧ !φ x z) ∧ !isEmpty y)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_leastOrdinalOrZeroFormula (φ : SetTheorySemisentence 2)
    (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (ht : ∀ x y, φ.Evalb ![x, y] ↔ R x y) (y x : V) :
    (leastOrdinalOrZeroFormula φ).Evalb ![y, x] ↔ y = leastOrdinalOrZero R hR x := by
  rw [leastOrdinalOrZero_eq_iff]
  simp [leastOrdinalOrZeroFormula, IsLeastOrdinal, ht]
  exact or_congr Iff.rfl (and_congr (forall_congr' (fun z ↦ by tauto)) Iff.rfl)

end ZFVP
