import ZFVP.SetTheory.BoundedCodingPrimitives

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedProductFormula : SetTheorySemisentence 3 :=
  “B A C. (∀ p ∈ B, ∃ x ∈ A, ∃ y ∈ C, !boundedKpairFormula p x y) ∧
    ∀ x ∈ A, ∀ y ∈ C, !boundedPairMemberFormula B x y”

theorem boundedProductFormula_bounded : IsBoundedSetFormula boundedProductFormula :=
  .and (.all (.bvar 0) (.exs (.bvar 2) (.exs (.bvar 4) (boundedKpairFormula_bounded.subst _))))
    (.all (.bvar 1) (.all (.bvar 3) (boundedPairMemberFormula_bounded.subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem eval_boundedProductFormula (B A C : V) :
    boundedProductFormula.Evalb ![B, A, C] ↔ B = A ×ˢ C := by
  have he : boundedProductFormula.Evalb ![B, A, C] ↔
      (∀ p ∈ B, ∃ x ∈ A, ∃ y ∈ C, p = ⟨x, y⟩ₖ) ∧
      ∀ x ∈ A, ∀ y ∈ C, ⟨x, y⟩ₖ ∈ B := by simp [boundedProductFormula]
  rw [he]
  constructor
  · rintro ⟨hf, hb⟩
    apply mem_ext
    intro p
    constructor
    · intro hp
      exact mem_prod_iff.mpr (hf p hp)
    · intro hp
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp hp
      exact hb x hx y hy
  · rintro rfl
    exact ⟨fun p hp ↦ mem_prod_iff.mp hp,
      fun x hx y hy ↦ mem_prod_iff.mpr ⟨x, hx, y, hy, rfl⟩⟩

end ZFVP
