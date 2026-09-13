import ZFVP.SetTheory.BoundedCodingPrimitives

/-! A bounded relational definition of binary union. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedUnionFormula : SetTheorySemisentence 3 :=
  “B X Y. (∀ z ∈ B, z ∈ X ∨ z ∈ Y) ∧ !isSubsetOf X B ∧ !isSubsetOf Y B”

theorem boundedUnionFormula_bounded : IsBoundedSetFormula boundedUnionFormula :=
  .and (.all (.bvar 0) (.or (.rel _ _) (.rel _ _)))
    (.and (isSubsetOf_bounded.subst _) (isSubsetOf_bounded.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedUnionFormula_defined : ℒₛₑₜ-function₂[V] (fun X Y : V ↦ X ∪ Y) via boundedUnionFormula :=
  ⟨fun v ↦ by
    change boundedUnionFormula.Evalb v ↔ v 0 = v 1 ∪ v 2
    simp [boundedUnionFormula]
    constructor
    · rintro ⟨hB, hX, hY⟩
      apply mem_ext
      intro z
      rw [mem_union_iff]
      exact ⟨hB z, fun h ↦ h.elim (hX z) (hY z)⟩
    · intro he
      rw [he]
      exact ⟨fun z ↦ mem_union_iff.mp, fun z hz ↦ mem_union_iff.mpr (Or.inl hz),
        fun z hz ↦ mem_union_iff.mpr (Or.inr hz)⟩⟩

end ZFVP
