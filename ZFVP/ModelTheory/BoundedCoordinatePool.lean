import ZFVP.ModelTheory.SparseCoordinatePoolRecovery
import ZFVP.SetTheory.BoundedValue

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedCoordinatePoolFormula : SetTheorySemisentence 3 :=
  “W S a. (∀ τ ∈ W, ∃ p ∈ S, !boundedValueFormula τ p a) ∧
    ∀ p ∈ S, ∃ τ ∈ W, !boundedValueFormula τ p a”

theorem boundedCoordinatePoolFormula_bounded : IsBoundedSetFormula boundedCoordinatePoolFormula := by
  repeat' first
    | exact boundedValueFormula_bounded.subst _
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedCoordinatePoolFormula {W S a : V} :
    boundedCoordinatePoolFormula.Evalb ![W, S, a] ↔ W = sparseCoordinatePool S a := by
  simp only [boundedCoordinatePoolFormula]
  simp
  constructor
  · rintro ⟨hl, hr⟩
    apply mem_ext
    intro τ
    rw [mem_sparseCoordinatePool_iff]
    constructor
    · exact hl τ
    · rintro ⟨p, hp, rfl⟩
      exact hr p hp
  · rintro rfl
    constructor
    · intro τ hτ
      exact mem_sparseCoordinatePool_iff.mp hτ
    · intro p hp
      exact mem_sparseCoordinatePool_iff.mpr ⟨p, hp, rfl⟩

end ZFVP

