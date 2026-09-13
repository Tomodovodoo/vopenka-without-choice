import ZFVP.SetTheory.BoundedCodingPrimitives

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedRangeFormula : SetTheorySemisentence 2 :=
  “R f. (∀ y ∈ R, ∃ p ∈ f, ∃ d ∈ p, ∃ x ∈ d, !boundedKpairFormula p x y) ∧
    ∀ p ∈ f, ∀ d ∈ p, ∀ x ∈ d, ∀ e ∈ p, ∀ y ∈ e, !boundedKpairFormula p x y → y ∈ R”

theorem boundedRangeFormula_bounded : IsBoundedSetFormula boundedRangeFormula :=
  .and (.all (.bvar 0) (.exs (.bvar 2) (.exs (.bvar 0) (.exs (.bvar 0)
    (boundedKpairFormula_bounded.subst _)))))
    (.all (.bvar 1) (.all (.bvar 0) (.all (.bvar 0) (.all (.bvar 2) (.all (.bvar 0)
      (.or (boundedKpairFormula_bounded.subst _).neg (.rel _ _)))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedRangeFormula_defined : ℒₛₑₜ-function₁[V] range via boundedRangeFormula :=
  ⟨fun v ↦ by
    change boundedRangeFormula.Evalb v ↔ v 0 = range (v 1)
    simp [boundedRangeFormula]
    constructor
    · rintro ⟨hf, hb⟩
      apply mem_ext
      intro y
      constructor
      · intro hy
        obtain ⟨d, x, hp, _, _⟩ := hf y hy
        exact mem_range_iff.mpr ⟨x, hp⟩
      · intro hy
        obtain ⟨x, hp⟩ := mem_range_iff.mp hy
        exact hb ⟨x, y⟩ₖ hp (doubleton x y) (by simp [kpair, pair_eq_doubleton])
          x (by simp) (doubleton x y) (by simp [kpair, pair_eq_doubleton]) y (by simp) rfl
    · intro h
      rw [h]
      constructor
      · intro y hy
        obtain ⟨x, hp⟩ := mem_range_iff.mp hy
        exact ⟨doubleton x y, x, hp, by simp [kpair, pair_eq_doubleton], by simp⟩
      · intro p hp d _ x _ e _ y _ hxy
        exact mem_range_iff.mpr ⟨x, hxy ▸ hp⟩⟩

end ZFVP
