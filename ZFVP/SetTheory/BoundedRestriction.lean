import ZFVP.SetTheory.BoundedCodingPrimitives

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedRestrictFormula : SetTheorySemisentence 3 :=
  “R f A. (∀ p ∈ R, p ∈ f ∧ ∃ x ∈ A, ∃ d ∈ p, ∃ y ∈ d, !boundedKpairFormula p x y) ∧
    ∀ p ∈ f, ∀ x ∈ A, ∀ d ∈ p, ∀ y ∈ d, !boundedKpairFormula p x y → p ∈ R”

theorem boundedRestrictFormula_bounded : IsBoundedSetFormula boundedRestrictFormula :=
  .and (.all (.bvar 0) (.and (.rel _ _) (.exs (.bvar 3) (.exs (.bvar 1) (.exs (.bvar 0)
    (boundedKpairFormula_bounded.subst _))))))
    (.all (.bvar 1) (.all (.bvar 3) (.all (.bvar 1) (.all (.bvar 0)
      (.or (boundedKpairFormula_bounded.subst _).neg (.rel _ _))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedRestrictFormula_defined : ℒₛₑₜ-function₂[V] restrict via boundedRestrictFormula :=
  ⟨fun v ↦ by
    change boundedRestrictFormula.Evalb v ↔ v 0 = (v 1) ↾ (v 2)
    simp [boundedRestrictFormula]
    constructor
    · rintro ⟨hf, hb⟩
      apply mem_ext
      intro p
      constructor
      · intro hp
        obtain ⟨hpf, x, hx, d, _, y, _, hxy⟩ := hf p hp
        exact mem_restrict_iff.mpr ⟨hpf, x, hx, y, hxy⟩
      · intro hp
        obtain ⟨hpf, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
        exact hb ⟨x, y⟩ₖ hpf x hx (doubleton x y) (by simp [kpair, pair_eq_doubleton]) y (by simp) rfl
    · intro h
      rw [h]
      constructor
      · intro p hp
        obtain ⟨hpf, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
        exact ⟨hpf, x, hx, doubleton x y, by simp [kpair, pair_eq_doubleton], y, by simp, rfl⟩
      · intro p hp x hx d _ y _ hxy
        exact mem_restrict_iff.mpr ⟨hp, x, hx, y, hxy⟩⟩

end ZFVP
