import ZFVP.SetTheory.BoundedCodingPrimitives

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedSUnionFormula : SetTheorySemisentence 2 :=
  “U A. (∀ x ∈ U, ∃ y ∈ A, x ∈ y) ∧ ∀ y ∈ A, ∀ x ∈ y, x ∈ U”

def boundedSInterFormula : SetTheorySemisentence 2 :=
  “I A. (∀ x ∈ I, (∃ u ∈ A, ⊤) ∧ ∀ u ∈ A, x ∈ u) ∧
    ∀ u ∈ A, ∀ x ∈ u, (∀ v ∈ A, x ∈ v) → x ∈ I”

theorem boundedSUnionFormula_bounded : IsBoundedSetFormula boundedSUnionFormula :=
  .and (.all (.bvar 0) (.exs (.bvar 2) (.rel _ _)))
    (.all (.bvar 1) (.all (.bvar 0) (.rel _ _)))

theorem boundedSInterFormula_bounded : IsBoundedSetFormula boundedSInterFormula :=
  .and (.all (.bvar 0) (.and (.exs (.bvar 2) .verum) (.all (.bvar 2) (.rel _ _))))
    (.all (.bvar 1) (.all (.bvar 0)
      (.or (IsBoundedSetFormula.all (.bvar 3) (.rel _ _)).neg (.rel _ _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedSUnionFormula_defined : ℒₛₑₜ-function₁[V] sUnion via boundedSUnionFormula :=
  ⟨fun v ↦ by
    change boundedSUnionFormula.Evalb v ↔ v 0 = ⋃ˢ v 1
    simp [boundedSUnionFormula]
    constructor
    · rintro ⟨hf, hb⟩
      apply mem_ext
      intro x
      constructor
      · intro hx
        exact mem_sUnion_iff.mpr (hf x hx)
      · intro hx
        obtain ⟨y, hy, hx⟩ := mem_sUnion_iff.mp hx
        exact hb y hy x hx
    · rintro h
      rw [h]
      exact ⟨fun x hx ↦ mem_sUnion_iff.mp hx,
        fun y hy x hx ↦ mem_sUnion_iff.mpr ⟨y, hy, hx⟩⟩⟩

instance boundedSInterFormula_defined : ℒₛₑₜ-function₁[V] sInter via boundedSInterFormula :=
  ⟨fun v ↦ by
    change boundedSInterFormula.Evalb v ↔ v 0 = ⋂ˢ v 1
    simp [boundedSInterFormula]
    constructor
    · rintro ⟨hf, hb⟩
      apply mem_ext
      intro x
      constructor
      · intro hx
        obtain ⟨hne, hall⟩ := hf x hx
        exact mem_sInter_iff.mpr ⟨isNonempty_def.mpr hne, hall⟩
      · intro hx
        obtain ⟨hne, hall⟩ := mem_sInter_iff.mp hx
        obtain ⟨u, hu⟩ := isNonempty_def.mp hne
        exact hb u hu x (hall u hu) hall
    · intro h
      rw [h]
      constructor
      · intro x hx
        obtain ⟨hne, hall⟩ := mem_sInter_iff.mp hx
        exact ⟨isNonempty_def.mp hne, hall⟩
      · intro u hu x _ hall
        exact mem_sInter_iff.mpr ⟨isNonempty_def.mpr ⟨u, hu⟩, hall⟩⟩

end ZFVP
