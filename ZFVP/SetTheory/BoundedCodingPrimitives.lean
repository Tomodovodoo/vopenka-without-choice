import ZFVP.SetTheory.LevySubstitution
import Foundation.FirstOrder.SetTheory.Function

/-! Bounded formulas for the elementary constructors used in syntax codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedEmptyFormula : SetTheorySemisentence 1 := “A. ∀ x ∈ A, ⊥”

def boundedSingletonFormula : SetTheorySemisentence 2 :=
  “p x. x ∈ p ∧ ∀ z ∈ p, z = x”

def boundedDoubletonFormula : SetTheorySemisentence 3 :=
  “p x y. x ∈ p ∧ y ∈ p ∧ ∀ z ∈ p, z = x ∨ z = y”

def boundedKpairFormula : SetTheorySemisentence 3 :=
  “p x y. ∃ s ∈ p, !boundedSingletonFormula s x ∧
    ∃ d ∈ p, !boundedDoubletonFormula d x y ∧ !boundedDoubletonFormula p s d”

def boundedSuccFormula : SetTheorySemisentence 2 :=
  “y x. x ∈ y ∧ (∀ z ∈ x, z ∈ y) ∧ ∀ z ∈ y, z = x ∨ z ∈ x”

def boundedPairMemberFormula : SetTheorySemisentence 3 :=
  “f x y. ∃ p ∈ f, !boundedKpairFormula p x y”

def boundedFunctionFormula : SetTheorySemisentence 3 :=
  “f A B. (∀ p ∈ f, ∃ x ∈ A, ∃ y ∈ B, !boundedKpairFormula p x y) ∧
    ∀ x ∈ A, ∃ y ∈ B, !boundedPairMemberFormula f x y ∧
      ∀ z ∈ B, !boundedPairMemberFormula f x z → z = y”

theorem boundedEmptyFormula_bounded : IsBoundedSetFormula boundedEmptyFormula := by
  exact .all (.bvar 0) .falsum

theorem boundedSingletonFormula_bounded : IsBoundedSetFormula boundedSingletonFormula := by
  exact .and (.rel _ _) (.all (.bvar 0) (.rel _ _))

theorem boundedDoubletonFormula_bounded : IsBoundedSetFormula boundedDoubletonFormula := by
  exact .and (.rel _ _) (.and (.rel _ _) (.all (.bvar 0) (.or (.rel _ _) (.rel _ _))))

theorem boundedKpairFormula_bounded : IsBoundedSetFormula boundedKpairFormula := by
  exact .exs (.bvar 0) (.and
    (boundedSingletonFormula_bounded.subst ![.bvar 0, .bvar 2])
    (.exs (.bvar 1) (.and
      (boundedDoubletonFormula_bounded.subst ![.bvar 0, .bvar 3, .bvar 4])
      (boundedDoubletonFormula_bounded.subst ![.bvar 2, .bvar 1, .bvar 0]))))

theorem boundedSuccFormula_bounded : IsBoundedSetFormula boundedSuccFormula := by
  exact .and (.rel _ _) (.and (.all (.bvar 1) (.rel _ _)) (.all (.bvar 0) (.or (.rel _ _) (.rel _ _))))

theorem isSubsetOf_bounded : IsBoundedSetFormula isSubsetOf := by
  exact .all (.bvar 0) (.rel _ _)

theorem isTransitiveFormula_bounded : IsBoundedSetFormula IsTransitive.dfn := by
  exact .all (.bvar 0) (isSubsetOf_bounded.subst ![.bvar 0, .bvar 1])

theorem isOrdinalFormula_bounded : IsBoundedSetFormula IsOrdinal.dfn := by
  exact .and (isTransitiveFormula_bounded.subst ![.bvar 0])
    (.all (.bvar 0) (.all (.bvar 1) (.or (.rel _ _) (.or (.rel _ _) (.rel _ _)))))

theorem boundedPairMemberFormula_bounded : IsBoundedSetFormula boundedPairMemberFormula := by
  exact .exs (.bvar 0) (boundedKpairFormula_bounded.subst ![.bvar 0, .bvar 2, .bvar 3])

theorem boundedFunctionFormula_bounded : IsBoundedSetFormula boundedFunctionFormula := by
  exact .and
    (.all (.bvar 0) (.exs (.bvar 2) (.exs (.bvar 4)
      (boundedKpairFormula_bounded.subst ![.bvar 2, .bvar 1, .bvar 0]))))
    (.all (.bvar 1) (.exs (.bvar 3) (.and
      (boundedPairMemberFormula_bounded.subst ![.bvar 2, .bvar 1, .bvar 0])
      (.all (.bvar 4) (.or
        (boundedPairMemberFormula_bounded.subst ![.bvar 3, .bvar 2, .bvar 0]).neg (.rel _ _))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedEmptyFormula_defined : ℒₛₑₜ-function₀[V] (∅ : V) via boundedEmptyFormula :=
  ⟨fun v ↦ by
    change boundedEmptyFormula.Evalb v ↔ v 0 = ∅
    rw [← isEmpty_iff_eq_empty]
    simp [boundedEmptyFormula, LO.FirstOrder.SetTheory.IsEmpty]⟩

instance boundedSingletonFormula_defined :
    ℒₛₑₜ-function₁[V] Singleton.singleton via boundedSingletonFormula :=
  ⟨fun v ↦ by
    change boundedSingletonFormula.Evalb v ↔ v 0 = {v 1}
    simp only [boundedSingletonFormula, mem_ext_iff]
    simp
    constructor
    · rintro ⟨hx, h⟩ z
      exact ⟨fun hz ↦ h z hz, fun hz ↦ hz ▸ hx⟩
    · intro h
      exact ⟨(h _).mpr rfl, fun z hz ↦ (h z).mp hz⟩⟩

instance boundedDoubletonFormula_defined : ℒₛₑₜ-function₂[V] doubleton via boundedDoubletonFormula :=
  ⟨fun v ↦ by
    change boundedDoubletonFormula.Evalb v ↔ v 0 = doubleton (v 1) (v 2)
    simp only [boundedDoubletonFormula, mem_ext_iff]
    simp
    constructor
    · rintro ⟨hx, hy, h⟩ z
      exact ⟨fun hz ↦ h z hz, fun hz ↦ hz.elim (fun hz ↦ hz ▸ hx) (fun hz ↦ hz ▸ hy)⟩
    · intro h
      exact ⟨(h _).mpr (Or.inl rfl), (h _).mpr (Or.inr rfl), fun z hz ↦ (h z).mp hz⟩⟩

instance boundedKpairFormula_defined : ℒₛₑₜ-function₂[V] kpair via boundedKpairFormula :=
  ⟨fun v ↦ by
    simp [boundedKpairFormula, kpair, pair_eq_doubleton]
    constructor
    · exact fun h ↦ h.2.2
    · intro h
      rw [h]
      simp⟩

instance boundedSuccFormula_defined : ℒₛₑₜ-function₁[V] succ via boundedSuccFormula :=
  ⟨fun v ↦ by
    change boundedSuccFormula.Evalb v ↔ v 0 = succ (v 1)
    simp only [boundedSuccFormula, mem_ext_iff]
    simp [mem_succ_iff]
    constructor
    · rintro ⟨hx, hsub, h⟩ z
      exact ⟨fun hz ↦ h z hz, fun hz ↦ hz.elim (fun hz ↦ hz ▸ hx) (hsub z)⟩
    · intro h
      exact ⟨(h _).mpr (Or.inl rfl), fun z hz ↦ (h z).mpr (Or.inr hz), fun z hz ↦ (h z).mp hz⟩⟩

instance boundedPairMemberFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun f x y ↦ ⟨x, y⟩ₖ ∈ f) via boundedPairMemberFormula :=
  ⟨fun v ↦ by simp [boundedPairMemberFormula]⟩

instance boundedFunctionFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun f A B ↦ f ∈ B ^ A) via boundedFunctionFormula :=
  ⟨fun v ↦ by
    change boundedFunctionFormula.Evalb v ↔ v 0 ∈ v 2 ^ v 1
    simp [boundedFunctionFormula]
    constructor
    · rintro ⟨hp, hv⟩
      have hsub : v 0 ⊆ v 1 ×ˢ v 2 := by
        intro p hpf
        obtain ⟨x, hx, y, hy, rfl⟩ := hp p hpf
        exact kpair_mem_iff.mpr ⟨hx, hy⟩
      apply mem_function.intro hsub
      intro x hx
      obtain ⟨y, _, hxy, hu⟩ := hv x hx
      refine ⟨y, hxy, ?_⟩
      intro z hxz
      exact hu z ((kpair_mem_iff.mp (hsub _ hxz)).2) hxz
    · intro hf
      have : IsFunction (v 0) := IsFunction.of_mem hf
      refine ⟨?_, ?_⟩
      · intro p hp
        obtain ⟨x, hx, y, hy, heq⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hf p hp)
        exact ⟨x, hx, y, hy, heq⟩
      · intro x hx
        obtain ⟨y, hy, hxy⟩ := exists_of_mem_function hf x hx
        exact ⟨y, hy, hxy, fun z _ hxz ↦ IsFunction.unique hxz hxy⟩⟩

end ZFVP
