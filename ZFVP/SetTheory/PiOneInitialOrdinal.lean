import ZFVP.ModelTheory.CriticalPointCardinal

/-! A bounded injection dictionary and a Pi-one initial-ordinal formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedInjectionFormula : SetTheorySemisentence 3 :=
  “f A B. !boundedFunctionFormula f A B ∧ ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ B,
    !boundedPairMemberFormula f x z → !boundedPairMemberFormula f y z → x = y”

theorem boundedInjectionFormula_bounded : IsBoundedSetFormula boundedInjectionFormula :=
  .and (boundedFunctionFormula_bounded.subst _) (.all (.bvar 1) (.all (.bvar 2) (.all (.bvar 4)
    (.or (boundedPairMemberFormula_bounded.subst _).neg
      (.or (boundedPairMemberFormula_bounded.subst _).neg (.rel _ _))))))

def piOneInitialOrdinalFormula : SetTheorySemisentence 1 :=
  “δ. !IsOrdinal.dfn δ ∧ ∀ α ∈ δ, ∀ f, ¬!boundedInjectionFormula f δ α”

theorem piOneInitialOrdinalFormula_piOne : IsPiFormula 1 piOneInitialOrdinalFormula :=
  .and (.bounded (isOrdinalFormula_bounded.subst _)) (.boundedAll (.bvar 0)
    (.all (.bounded (boundedInjectionFormula_bounded.subst _).neg)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedInjectionFormula_defined :
    Defined (fun v : Fin 3 → V ↦ v 0 ∈ v 2 ^ v 1 ∧ Injective (v 0)) boundedInjectionFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [boundedInjectionFormula]
  intro hf
  constructor
  · intro hi x y z hx hy
    obtain ⟨hxA, hzB⟩ := mem_of_mem_functions hf hx
    obtain ⟨hyA, _⟩ := mem_of_mem_functions hf hy
    exact hi x hxA y hyA z hzB hx hy
  · intro hi x _ y _ z _ hx hy
    exact hi x y z hx hy

instance piOneInitialOrdinalFormula_defined :
    ℒₛₑₜ-predicate[V] IsInitialOrdinal via piOneInitialOrdinalFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [piOneInitialOrdinalFormula, IsInitialOrdinal, CardLE]

end ZFVP
