import ZFVP.SetTheory.BoundedSetUnionInter

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOnePairFirstFormula : SetTheorySemisentence 2 :=
  “y x. ∃ I, !boundedSInterFormula I x ∧ !boundedSUnionFormula y I”

def piOnePairFirstFormula : SetTheorySemisentence 2 :=
  “y x. ∀ I, !boundedSInterFormula I x → !boundedSUnionFormula y I”

def boundedPairSecondSupportFormula : SetTheorySemisentence 3 :=
  “S U I. (∀ z ∈ S, z ∈ U ∧ (z ∈ I → U = I)) ∧
    ∀ z ∈ U, (z ∈ I → U = I) → z ∈ S”

theorem boundedPairSecondSupportFormula_bounded : IsBoundedSetFormula boundedPairSecondSupportFormula :=
  .and (.all (.bvar 0) (.and (.rel _ _) (.or (.nrel _ _) (.rel _ _))))
    (.all (.bvar 1) (.or (IsBoundedSetFormula.or (.nrel _ _) (.rel _ _)).neg (.rel _ _)))

def sigmaOnePairSecondFormula : SetTheorySemisentence 2 :=
  “y x. ∃ U, ∃ I, ∃ S, !boundedSUnionFormula U x ∧ !boundedSInterFormula I x ∧
    !boundedPairSecondSupportFormula S U I ∧ !boundedSUnionFormula y S”

def piOnePairSecondFormula : SetTheorySemisentence 2 :=
  “y x. ∀ U, ∀ I, ∀ S, !boundedSUnionFormula U x → !boundedSInterFormula I x →
    !boundedPairSecondSupportFormula S U I → !boundedSUnionFormula y S”

theorem sigmaOnePairFirstFormula_sigmaOne : IsSigmaFormula 1 sigmaOnePairFirstFormula :=
  .exs (.bounded (.and (boundedSInterFormula_bounded.subst _) (boundedSUnionFormula_bounded.subst _)))

theorem piOnePairFirstFormula_piOne : IsPiFormula 1 piOnePairFirstFormula :=
  .all (.bounded (.or (boundedSInterFormula_bounded.subst _).neg (boundedSUnionFormula_bounded.subst _)))

theorem sigmaOnePairSecondFormula_sigmaOne : IsSigmaFormula 1 sigmaOnePairSecondFormula :=
  .exs (.exs (.exs (.bounded (.and (boundedSUnionFormula_bounded.subst _)
    (.and (boundedSInterFormula_bounded.subst _) (.and (boundedPairSecondSupportFormula_bounded.subst _)
      (boundedSUnionFormula_bounded.subst _)))))))

theorem piOnePairSecondFormula_piOne : IsPiFormula 1 piOnePairSecondFormula :=
  .all (.all (.all (.bounded (.or (boundedSUnionFormula_bounded.subst _).neg
    (.or (boundedSInterFormula_bounded.subst _).neg (.or (boundedPairSecondSupportFormula_bounded.subst _).neg
      (boundedSUnionFormula_bounded.subst _)))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedPairSecondSupportFormula_defined :
    ℒₛₑₜ-function₂[V] (fun U I : V ↦ {x ∈ U; x ∈ I → U = I}) via boundedPairSecondSupportFormula :=
  ⟨fun v ↦ by
    change boundedPairSecondSupportFormula.Evalb v ↔ v 0 = {x ∈ v 1; x ∈ v 2 → v 1 = v 2}
    simp [boundedPairSecondSupportFormula]
    constructor
    · rintro ⟨hf, hb⟩
      apply mem_ext
      intro x
      rw [mem_sep_iff]
      exact ⟨hf x, fun ⟨hu, hi⟩ ↦ hb x hu hi⟩
    · intro h
      rw [h]
      exact ⟨fun x hx ↦ mem_sep_iff.mp hx, fun x hu hi ↦ mem_sep_iff.mpr ⟨hu, hi⟩⟩⟩

instance sigmaOnePairFirstFormula_defined : ℒₛₑₜ-function₁[V] kpair.π₁ via sigmaOnePairFirstFormula :=
  ⟨fun v ↦ by simp [sigmaOnePairFirstFormula, kpair.π₁]⟩

instance piOnePairFirstFormula_defined : ℒₛₑₜ-function₁[V] kpair.π₁ via piOnePairFirstFormula :=
  ⟨fun v ↦ by simp [piOnePairFirstFormula, kpair.π₁]⟩

instance sigmaOnePairSecondFormula_defined : ℒₛₑₜ-function₁[V] kpair.π₂ via sigmaOnePairSecondFormula :=
  ⟨fun v ↦ by
    simp [sigmaOnePairSecondFormula, kpair.π₂]
    constructor
    · rintro ⟨S, hS, h⟩
      exact h.trans (congrArg sUnion hS)
    · intro h
      exact ⟨_, rfl, h⟩⟩

instance piOnePairSecondFormula_defined : ℒₛₑₜ-function₁[V] kpair.π₂ via piOnePairSecondFormula :=
  ⟨fun v ↦ by
    simp [piOnePairSecondFormula, kpair.π₂]
    constructor
    · intro h
      exact h _ _ _ rfl rfl rfl
    · intro h U I S hU hI hS
      subst U I
      exact h.trans (congrArg sUnion hS.symm)⟩

end ZFVP
