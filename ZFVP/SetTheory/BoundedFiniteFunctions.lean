import ZFVP.SetTheory.BoundedSequenceSupport
import ZFVP.ModelTheory.ConstantStructure
import ZFVP.Syntax.StandardTuples

/-! Bounded graph checks for constant functions and finite function spaces in a support. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedConstantGraphFormula : SetTheorySemisentence 3 :=
  “f A a. (∀ p ∈ f, ∃ x ∈ A, !boundedKpairFormula p x a) ∧
    ∀ x ∈ A, !boundedPairMemberFormula f x a”

def boundedFiniteFunctionSetFormula : SetTheorySemisentence 4 :=
  “U X A n. (∀ s ∈ X, !boundedFunctionFormula s n A) ∧
    ∀ s ∈ U, !boundedFunctionFormula s n A → s ∈ X”

theorem boundedConstantGraphFormula_bounded : IsBoundedSetFormula boundedConstantGraphFormula :=
  .and (.all (.bvar 0) (.exs (.bvar 2) (boundedKpairFormula_bounded.subst _)))
    (.all (.bvar 1) (boundedPairMemberFormula_bounded.subst _))

theorem boundedFiniteFunctionSetFormula_bounded : IsBoundedSetFormula boundedFiniteFunctionSetFormula :=
  .and (.all (.bvar 1) (boundedFunctionFormula_bounded.subst _))
    (.all (.bvar 0) (.or (boundedFunctionFormula_bounded.subst _).neg (.rel _ _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem eval_boundedConstantGraphFormula (f A a : V) :
    boundedConstantGraphFormula.Evalb ![f, A, a] ↔ f = constantGraph A a := by
  simp only [boundedConstantGraphFormula]
  simp
  rw [mem_ext_iff]
  simp only [constantGraph, mem_definableGraph_iff]
  constructor
  · rintro ⟨hl, hr⟩ p
    exact ⟨fun hp ↦ hl p hp, fun ⟨x, hx, he⟩ ↦ he ▸ hr x hx⟩
  · intro h
    exact ⟨fun p hp ↦ (h p).mp hp, fun x hx ↦ (h _).mpr ⟨x, hx, rfl⟩⟩

theorem eval_boundedFiniteFunctionSetFormula {U A n : V} [IsSequenceSupport U]
    (hA : A ⊆ U) (hn : n ∈ (ω : V)) (X : V) :
    boundedFiniteFunctionSetFormula.Evalb ![U, X, A, n] ↔ X = A ^ n := by
  simp [boundedFiniteFunctionSetFormula]
  constructor
  · rintro ⟨hl, hr⟩
    apply SetTheory.subset_antisymm hl
    exact fun s hs ↦ hr s (function_mem_sequenceSupport hA hn hs) hs
  · rintro rfl
    exact ⟨fun _ hs ↦ hs, fun _ _ hs ↦ hs⟩

theorem sequenceSupport_containing_parameters {n : ℕ} (v : Fin n → V) :
    ∃ U : V, IsSequenceSupport U ∧ ∀ i, v i ∈ U := by
  obtain ⟨U, hU, ht⟩ := sequenceSupport_containing (standardTuple v)
  let := hU
  refine ⟨U, hU, ?_⟩
  intro i
  have hp : ⟨(i.val : V), v i⟩ₖ ∈ U :=
    hU.toIsTransitive.mem_trans ((mem_standardTuple_iff v _).mpr ⟨i, rfl⟩) ht
  exact (kpair_components_mem_transitive hp).2

end ZFVP
