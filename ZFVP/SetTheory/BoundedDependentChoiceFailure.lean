import ZFVP.SetTheory.BoundedDependentChoicePath

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedDependentChoiceFailureFormula : SetTheorySemisentence 2 :=
  “κ B. ∃ A ∈ B, ∃ R ∈ B, !boundedNonemptyFormula A ∧
    (∀ β ∈ κ, ∀ s ∈ B, !boundedFunctionFormula s β A →
      ∃ x ∈ A, !boundedPairMemberFormula R s x) ∧
    ∀ f ∈ B, ¬!boundedDependentChoicePathFormula B κ A R f”

theorem boundedDependentChoiceFailureFormula_bounded : IsBoundedSetFormula boundedDependentChoiceFailureFormula :=
  .exs (.bvar 1) (.exs (.bvar 2) (.and (boundedNonemptyFormula_bounded.subst _)
    (.and (.all (.bvar 2) (.all (.bvar 4) (.or (boundedFunctionFormula_bounded.subst _).neg
      (.exs (.bvar 3) (boundedPairMemberFormula_bounded.subst _)))))
      (.all (.bvar 3) (boundedDependentChoicePathFormula_bounded.subst _).neg))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsBoundedDependentChoiceFailure (κ B : V) : Prop :=
  ∃ A ∈ B, ∃ R ∈ B, IsNonempty A ∧
    (∀ β ∈ κ, ∀ s ∈ B, s ∈ A ^ β → ∃ x ∈ A, ⟨s, x⟩ₖ ∈ R) ∧
    ∀ f ∈ B, ¬IsBoundedDependentChoicePath B κ A R f

instance boundedDependentChoiceFailureFormula_defined :
    ℒₛₑₜ-relation[V] IsBoundedDependentChoiceFailure via boundedDependentChoiceFailureFormula :=
  ⟨fun v ↦ by simp [boundedDependentChoiceFailureFormula, IsBoundedDependentChoiceFailure]⟩

theorem IsBoundedDependentChoiceFailure.not_dependentChoice {κ B : V} [IsOrdinal κ]
    (h : IsBoundedDependentChoiceFailure κ B)
    (hclosed : ∀ A ∈ B, ∀ β ∈ succ κ, ∀ f ∈ A ^ β, f ∈ B) :
    ¬InternalDependentChoiceAt κ := by
  rintro hDC
  obtain ⟨A, hA, R, _hR, hne, hserial, hfail⟩ := h
  have hs : ∀ s ∈ shorterSequences κ A, ∃ x ∈ A, ⟨s, x⟩ₖ ∈ R := by
    intro s hs
    obtain ⟨β, hβ, hsf⟩ := (mem_shorterSequences _ _ _).mp hs
    exact hserial β hβ s (hclosed A hA β (mem_succ_iff.mpr (Or.inr hβ)) s hsf) hsf
  obtain ⟨f, hf, hsteps⟩ := hDC A R hne hs
  apply hfail f (hclosed A hA κ (by simp) f hf)
  exact (boundedDependentChoicePath_iff
    (fun β hβ r hr ↦ hclosed A hA β (mem_succ_iff.mpr (Or.inr hβ)) r hr)).mpr ⟨hf, hsteps⟩

end ZFVP
