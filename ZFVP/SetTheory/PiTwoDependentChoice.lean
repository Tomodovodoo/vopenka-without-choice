import ZFVP.SetTheory.BoundedDependentChoicePath
import ZFVP.SetTheory.LevySubstitution
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piOneShorterSequencesFormula : SetTheorySemisentence 3 :=
  “S κ A. (∀ s ∈ S, ∃ β ∈ κ, !boundedFunctionFormula s β A) ∧
    ∀ s, (∃ β ∈ κ, !boundedFunctionFormula s β A) → s ∈ S”

theorem piOneShorterSequencesFormula_piOne : IsPiFormula 1 piOneShorterSequencesFormula :=
  .and (.bounded (.all (.bvar 0) (.exs (.bvar 2) (boundedFunctionFormula_bounded.subst _))))
    (.all (.bounded (.or (IsBoundedSetFormula.exs (.bvar 2) (boundedFunctionFormula_bounded.subst _)).neg (.rel _ _))))

def boundedSequenceSerialFormula : SetTheorySemisentence 3 :=
  “S A R. ∀ s ∈ S, ∃ x ∈ A, !boundedPairMemberFormula R s x”

theorem boundedSequenceSerialFormula_bounded : IsBoundedSetFormula boundedSequenceSerialFormula :=
  .all (.bvar 0) (.exs (.bvar 2) (boundedPairMemberFormula_bounded.subst _))

def piTwoOrdinalDependentChoiceFormula : SetTheorySemisentence 1 :=
  “κ. !IsOrdinal.dfn κ ∧ ∀ A S R, !piOneShorterSequencesFormula S κ A →
    !boundedNonemptyFormula A → !boundedSequenceSerialFormula S A R →
      ∃ f, !boundedDependentChoicePathFormula S κ A R f”

theorem piTwoOrdinalDependentChoiceFormula_piTwo : IsPiFormula 2 piTwoOrdinalDependentChoiceFormula :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.all (.all (.all (.raise (.or (piOneShorterSequencesFormula_piOne.subst _).neg
      (.or (.bounded (boundedNonemptyFormula_bounded.subst _).neg)
        (.or (.bounded (boundedSequenceSerialFormula_bounded.subst _).neg)
          (.exs (.bounded (boundedDependentChoicePathFormula_bounded.subst _))))))))))

def piTwoOrdinalDependentChoiceBelowFormula : SetTheorySemisentence 1 :=
  “κ. !IsOrdinal.dfn κ ∧ ∀ γ ∈ κ, !piTwoOrdinalDependentChoiceFormula γ”

theorem piTwoOrdinalDependentChoiceBelowFormula_piTwo :
    IsPiFormula 2 piTwoOrdinalDependentChoiceBelowFormula :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.boundedAll (.bvar 0) (piTwoOrdinalDependentChoiceFormula_piTwo.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance piOneShorterSequencesFormula_defined :
    ℒₛₑₜ-function₂[V] shorterSequences via piOneShorterSequencesFormula :=
  ⟨fun v ↦ by
    simp [piOneShorterSequencesFormula]
    rw [mem_ext_iff]
    simp only [mem_shorterSequences]
    exact ⟨fun h s ↦ ⟨h.1 s, fun ⟨β, hβ, hf⟩ ↦ h.2 s β hβ hf⟩,
      fun h ↦ ⟨fun s ↦ (h s).mp, fun s β hβ hf ↦ (h s).mpr ⟨β, hβ, hf⟩⟩⟩⟩


instance boundedSequenceSerialFormula_defined : Defined
    (fun v : Fin 3 → V ↦ ∀ s ∈ v 0, ∃ x ∈ v 1, ⟨s, x⟩ₖ ∈ v 2)
    boundedSequenceSerialFormula :=
  ⟨fun v ↦ by simp [boundedSequenceSerialFormula]⟩

theorem eval_piTwoOrdinalDependentChoiceFormula (κ : V) :
    piTwoOrdinalDependentChoiceFormula.Evalb ![κ] ↔ IsOrdinal κ ∧ InternalDependentChoiceAt κ := by
  have he : piTwoOrdinalDependentChoiceFormula.Evalb ![κ] ↔
      IsOrdinal κ ∧ ∀ A S R : V, S = shorterSequences κ A → IsNonempty A →
        (∀ s ∈ S, ∃ x ∈ A, ⟨s, x⟩ₖ ∈ R) → ∃ f, IsBoundedDependentChoicePath S κ A R f := by
    simp [piTwoOrdinalDependentChoiceFormula]
  rw [he]
  constructor
  · rintro ⟨hk, h⟩
    let := hk
    refine ⟨hk, ?_⟩
    intro A R hA hR
    obtain ⟨f, hf⟩ := h A (shorterSequences κ A) R rfl hA hR
    exact (boundedDependentChoicePath_iff
      (fun β hβ r hr ↦ (mem_shorterSequences κ A r).mpr ⟨β, hβ, hr⟩)).mp hf
      |> fun hf ↦ ⟨f, hf.1, hf.2⟩
  · rintro ⟨hk, hDC⟩
    let := hk
    refine ⟨hk, ?_⟩
    intro A S R hS hA hR
    subst S
    obtain ⟨f, hf, hsteps⟩ := hDC A R hA hR
    exact ⟨f, (boundedDependentChoicePath_iff
      (fun β hβ r hr ↦ (mem_shorterSequences κ A r).mpr ⟨β, hβ, hr⟩)).mpr ⟨hf, hsteps⟩⟩

instance piTwoOrdinalDependentChoiceFormula_defined :
    ℒₛₑₜ-predicate[V] (fun κ ↦ IsOrdinal κ ∧ InternalDependentChoiceAt κ)
      via piTwoOrdinalDependentChoiceFormula :=
  ⟨fun v ↦ by
    have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    rw [← hv]
    exact eval_piTwoOrdinalDependentChoiceFormula (v 0)⟩

theorem eval_piTwoOrdinalDependentChoiceBelowFormula (κ : V) :
    piTwoOrdinalDependentChoiceBelowFormula.Evalb ![κ] ↔
      IsOrdinal κ ∧ ∀ γ ∈ κ, InternalDependentChoiceAt γ := by
  have he : piTwoOrdinalDependentChoiceBelowFormula.Evalb ![κ] ↔
      IsOrdinal κ ∧ ∀ γ ∈ κ, IsOrdinal γ ∧ InternalDependentChoiceAt γ := by
    simp [piTwoOrdinalDependentChoiceBelowFormula]
  rw [he]
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun γ hγ ↦ (h γ hγ).2⟩
  · rintro ⟨hk, h⟩
    let := hk
    exact ⟨hk, fun γ hγ ↦ ⟨IsOrdinal.of_mem hγ, h γ hγ⟩⟩

instance piTwoOrdinalDependentChoiceBelowFormula_defined :
    ℒₛₑₜ-predicate[V] (fun κ ↦ IsOrdinal κ ∧ ∀ γ ∈ κ, InternalDependentChoiceAt γ)
      via piTwoOrdinalDependentChoiceBelowFormula :=
  ⟨fun v ↦ by
    have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    rw [← hv]
    exact eval_piTwoOrdinalDependentChoiceBelowFormula (v 0)⟩
end ZFVP
