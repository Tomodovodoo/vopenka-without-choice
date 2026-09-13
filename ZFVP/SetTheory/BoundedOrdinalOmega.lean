import ZFVP.SetTheory.BoundedNaturals
import ZFVP.SetTheory.NaturalAddition

/-! A bounded graph for addition of omega on ordinals. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedSuccessorClosedFormula : SetTheorySemisentence 1 :=
  “η. ∀ x ∈ η, ∃ y ∈ η, !boundedSuccFormula y x”

def boundedOrdinalOmegaFormula : SetTheorySemisentence 2 :=
  “η δ. !IsOrdinal.dfn η ∧ !IsOrdinal.dfn δ ∧ δ ∈ η ∧
    !boundedSuccessorClosedFormula η ∧
    ∀ γ ∈ η, δ ∈ γ → ¬!boundedSuccessorClosedFormula γ”

theorem boundedSuccessorClosedFormula_bounded : IsBoundedSetFormula boundedSuccessorClosedFormula :=
  .all (.bvar 0) (.exs (.bvar 1) (boundedSuccFormula_bounded.subst _))

theorem boundedOrdinalOmegaFormula_bounded : IsBoundedSetFormula boundedOrdinalOmegaFormula :=
  .and (isOrdinalFormula_bounded.subst _) (.and (isOrdinalFormula_bounded.subst _)
    (.and (.rel _ _) (.and (boundedSuccessorClosedFormula_bounded.subst _)
      (.all (.bvar 0) (.or (.nrel _ _) (boundedSuccessorClosedFormula_bounded.subst _).neg)))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinalAdd_omega_subset_of_successor_closed {δ η : V} [IsOrdinal δ] [IsOrdinal η]
    (hδη : δ ∈ η) (hη : ∀ x ∈ η, succ x ∈ η) : ordinalAdd δ ω ⊆ η := by
  have hn : ∀ n ∈ (ω : V), ordinalAdd δ n ∈ η := by
    intro n hn
    apply naturalNumber_induction (fun n ↦ ordinalAdd δ n ∈ η) (by definability) ?_ ?_ n hn
    · simpa only [zero_def, ordinalAdd_zero] using hδη
    · intro n hn ih
      have : IsOrdinal n := IsOrdinal.of_mem hn
      simpa only [ordinalAdd_succ] using hη _ ih
  intro x hx
  obtain ⟨n, hnω, hxn⟩ := (ordinalAdd_limit δ ω (fun _ ↦ ω_succ_closed) x).mp hx
  exact IsOrdinal.toIsTransitive.mem_trans hxn (hn n hnω)

theorem ordinalAdd_omega_minimal {δ γ : V} [IsOrdinal δ] [IsOrdinal γ]
    (hγ : γ ∈ ordinalAdd δ ω) (hδγ : δ ∈ γ) : ¬(∀ x ∈ γ, succ x ∈ γ) := by
  intro hs
  exact mem_irrefl γ (ordinalAdd_omega_subset_of_successor_closed hδγ hs _ hγ)

theorem ordinalOmega_characterization (η δ : V) :
    (IsOrdinal η ∧ IsOrdinal δ ∧ δ ∈ η ∧ (∀ x ∈ η, succ x ∈ η) ∧
      ∀ γ ∈ η, δ ∈ γ → ¬(∀ x ∈ γ, succ x ∈ γ)) ↔
      IsOrdinal δ ∧ η = ordinalAdd δ ω := by
  constructor
  · rintro ⟨hη, hδ, hδη, hs, hmin⟩
    let := hη
    let := hδ
    have hsub := ordinalAdd_omega_subset_of_successor_closed hδη hs
    refine ⟨hδ, ?_⟩
    rcases IsOrdinal.subset_iff.mp hsub with he | hlt
    · exact he.symm
    · exact False.elim (hmin _ hlt (ordinalAdd_omega_gt δ) (fun _ ↦ ordinalAdd_omega_succ_closed δ))
  · rintro ⟨hδ, rfl⟩
    let := hδ
    refine ⟨inferInstance, hδ, ordinalAdd_omega_gt δ, fun _ ↦ ordinalAdd_omega_succ_closed δ, ?_⟩
    intro γ hγ hδγ
    let : IsOrdinal γ := IsOrdinal.of_mem hγ
    exact ordinalAdd_omega_minimal hγ hδγ

@[simp] theorem eval_boundedSuccessorClosedFormula (η : V) :
    boundedSuccessorClosedFormula.Evalb ![η] ↔ ∀ x ∈ η, succ x ∈ η := by
  simp [boundedSuccessorClosedFormula]

theorem eval_boundedOrdinalOmegaFormula (η δ : V) :
    boundedOrdinalOmegaFormula.Evalb ![η, δ] ↔ IsOrdinal δ ∧ η = ordinalAdd δ ω := by
  rw [← ordinalOmega_characterization]
  simp [boundedOrdinalOmegaFormula]

end ZFVP
