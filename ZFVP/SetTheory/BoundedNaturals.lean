import ZFVP.SetTheory.BoundedCodingPrimitives
import ZFVP.SetTheory.NaturalPredecessor

/-! Bounded definitions of standard numerals and of the internal omega set. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedNumeralFormula : ℕ → SetTheorySemisentence 1
  | 0 => boundedEmptyFormula
  | n + 1 => “x. ∃ y ∈ x, !(boundedNumeralFormula n) y ∧ !boundedSuccFormula x y”

theorem boundedNumeralFormula_bounded (n : ℕ) : IsBoundedSetFormula (boundedNumeralFormula n) := by
  induction n with
  | zero => exact boundedEmptyFormula_bounded
  | succ n ih =>
    exact .exs (.bvar 0) (.and (ih.subst ![.bvar 0]) (boundedSuccFormula_bounded.subst ![.bvar 1, .bvar 0]))

def boundedOmegaFormula : SetTheorySemisentence 1 :=
  “W. !IsOrdinal.dfn W ∧ (∃ e ∈ W, !boundedEmptyFormula e) ∧
    (∀ x ∈ W, ∃ y ∈ W, !boundedSuccFormula y x) ∧
    ∀ x ∈ W, !boundedEmptyFormula x ∨ ∃ y ∈ x, !boundedSuccFormula x y”

theorem boundedOmegaFormula_bounded : IsBoundedSetFormula boundedOmegaFormula := by
  exact .and (isOrdinalFormula_bounded.subst ![.bvar 0])
    (.and (.exs (.bvar 0) (boundedEmptyFormula_bounded.subst ![.bvar 0]))
      (.and (.all (.bvar 0) (.exs (.bvar 1) (boundedSuccFormula_bounded.subst ![.bvar 0, .bvar 1])))
        (.all (.bvar 0) (.or (boundedEmptyFormula_bounded.subst ![.bvar 0])
          (.exs (.bvar 0) (boundedSuccFormula_bounded.subst ![.bvar 1, .bvar 0]))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedNumeralFormula_defined (n : ℕ) :
    ℒₛₑₜ-function₀[V] (n : V) via boundedNumeralFormula n := by
  induction n with
  | zero => exact boundedEmptyFormula_defined
  | succ n ih =>
    exact ⟨fun v ↦ by
      change (boundedNumeralFormula (n + 1)).Evalb v ↔ v 0 = ((n + 1 : ℕ) : V)
      simp [boundedNumeralFormula, num_succ_def]
      intro h
      rw [h]
      simp⟩

def IsOmegaBySuccessors (W : V) : Prop := IsOrdinal W ∧ (∅ : V) ∈ W ∧
  (∀ x ∈ W, succ x ∈ W) ∧ ∀ x ∈ W, x = ∅ ∨ ∃ y ∈ x, x = succ y

theorem isOmegaBySuccessors_iff (W : V) : IsOmegaBySuccessors W ↔ W = (ω : V) := by
  constructor
  · rintro ⟨hW, h0, hs, hp⟩
    let := hW
    have hωW : (ω : V) ⊆ W := (show IsInductive W from ⟨h0, hs⟩).ω_subset
    have hall : ∀ x : Ordinal V, (x : V) ∈ W → (x : V) ∈ (ω : V) := by
      apply transfinite_induction (P := fun x : V ↦ x ∈ W → x ∈ (ω : V)) (by definability)
      intro x ih hx
      rcases hp x hx with hzero | ⟨y, hy, hxy⟩
      · rw [hzero]
        exact empty_mem_ω
      · have : IsOrdinal y := IsOrdinal.of_mem hy
        have hyW := hW.transitive x hx y hy
        have hyω := ih (IsOrdinal.toOrdinal y) hy hyW
        rw [hxy]
        exact ω_succ_closed hyω
    apply SetTheory.subset_antisymm
    · intro x hx
      have : IsOrdinal x := IsOrdinal.of_mem hx
      exact hall (IsOrdinal.toOrdinal x) hx
    · exact hωW
  · rintro rfl
    refine ⟨inferInstance, empty_mem_ω, fun _ ↦ ω_succ_closed, ?_⟩
    intro x hx
    rcases internalNatural_cases hx with hzero | ⟨y, _, rfl⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨y, by simp, rfl⟩

instance boundedOmegaFormula_defined : ℒₛₑₜ-function₀[V] (ω : V) via boundedOmegaFormula :=
  ⟨fun v ↦ by
    change boundedOmegaFormula.Evalb v ↔ v 0 = (ω : V)
    rw [← isOmegaBySuccessors_iff]
    simp [boundedOmegaFormula, IsOmegaBySuccessors]⟩

end ZFVP
