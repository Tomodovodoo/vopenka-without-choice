import ZFVP.SetTheory.SigmaOneStarCorrectness
import ZFVP.Syntax.SigmaOneBoundedCodes

/-! Pi-one presentations of C(1) and of Sigma-one-star correctness, relative to a
Sigma-one graph of the cumulative hierarchy.

The shipped formulas `cnFormula 1` and `sigmaOneStarCorrectFormula` sit at Pi_2 for one
reason: the antecedent `piOneHierarchyFormula A α` occurs negatively, and it is Pi_1.
The first section here splits that antecedent into its two halves.  The half `A ⊆ V_α`
is Delta_1, because `rank` is; the half `V_α ⊆ A` is Pi_1 and has no Sigma_1 form, since
a Sigma_1 graph of `α ↦ V_α` would make the power set operation Sigma_1 and would make
`y = V_α` upward absolute from transitive models, which it is not.

Everything else in the Pi_1 computation goes through, and the two remaining sections
record that: given a Sigma_1 formula `H` defining `IsHierarchySegment` (and, for the
second predicate, a Sigma_1 and a Pi_1 formula for `StarReflectionWitness`), the
formulas built below are Pi_1 and define `Cn 1` and `IsSigmaOneStarCorrect` exactly as
shipped.  The hypotheses isolate the single missing input; no such `H` is available in
ZF.  Bagaria's Pi_1 definition of C(1) goes through `V_α = H_α` and uses choice. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- `A ⊆ hierarchy α`, written with the Sigma-one graph of `rank`. -/
def sigmaOneSubsetHierarchyFormula : SetTheorySemisentence 2 :=
  “A α. ∀ x ∈ A, !sigmaOneRankLtFormula x α”

/-- `A ⊆ hierarchy α`, written with the Pi-one graph of `rank`. -/
def piOneSubsetHierarchyFormula : SetTheorySemisentence 2 :=
  “A α. ∀ x ∈ A, !piOneRankLtFormula x α”

/-- `hierarchy α ⊆ A`.  This is the half of the hierarchy graph with no Sigma-one form. -/
def piOneHierarchySubsetFormula : SetTheorySemisentence 2 :=
  “A α. ∀ x, !sigmaOneRankLtFormula x α → x ∈ A”

theorem sigmaOneSubsetHierarchyFormula_sigmaOne :
    IsSigmaFormula 1 sigmaOneSubsetHierarchyFormula :=
  .boundedAll (.bvar 0) (sigmaOneRankLtFormula_sigmaOne.subst _)

theorem piOneSubsetHierarchyFormula_piOne : IsPiFormula 1 piOneSubsetHierarchyFormula :=
  .boundedAll (.bvar 0) (piOneRankLtFormula_piOne.subst _)

theorem piOneHierarchySubsetFormula_piOne : IsPiFormula 1 piOneHierarchySubsetFormula :=
  .all (.or (sigmaOneRankLtFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

section Formulas

variable (H : SetTheorySemisentence 2) (Wσ Wπ : SetTheorySemisentence 4)

/-- `C(1)` with the hierarchy segment supplied by `H` instead of by `piOneHierarchyFormula`. -/
def piOneCnOneFormula : SetTheorySemisentence 1 :=
  “α. !IsOrdinal.dfn α ∧ ∀ A, !H A α → !(correctDomainFormula 1) A”

/-- Sigma-one-star correctness with the hierarchy segment supplied by `H`, the witness
clause split into a Sigma-one occurrence `Wσ` and a Pi-one occurrence `Wπ`. -/
def piOneSigmaOneStarCorrectFormula : SetTheorySemisentence 1 :=
  “γ. !(piOneCnOneFormula H) γ ∧ ∀ A, !H A γ → ∀ α ∈ γ, ∀ a ∈ A, ∀ φ, ∀ two,
    !(boundedNumeralFormula 2) two → !sigmaOneBoundedCodeFormula two φ →
    (∃ b, !Wσ α φ a b) → ∃ b ∈ A, !Wπ α φ a b”

theorem piOneCnOneFormula_piOne (hH : IsSigmaFormula 1 H) :
    IsPiFormula 1 (piOneCnOneFormula H) :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.all (.or (hH.subst _).neg ((correctDomainFormula_pi 1).subst _)))

theorem piOneSigmaOneStarCorrectFormula_piOne (hH : IsSigmaFormula 1 H)
    (hσ : IsSigmaFormula 1 Wσ) (hπ : IsPiFormula 1 Wπ) :
    IsPiFormula 1 (piOneSigmaOneStarCorrectFormula H Wσ Wπ) := by
  refine .and ((piOneCnOneFormula_piOne H hH).subst _) (.all (.or (hH.subst _).neg ?_))
  refine .boundedAll (.bvar _) (.boundedAll (.bvar _) (.all (.all ?_)))
  refine .or (.bounded ((boundedNumeralFormula_bounded 2).subst _).neg) ?_
  refine .or (sigmaOneBoundedCodeFormula_sigmaOne.subst _).neg ?_
  exact .or (IsLevyFormula.exs (hσ.subst _)).neg (.boundedExs (.bvar _) (hπ.subst _))

end Formulas

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneSubsetHierarchyFormula (A α : V) [IsOrdinal α] :
    sigmaOneSubsetHierarchyFormula.Evalb ![A, α] ↔ ∀ x ∈ A, x ∈ hierarchy α := by
  simp [sigmaOneSubsetHierarchyFormula, eval_sigmaOneRankLtFormula, mem_hierarchy_iff_rank_mem]

theorem eval_piOneSubsetHierarchyFormula (A α : V) [IsOrdinal α] :
    piOneSubsetHierarchyFormula.Evalb ![A, α] ↔ ∀ x ∈ A, x ∈ hierarchy α := by
  simp [piOneSubsetHierarchyFormula, eval_piOneRankLtFormula, mem_hierarchy_iff_rank_mem]

theorem eval_piOneHierarchySubsetFormula (A α : V) [IsOrdinal α] :
    piOneHierarchySubsetFormula.Evalb ![A, α] ↔ ∀ x ∈ hierarchy α, x ∈ A := by
  simp [piOneHierarchySubsetFormula, eval_sigmaOneRankLtFormula, mem_hierarchy_iff_rank_mem]

/-- The Pi-one hierarchy graph is the conjunction of a Delta-one half and a Pi-one half. -/
theorem eval_piOneHierarchyFormula_split (A α : V) :
    piOneHierarchyFormula.Evalb ![A, α] ↔ IsOrdinal α ∧
      sigmaOneSubsetHierarchyFormula.Evalb ![A, α] ∧ piOneHierarchySubsetFormula.Evalb ![A, α] := by
  rw [eval_piOneHierarchyFormula]
  constructor
  · rintro ⟨hα, rfl⟩
    let := hα
    exact ⟨hα, (eval_sigmaOneSubsetHierarchyFormula _ α).mpr (fun _ h ↦ h),
      (eval_piOneHierarchySubsetFormula _ α).mpr (fun _ h ↦ h)⟩
  · rintro ⟨hα, h₁, h₂⟩
    let := hα
    refine ⟨hα, mem_ext fun x ↦ ⟨?_, ?_⟩⟩
    · exact (eval_sigmaOneSubsetHierarchyFormula A α).mp h₁ x
    · exact (eval_piOneHierarchySubsetFormula A α).mp h₂ x

theorem eval_piOneCnOneFormula (H : SetTheorySemisentence 2)
    [ℒₛₑₜ-relation[V] IsHierarchySegment via H] (α : V) :
    (piOneCnOneFormula H).Evalb ![α] ↔ Cn 1 α := by
  have h : (piOneCnOneFormula H).Evalb ![α] ↔ IsCorrectRankStage 1 α := by
    simp (config := { contextual := true }) [piOneCnOneFormula, IsHierarchySegment,
      IsCorrectRankStage]
  exact h.trans (cn_successor_iff 0 α).symm

theorem eval_piOneSigmaOneStarCorrectFormula (H : SetTheorySemisentence 2)
    (Wσ Wπ : SetTheorySemisentence 4) [ℒₛₑₜ-relation[V] IsHierarchySegment via H]
    [ℒₛₑₜ-relation₄[V] StarReflectionWitness via Wσ]
    [ℒₛₑₜ-relation₄[V] StarReflectionWitness via Wπ] (γ : V) :
    (piOneSigmaOneStarCorrectFormula H Wσ Wπ).Evalb ![γ] ↔ IsSigmaOneStarCorrect γ := by
  simp (config := { contextual := true }) [piOneSigmaOneStarCorrectFormula,
    eval_piOneCnOneFormula, IsHierarchySegment, IsSigmaOneStarCorrect]
  exact fun h ↦ Or.inl h.ordinal

/-- The evaluation clauses are about the shipped predicates: taking the shipped Pi-one
hierarchy graph for `H` gives back `Cn 1`.  That instance is Pi_2, not Pi_1. -/
theorem eval_piOneCnOneFormula_shipped (α : V) :
    (piOneCnOneFormula piOneHierarchyFormula).Evalb ![α] ↔ Cn 1 α :=
  eval_piOneCnOneFormula piOneHierarchyFormula α

theorem eval_piOneSigmaOneStarCorrectFormula_shipped (γ : V) :
    (piOneSigmaOneStarCorrectFormula piOneHierarchyFormula starReflectionWitnessFormula
      starReflectionWitnessFormula).Evalb ![γ] ↔ IsSigmaOneStarCorrect γ :=
  eval_piOneSigmaOneStarCorrectFormula _ _ _ γ

end ZFVP
