import ZFVP.SetTheory.ExtendibilityFailureClass

/-! Limit points of the good closure point class.

Fix `α` and assume no ordinal above `α` is `C(k+1)`-extendible. `IsGoodClosurePoint k α` is then
a closed unbounded class of `C(k+2)` ordinals (ExtendibilityFailureClass). This module adds the
three pieces the converse of Bagaria's Theorem 4.12 needs on top of that class:

* `leastGoodClosurePoint k α β`, the least good closure point above `β`;
* `IsGoodLimitPoint k α lam`, saying that `lam` is a good closure point with good closure points
  cofinally below it, together with its `Pi_{k+2}` formula and unboundedness;
* `minFailureStage k α β`, the least failure stage of `β`, which lies below every good closure
  point containing `β`.

Nothing here uses Vopenka's principle. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The `Pi_{k+2}` formula for `IsGoodLimitPoint k`. Free variables: `lam`, `α`. -/
def goodLimitPointFormula (k : ℕ) : SetTheorySemisentence 2 :=
  “lam α. !(goodClosurePointFormula k) lam α ∧
    ∀ β ∈ lam, ∃ ν ∈ lam, β ∈ ν ∧ !(goodClosurePointFormula k) ν α”

theorem goodLimitPointFormula_pi (k : ℕ) : IsPiFormula (k + 2) (goodLimitPointFormula k) := by
  refine .and ((goodClosurePointFormula_pi k).subst _) ?_
  refine .boundedAll (.bvar 0) (.boundedExs (.bvar 1) ?_)
  exact .and (.bounded (.rel _ _)) ((goodClosurePointFormula_pi k).subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The least good closure point above an ordinal -/

theorem isGoodClosurePoint_definable_pred (k : ℕ) (α : V) :
    ℒₛₑₜ-predicate[V] (IsGoodClosurePoint k α) := by
  unfold IsGoodClosurePoint IsFailureStage IsExtendibilityCandidate
  definability

/-- `x` is a good closure point strictly above `β`. -/
def IsGoodClosurePointAbove (k : ℕ) (α β x : V) : Prop := β ∈ x ∧ IsGoodClosurePoint k α x

instance isGoodClosurePointAbove_definable (k : ℕ) (α : V) :
    ℒₛₑₜ-relation[V] (IsGoodClosurePointAbove k α) := by
  unfold IsGoodClosurePointAbove IsGoodClosurePoint IsFailureStage IsExtendibilityCandidate
  definability

theorem leastGoodClosurePoint_existsUnique (k : ℕ) (α β : V)
    (h : ∃ x : V, IsOrdinal x ∧ (β ∈ x ∧ IsGoodClosurePoint k α x)) :
    ∃! x, IsLeastOrdinal (fun x ↦ β ∈ x ∧ IsGoodClosurePoint k α x) x := by
  refine leastOrdinal_existsUnique _ ?_ h
  unfold IsGoodClosurePoint IsFailureStage IsExtendibilityCandidate
  definability

/-- The least good closure point above `β`, and `∅` when there is none. -/
noncomputable def leastGoodClosurePoint (k : ℕ) (α β : V) : V := by
  classical
  exact if h : ∃ x : V, IsOrdinal x ∧ (β ∈ x ∧ IsGoodClosurePoint k α x) then
    Classical.choose! (leastGoodClosurePoint_existsUnique k α β h) else ∅

theorem leastGoodClosurePoint_eq_iff (k : ℕ) (α β x : V) :
    leastGoodClosurePoint k α β = x ↔
      IsLeastOrdinal (fun y ↦ β ∈ y ∧ IsGoodClosurePoint k α y) x ∨
        ((¬∃ y : V, IsOrdinal y ∧ (β ∈ y ∧ IsGoodClosurePoint k α y)) ∧ x = ∅) := by
  classical
  by_cases h : ∃ y : V, IsOrdinal y ∧ (β ∈ y ∧ IsGoodClosurePoint k α y)
  · simp only [h, not_true_eq_false, false_and, or_false]
    have hspec : IsLeastOrdinal (fun y ↦ β ∈ y ∧ IsGoodClosurePoint k α y)
        (leastGoodClosurePoint k α β) := by
      simpa [leastGoodClosurePoint, h] using
        Classical.choose!_spec (leastGoodClosurePoint_existsUnique k α β h)
    constructor
    · rintro rfl
      exact hspec
    · intro hx
      exact (leastGoodClosurePoint_existsUnique k α β h).unique hspec hx
  · have hn : ¬IsLeastOrdinal (fun y ↦ β ∈ y ∧ IsGoodClosurePoint k α y) x :=
      fun hl ↦ h ⟨x, hl.1, hl.2.1⟩
    simp [leastGoodClosurePoint, h, hn, eq_comm]

theorem leastGoodClosurePoint_definable (k : ℕ) (α : V) :
    ℒₛₑₜ-function₁ (leastGoodClosurePoint k α) := by
  have h : ℒₛₑₜ-relation (fun x β : V ↦
      IsLeastOrdinal (IsGoodClosurePointAbove k α β) x ∨
        ((¬∃ y : V, IsOrdinal y ∧ IsGoodClosurePointAbove k α β y) ∧ x = ∅)) := by
    unfold IsLeastOrdinal
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (leastGoodClosurePoint_eq_iff k α (v 1) (v 0))

theorem leastGoodClosurePoint_spec {k : ℕ} {α : V} [IsOrdinal α]
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ) (β : V) [IsOrdinal β] :
    IsLeastOrdinal (fun x ↦ β ∈ x ∧ IsGoodClosurePoint k α x) (leastGoodClosurePoint k α β) := by
  rcases (leastGoodClosurePoint_eq_iff k α β (leastGoodClosurePoint k α β)).mp rfl with h | ⟨h, -⟩
  · exact h
  · obtain ⟨lam, hβ, hlam⟩ := exists_goodClosurePoint_above hno β
    exact absurd ⟨lam, hlam.1, hβ, hlam⟩ h

theorem leastGoodClosurePoint_isOrdinal {k : ℕ} {α : V} [IsOrdinal α]
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ) (β : V) [IsOrdinal β] :
    IsOrdinal (leastGoodClosurePoint k α β) := (leastGoodClosurePoint_spec hno β).1

theorem mem_leastGoodClosurePoint {k : ℕ} {α : V} [IsOrdinal α]
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ) (β : V) [IsOrdinal β] :
    β ∈ leastGoodClosurePoint k α β := (leastGoodClosurePoint_spec hno β).2.1.1

theorem leastGoodClosurePoint_good {k : ℕ} {α : V} [IsOrdinal α]
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ) (β : V) [IsOrdinal β] :
    IsGoodClosurePoint k α (leastGoodClosurePoint k α β) := (leastGoodClosurePoint_spec hno β).2.1.2

/-! ### Limit points of the good class -/

/-- A good closure point with good closure points cofinally below it. -/
def IsGoodLimitPoint (k : ℕ) (α lam : V) : Prop :=
  IsGoodClosurePoint k α lam ∧ ∀ β ∈ lam, ∃ ν ∈ lam, β ∈ ν ∧ IsGoodClosurePoint k α ν

theorem goodLimitPointFormula_defines (k : ℕ) :
    Defined (fun v : Fin 2 → V ↦ IsGoodLimitPoint k (v 1) (v 0)) (goodLimitPointFormula k) := by
  have hg : Defined (fun v : Fin 2 → V ↦ IsGoodClosurePoint k (v 1) (v 0))
      (goodClosurePointFormula k) := goodClosurePointFormula_defines k
  refine ⟨fun v ↦ ?_⟩
  simp [goodLimitPointFormula, IsGoodLimitPoint, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]

theorem IsGoodLimitPoint.good {k : ℕ} {α lam : V} (h : IsGoodLimitPoint k α lam) :
    IsGoodClosurePoint k α lam := h.1

theorem IsGoodLimitPoint.cn {k : ℕ} {α lam : V} (h : IsGoodLimitPoint k α lam) :
    Cn (k + 2) lam := h.1.cn

theorem IsGoodLimitPoint.exists_good_above {k : ℕ} {α lam β : V} (h : IsGoodLimitPoint k α lam)
    (hβ : β ∈ lam) : ∃ ν ∈ lam, β ∈ ν ∧ IsGoodClosurePoint k α ν := h.2 β hβ

/-- Above every ordinal there is a limit point of the good closure point class. -/
theorem exists_goodLimitPoint_above {k : ℕ} {α : V} [IsOrdinal α]
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ) (γ : V) [IsOrdinal γ] :
    ∃ lam : V, γ ∈ lam ∧ IsGoodLimitPoint k α lam := by
  obtain ⟨lam, hγ, hlam⟩ := exists_ordinalClosurePoint_above (leastGoodClosurePoint_definable k α)
    (fun ξ hξ ↦ have : IsOrdinal ξ := hξ; leastGoodClosurePoint_isOrdinal hno ξ)
    (fun ξ hξ ↦ have : IsOrdinal ξ := hξ; mem_leastGoodClosurePoint hno ξ) γ
  have hord : IsOrdinal lam := hlam.1
  have hub : ∀ ξ ∈ lam, ∃ ν ∈ lam, ξ ∈ ν ∧ IsGoodClosurePoint k α ν := by
    intro ξ hξ
    have : IsOrdinal ξ := IsOrdinal.of_mem hξ
    exact ⟨leastGoodClosurePoint k α ξ, hlam.2.2 ξ hξ, mem_leastGoodClosurePoint hno ξ,
      leastGoodClosurePoint_good hno ξ⟩
  exact ⟨lam, hγ, goodClosurePoint_of_unbounded hlam.2.1 hub, hub⟩

/-! ### The least failure stage -/

theorem minFailureStage_existsUnique (k : ℕ) (α β : V)
    (h : ∃ μ : V, IsOrdinal μ ∧ IsFailureStage k α β μ) :
    ∃! μ, IsLeastOrdinal (IsFailureStage k α β) μ := by
  refine leastOrdinal_existsUnique _ ?_ h
  unfold IsFailureStage IsExtendibilityCandidate
  definability

/-- The least failure stage of `β`, and `∅` when there is none. -/
noncomputable def minFailureStage (k : ℕ) (α β : V) : V := by
  classical
  exact if h : ∃ μ : V, IsOrdinal μ ∧ IsFailureStage k α β μ then
    Classical.choose! (minFailureStage_existsUnique k α β h) else ∅

theorem minFailureStage_eq_iff (k : ℕ) (α β μ : V) :
    minFailureStage k α β = μ ↔ IsLeastOrdinal (IsFailureStage k α β) μ ∨
      ((¬∃ ν : V, IsOrdinal ν ∧ IsFailureStage k α β ν) ∧ μ = ∅) := by
  classical
  by_cases h : ∃ ν : V, IsOrdinal ν ∧ IsFailureStage k α β ν
  · simp only [h, not_true_eq_false, false_and, or_false]
    have hspec : IsLeastOrdinal (IsFailureStage k α β) (minFailureStage k α β) := by
      simpa [minFailureStage, h] using Classical.choose!_spec (minFailureStage_existsUnique k α β h)
    constructor
    · rintro rfl
      exact hspec
    · intro hμ
      exact (minFailureStage_existsUnique k α β h).unique hspec hμ
  · have hn : ¬IsLeastOrdinal (IsFailureStage k α β) μ := fun hl ↦ h ⟨μ, hl.1, hl.2.1⟩
    simp [minFailureStage, h, hn, eq_comm]

theorem minFailureStage_definable (k : ℕ) (α : V) : ℒₛₑₜ-function₁ (minFailureStage k α) := by
  have h : ℒₛₑₜ-relation (fun μ β : V ↦ IsLeastOrdinal (IsFailureStage k α β) μ ∨
      ((¬∃ ν : V, IsOrdinal ν ∧ IsFailureStage k α β ν) ∧ μ = ∅)) := by
    unfold IsLeastOrdinal IsFailureStage IsExtendibilityCandidate
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (minFailureStage_eq_iff k α (v 1) (v 0))

theorem minFailureStage_spec {k : ℕ} {α : V}
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ) (β : V) [IsOrdinal β] :
    IsLeastOrdinal (IsFailureStage k α β) (minFailureStage k α β) := by
  rcases (minFailureStage_eq_iff k α β (minFailureStage k α β)).mp rfl with h | ⟨h, -⟩
  · exact h
  · obtain ⟨μ, hμ⟩ := exists_isFailureStage hno β
    exact absurd ⟨μ, hμ.1.ordinal, hμ⟩ h

theorem minFailureStage_isFailureStage {k : ℕ} {α : V}
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ) (β : V) [IsOrdinal β] :
    IsFailureStage k α β (minFailureStage k α β) := (minFailureStage_spec hno β).2.1

theorem minFailureStage_mem_of_good {k : ℕ} {α lam β : V}
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ)
    (hlam : IsGoodClosurePoint k α lam) (hβ : β ∈ lam) :
    minFailureStage k α β ∈ lam := by
  have hlamord : IsOrdinal lam := hlam.1
  have hβord : IsOrdinal β := IsOrdinal.of_mem hβ
  obtain ⟨μ, hμlam, hμ⟩ := hlam.2.2.1 β hβ
  have hμord : IsOrdinal μ := hμ.1.ordinal
  have hmord : IsOrdinal (minFailureStage k α β) := (minFailureStage_spec hno β).1
  have hsub : minFailureStage k α β ⊆ μ := (minFailureStage_spec hno β).2.2 μ hμord hμ
  rcases IsOrdinal.subset_iff.mp hsub with he | hlt
  · exact he ▸ hμlam
  · exact IsOrdinal.toIsTransitive.mem_trans hlt hμlam

end ZFVP
