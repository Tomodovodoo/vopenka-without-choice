import ZFVP.SetTheory.MagidorClosurePoint
import ZFVP.SetTheory.OrdinalClosureClass

/-! # Limit points of the Magidor closure point class

`ZFVP.SetTheory.MagidorClosurePoint` builds the class of closure points of the failure function
`magidorFailure ρ` and shows it is unbounded. This module adds the pieces the `Pi_1` index
condition needs on top of that class, in the same shape as
`ZFVP.SetTheory.GoodLimitPointClass` does for the good closure point class:

* `leastMagidorClosurePoint ρ β`, the least closure point above `β`;
* `IsMagidorClosureLimitPoint ρ lam`, saying that `lam` is a limit ordinal above `ρ` with closure
  points cofinally below it, together with its definability, the fact that such a `lam` is itself a
  closure point, and unboundedness of the class;
* `IsLeastMagidorClosureLimitPoint ρ r lam`, the least closure limit point above a marker `r`,
  with existence and functionality.

`IsMagidorClosurePoint` is used here only through `magidorFailure_mem_of_closurePoint` and
`exists_magidorClosurePoint_above`; nothing about supercompactness is reproved. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The least closure point above an ordinal -/

/-- `x` is a Magidor closure point strictly above `β`. -/
def IsMagidorClosurePointAbove (ρ β x : V) : Prop := β ∈ x ∧ IsMagidorClosurePoint ρ x

instance isMagidorClosurePointAbove_definable :
    ℒₛₑₜ-relation₃[V] IsMagidorClosurePointAbove := by
  unfold IsMagidorClosurePointAbove
  definability

theorem leastMagidorClosurePoint_existsUnique (ρ β : V)
    (h : ∃ x : V, IsOrdinal x ∧ (β ∈ x ∧ IsMagidorClosurePoint ρ x)) :
    ∃! x, IsLeastOrdinal (fun x ↦ β ∈ x ∧ IsMagidorClosurePoint ρ x) x :=
  leastOrdinal_existsUnique _ (by definability) h

/-- The least Magidor closure point above `β`, and `∅` when there is none. -/
noncomputable def leastMagidorClosurePoint (ρ β : V) : V := by
  classical
  exact if h : ∃ x : V, IsOrdinal x ∧ (β ∈ x ∧ IsMagidorClosurePoint ρ x) then
    Classical.choose! (leastMagidorClosurePoint_existsUnique ρ β h) else ∅

theorem leastMagidorClosurePoint_eq_iff (ρ β x : V) :
    leastMagidorClosurePoint ρ β = x ↔
      IsLeastOrdinal (fun y ↦ β ∈ y ∧ IsMagidorClosurePoint ρ y) x ∨
        ((¬∃ y : V, IsOrdinal y ∧ (β ∈ y ∧ IsMagidorClosurePoint ρ y)) ∧ x = ∅) := by
  classical
  by_cases h : ∃ y : V, IsOrdinal y ∧ (β ∈ y ∧ IsMagidorClosurePoint ρ y)
  · simp only [h, not_true_eq_false, false_and, or_false]
    have hspec : IsLeastOrdinal (fun y ↦ β ∈ y ∧ IsMagidorClosurePoint ρ y)
        (leastMagidorClosurePoint ρ β) := by
      simpa [leastMagidorClosurePoint, h] using
        Classical.choose!_spec (leastMagidorClosurePoint_existsUnique ρ β h)
    constructor
    · rintro rfl
      exact hspec
    · intro hx
      exact (leastMagidorClosurePoint_existsUnique ρ β h).unique hspec hx
  · have hn : ¬IsLeastOrdinal (fun y ↦ β ∈ y ∧ IsMagidorClosurePoint ρ y) x :=
      fun hl ↦ h ⟨x, hl.1, hl.2.1⟩
    simp [leastMagidorClosurePoint, h, hn, eq_comm]

theorem leastMagidorClosurePoint_definable (ρ : V) :
    ℒₛₑₜ-function₁ (leastMagidorClosurePoint ρ) := by
  have h : ℒₛₑₜ-relation (fun x β : V ↦
      IsLeastOrdinal (IsMagidorClosurePointAbove ρ β) x ∨
        ((¬∃ y : V, IsOrdinal y ∧ IsMagidorClosurePointAbove ρ β y) ∧ x = ∅)) := by
    unfold IsLeastOrdinal IsMagidorClosurePointAbove
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (leastMagidorClosurePoint_eq_iff ρ (v 1) (v 0))

theorem leastMagidorClosurePoint_spec {ρ : V} [IsOrdinal ρ] (htot : MagidorFailureTotal ρ)
    (β : V) [IsOrdinal β] :
    IsLeastOrdinal (fun x ↦ β ∈ x ∧ IsMagidorClosurePoint ρ x)
      (leastMagidorClosurePoint ρ β) := by
  rcases (leastMagidorClosurePoint_eq_iff ρ β (leastMagidorClosurePoint ρ β)).mp rfl with
    h | ⟨h, -⟩
  · exact h
  · obtain ⟨d, hd, hβd⟩ := exists_magidorClosurePoint_above htot β
    exact absurd ⟨d, hd.1.1, hβd, hd⟩ h

theorem leastMagidorClosurePoint_isOrdinal {ρ : V} [IsOrdinal ρ] (htot : MagidorFailureTotal ρ)
    (β : V) [IsOrdinal β] : IsOrdinal (leastMagidorClosurePoint ρ β) :=
  (leastMagidorClosurePoint_spec htot β).1

theorem mem_leastMagidorClosurePoint {ρ : V} [IsOrdinal ρ] (htot : MagidorFailureTotal ρ)
    (β : V) [IsOrdinal β] : β ∈ leastMagidorClosurePoint ρ β :=
  (leastMagidorClosurePoint_spec htot β).2.1.1

theorem leastMagidorClosurePoint_isClosurePoint {ρ : V} [IsOrdinal ρ]
    (htot : MagidorFailureTotal ρ) (β : V) [IsOrdinal β] :
    IsMagidorClosurePoint ρ (leastMagidorClosurePoint ρ β) :=
  (leastMagidorClosurePoint_spec htot β).2.1.2

/-- Nothing strictly between `β` and the least closure point above `β` is a closure point. -/
theorem leastMagidorClosurePoint_least {ρ : V} [IsOrdinal ρ] (htot : MagidorFailureTotal ρ)
    (β : V) [IsOrdinal β] :
    ∀ ξ ∈ leastMagidorClosurePoint ρ β, β ∈ ξ → ¬ IsMagidorClosurePoint ρ ξ := by
  have hlord : IsOrdinal (leastMagidorClosurePoint ρ β) :=
    leastMagidorClosurePoint_isOrdinal htot β
  intro ξ hξ hβξ hcp
  have hξord : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hsub : leastMagidorClosurePoint ρ β ⊆ ξ :=
    (leastMagidorClosurePoint_spec htot β).2.2 ξ hξord ⟨hβξ, hcp⟩
  exact mem_irrefl ξ (hsub ξ hξ)

/-! ### Limit points of the closure point class -/

/-- A limit ordinal above `ρ` with Magidor closure points cofinally below it. -/
def IsMagidorClosureLimitPoint (ρ lam : V) : Prop :=
  IsLimitOrdinal lam ∧ ρ ∈ lam ∧ ∀ ξ ∈ lam, ∃ d ∈ lam, ξ ∈ d ∧ IsMagidorClosurePoint ρ d

instance isMagidorClosureLimitPoint_definable :
    ℒₛₑₜ-relation[V] IsMagidorClosureLimitPoint := by
  unfold IsMagidorClosureLimitPoint IsLimitOrdinal
  definability

/-- A limit of closure points is a closure point. -/
theorem IsMagidorClosureLimitPoint.closurePoint {ρ lam : V}
    (h : IsMagidorClosureLimitPoint ρ lam) : IsMagidorClosurePoint ρ lam := by
  have hord : IsOrdinal lam := h.1.1
  refine ⟨h.1, h.2.1, ?_⟩
  intro ν hν hρν
  obtain ⟨d, hdlam, hνd, hd⟩ := h.2.2 ν hν
  exact IsOrdinal.toIsTransitive.mem_trans
    (magidorFailure_mem_of_closurePoint hd hρν hνd) hdlam

/-- Above every ordinal there is a limit point of the closure point class. -/
theorem exists_magidorClosureLimitPoint_above {ρ : V} [IsOrdinal ρ]
    (htot : MagidorFailureTotal ρ) (β : V) [IsOrdinal β] :
    ∃ lam : V, β ∈ lam ∧ IsMagidorClosureLimitPoint ρ lam := by
  have hGord : ∀ ξ : V, IsOrdinal ξ → IsOrdinal (leastMagidorClosurePoint ρ ξ) :=
    fun ξ hξ ↦ have : IsOrdinal ξ := hξ; leastMagidorClosurePoint_isOrdinal htot ξ
  have hGgt : ∀ ξ : V, IsOrdinal ξ → ξ ∈ leastMagidorClosurePoint ρ ξ :=
    fun ξ hξ ↦ have : IsOrdinal ξ := hξ; mem_leastMagidorClosurePoint htot ξ
  obtain ⟨lam, hβ, hlam⟩ := exists_ordinalClosurePoint_above
    (leastMagidorClosurePoint_definable ρ) hGord hGgt β
  have hord : IsOrdinal lam := hlam.1
  have hlim : IsLimitOrdinal lam := IsOrdinalClosurePoint.limit hGgt hlam
  have hub : ∀ ξ ∈ lam, ∃ d ∈ lam, ξ ∈ d ∧ IsMagidorClosurePoint ρ d := by
    intro ξ hξ
    have : IsOrdinal ξ := IsOrdinal.of_mem hξ
    exact ⟨leastMagidorClosurePoint ρ ξ, hlam.2.2 ξ hξ, mem_leastMagidorClosurePoint htot ξ,
      leastMagidorClosurePoint_isClosurePoint htot ξ⟩
  have hρ : ρ ∈ lam := by
    obtain ⟨ξ, hξ⟩ := hlam.2.1.nonempty
    obtain ⟨d, hdlam, -, hd⟩ := hub ξ hξ
    exact IsOrdinal.toIsTransitive.mem_trans hd.2.1 hdlam
  exact ⟨lam, hβ, hlim, hρ, hub⟩

/-! ### The least closure limit point above a marker -/

/-- `lam` is the least closure limit point above `r`. -/
def IsLeastMagidorClosureLimitPoint (ρ r lam : V) : Prop :=
  r ∈ lam ∧ IsMagidorClosureLimitPoint ρ lam ∧
    ∀ ξ ∈ lam, r ∈ ξ → ¬ IsMagidorClosureLimitPoint ρ ξ

instance isLeastMagidorClosureLimitPoint_definable :
    ℒₛₑₜ-relation₃[V] IsLeastMagidorClosureLimitPoint := by
  unfold IsLeastMagidorClosureLimitPoint
  definability

theorem exists_isLeastMagidorClosureLimitPoint {ρ : V} [IsOrdinal ρ]
    (htot : MagidorFailureTotal ρ) (r : V) [IsOrdinal r] :
    ∃ lam : V, IsLeastMagidorClosureLimitPoint ρ r lam := by
  have hex : ∃ x : V, IsOrdinal x ∧ (r ∈ x ∧ IsMagidorClosureLimitPoint ρ x) := by
    obtain ⟨lam, hr, hlam⟩ := exists_magidorClosureLimitPoint_above htot r
    exact ⟨lam, hlam.1.1, hr, hlam⟩
  obtain ⟨lam, hlam, -⟩ :=
    leastOrdinal_existsUnique (fun x : V ↦ r ∈ x ∧ IsMagidorClosureLimitPoint ρ x)
      (by definability) hex
  refine ⟨lam, hlam.2.1.1, hlam.2.1.2, ?_⟩
  have hlamord : IsOrdinal lam := hlam.1
  intro ξ hξ hrξ hcp
  have hξord : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hsub : lam ⊆ ξ := hlam.2.2 ξ hξord ⟨hrξ, hcp⟩
  exact mem_irrefl ξ (hsub ξ hξ)

theorem isLeastMagidorClosureLimitPoint_functional {ρ r lam₁ lam₂ : V}
    (h₁ : IsLeastMagidorClosureLimitPoint ρ r lam₁)
    (h₂ : IsLeastMagidorClosureLimitPoint ρ r lam₂) : lam₁ = lam₂ := by
  have ho₁ : IsOrdinal lam₁ := h₁.2.1.1.1
  have ho₂ : IsOrdinal lam₂ := h₂.2.1.1.1
  rcases IsOrdinal.mem_trichotomy (α := lam₁) (β := lam₂) with h | h | h
  · exact absurd h₁.2.1 (h₂.2.2 lam₁ h h₁.1)
  · exact h
  · exact absurd h₂.2.1 (h₁.2.2 lam₂ h h₂.1)

end ZFVP
