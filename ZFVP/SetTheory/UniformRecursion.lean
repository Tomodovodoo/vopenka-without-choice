import ZFVP.SetTheory.Hierarchy

/-! Parameter-free formulas for internal recursion and the cumulative hierarchy.
Definability with unspecified parameters alone cannot justify transport between
different elementary models; these formulas are uniform across models. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def recursionAttemptFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  f“α f. !IsOrdinal.dfn α ∧ !IsFunction.dfn f ∧ α = !domain.dfn f ∧
    ∀ β ∈ α, ∀ y, !kpair.dfn β y ∈ f ↔ !φ y (!restrict.dfn f β)”

def transfiniteRecFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “y α. (∃ f, !(recursionAttemptFormula φ) α f ∧ !φ y f) ∨
    (¬!IsOrdinal.dfn α ∧ !isEmpty y)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance recursionAttemptFormula_defined (F : V → V) (φ : SetTheorySemisentence 2)
    [hF : ℒₛₑₜ-function₁ F via φ] :
    ℒₛₑₜ-relation (IsAttempt F) via recursionAttemptFormula φ :=
  ⟨fun v ↦ by simp [recursionAttemptFormula, IsAttempt, eq_comm]⟩

theorem transfiniteRec_eq_iff (F : V → V) (hF : ℒₛₑₜ-function₁ F) (α y : V) :
    y = Replacement.transfiniteRec F hF α ↔
      (∃ f, IsAttempt F α f ∧ y = F f) ∨ (¬IsOrdinal α ∧ y = ∅) := by
  classical
  by_cases hα : IsOrdinal α
  · have : IsOrdinal α := hα
    have hg := Replacement.replAttemptOrEmpty_aux F hF (IsOrdinal.toOrdinal α)
    constructor
    · intro hy
      exact Or.inl ⟨Replacement.replAttemptOrEmpty F hF α, hg, by
        simpa [Replacement.transfiniteRec, hα] using hy⟩
    · rintro (⟨f, hf, hy⟩ | ⟨hn, _⟩)
      · have : IsFunction f := hf.2.1
        have : IsFunction (Replacement.replAttemptOrEmpty F hF α) := hg.2.1
        have heq := IsAttempt.isAttempt_unique hf hg
        simpa [Replacement.transfiniteRec, hα, heq] using hy
      · exact False.elim (hn hα)
  · have hn : ¬∃ f, IsAttempt F α f ∧ y = F f := by
      rintro ⟨f, hf, _⟩
      exact hα hf.1
    simp [Replacement.transfiniteRec, hα, hn]

instance transfiniteRecFormula_defined (F : V → V) (φ : SetTheorySemisentence 2)
    [hF : ℒₛₑₜ-function₁ F via φ] :
    ℒₛₑₜ-function₁ (Replacement.transfiniteRec F hF.to_definable) via
      transfiniteRecFormula φ := ⟨fun v ↦ by
    simp [transfiniteRecFormula, transfiniteRec_eq_iff, isEmpty_iff_eq_empty]⟩

def hierarchyStepFormula : SetTheorySemisentence 2 :=
  f“h f. ∀ x, x ∈ h ↔ ∃ y ∈ !range.dfn f, x ⊆ y”

instance hierarchyStepFormula_defined :
    ℒₛₑₜ-function₁[V] hierarchyStep via hierarchyStepFormula :=
  ⟨fun v ↦ by simp [hierarchyStepFormula, mem_ext_iff (y := hierarchyStep _),
    mem_hierarchyStep_iff]⟩

def hierarchyFormula : SetTheorySemisentence 2 := transfiniteRecFormula hierarchyStepFormula

instance hierarchyFormula_defined : ℒₛₑₜ-function₁[V] hierarchy via hierarchyFormula :=
  transfiniteRecFormula_defined hierarchyStep hierarchyStepFormula

end ZFVP
