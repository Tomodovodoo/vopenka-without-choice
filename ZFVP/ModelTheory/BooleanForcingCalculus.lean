import ZFVP.SetTheory.ForcingNegationCalculus
import ZFVP.SetTheory.GenericNameSeparative
import ZFVP.ModelTheory.BooleanValues

/-! Closure rules for the forcing relation that the rest of the calculus did not yet have.

The library already proves monotonicity (`forcingFormula_mono`), modus ponens
(`forcingFormula_imp_mp`), the conjunction rules (`forcingFormula_and_intro`,
`forcingFormula_and_elim`), the negation equation (`forcingFormula_neg` and
`mem_forcingFormula_neg_iff`), universal instantiation (`forcingFormula_all_elim`), existential
introduction (`forcingFormula_exs_intro`), the dense form of the existential
(`forcingFormula_exs_dense_iff`), and the two directions of localization over generic filters
(`forcingFormula_iff_all_generics`). The density rule is the third clause of
`forcingFormula_regular`: a condition whose extensions forcing `φ` are dense below it forces `φ`.

Added here: the dense reading of a disjunction, disjunction introduction and elimination,
implication introduction (the deduction rule), universal generalization, the fact that a condition
never forces both a formula and its negation, the rule that a condition failing to force `∼φ` has
an extension forcing `φ`, that the conditions deciding `φ` are dense, and `∼∼φ` has the same
forcing set as `φ`. All of it is stated for `forcingFormula P R` over an arbitrary forcing
preorder, so it applies to the Boolean completion `booleanConditions P R` with `booleanOrder P R`
through `(booleanOrder_poset P R).1`; the last two results draw that consequence for the Boolean
value `‖φ‖` of `ForcingContext.booleanValue`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Disjunction -/

/-- A condition forces `φ ⋎ ψ` exactly when the conditions forcing one of the two disjuncts are
dense below it. -/
theorem forcingFormula_or_dense_iff {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    (φ ψ : SetTheorySemisentence n) (b p : V) :
    p ∈ forcingFormula P R (φ ⋎ ψ) b ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        (r ∈ forcingFormula P R φ b ∨ r ∈ forcingFormula P R ψ b) := by
  show p ∈ forcingFormula P R (.or φ ψ) b ↔ _
  rw [forcingFormula_or, mem_forcingClosure_iff]
  apply and_congr Iff.rfl
  refine forall_congr' fun q ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ ?_
  constructor
  · rintro ⟨r, hr, hrq⟩
    rcases mem_union_iff.mp hr with h | h
    · exact ⟨r, (forcingFormula_regular hR φ b).1 r h, hrq, Or.inl h⟩
    · exact ⟨r, (forcingFormula_regular hR ψ b).1 r h, hrq, Or.inr h⟩
  · rintro ⟨r, _, hrq, h⟩
    exact ⟨r, mem_union_iff.mpr h, hrq⟩

/-- Left disjunction introduction. -/
theorem forcingFormula_or_intro_left {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    {φ ψ : SetTheorySemisentence n} {b p : V} (h : p ∈ forcingFormula P R φ b) :
    p ∈ forcingFormula P R (φ ⋎ ψ) b := by
  have hp : p ∈ P := (forcingFormula_regular hR φ b).1 p h
  rw [forcingFormula_or_dense_iff hR]
  exact ⟨hp, fun q hq hqp ↦ ⟨q, hq, hR.2.1 q hq, Or.inl (forcingFormula_mono hR h hq hqp)⟩⟩

/-- Right disjunction introduction. -/
theorem forcingFormula_or_intro_right {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    {φ ψ : SetTheorySemisentence n} {b p : V} (h : p ∈ forcingFormula P R ψ b) :
    p ∈ forcingFormula P R (φ ⋎ ψ) b := by
  have hp : p ∈ P := (forcingFormula_regular hR ψ b).1 p h
  rw [forcingFormula_or_dense_iff hR]
  exact ⟨hp, fun q hq hqp ↦ ⟨q, hq, hR.2.1 q hq, Or.inr (forcingFormula_mono hR h hq hqp)⟩⟩

/-! ### Negation -/

/-- A condition that does not force `∼φ` has an extension forcing `φ`. -/
theorem exists_forces_of_not_forces_neg {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    {φ : SetTheorySemisentence n} {b q : V} (hq : q ∈ P)
    (hqn : q ∉ forcingFormula P R (∼φ) b) :
    ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ r ∈ forcingFormula P R φ b := by
  by_contra hcon
  exact hqn ((mem_forcingFormula_neg_iff hR φ b q).mpr
    ⟨hq, fun s hs hsq hsφ ↦ hcon ⟨s, hs, hsq, hsφ⟩⟩)

/-- No condition forces both a formula and its negation. -/
theorem forcingFormula_not_both {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    {φ : SetTheorySemisentence n} {b p : V} (hφ : p ∈ forcingFormula P R φ b)
    (hnφ : p ∈ forcingFormula P R (∼φ) b) : False := by
  obtain ⟨hp, hh⟩ := (mem_forcingFormula_neg_iff hR φ b p).mp hnφ
  exact hh p hp (hR.2.1 p hp) hφ

/-- Below any condition, the conditions deciding `φ` are dense. -/
theorem forcingFormula_decide_dense {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    (φ : SetTheorySemisentence n) (b : V) {q : V} (hq : q ∈ P) :
    ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
      (r ∈ forcingFormula P R φ b ∨ r ∈ forcingFormula P R (∼φ) b) := by
  by_cases hqn : q ∈ forcingFormula P R (∼φ) b
  · exact ⟨q, hq, hR.2.1 q hq, Or.inr hqn⟩
  · obtain ⟨r, hr, hrq, hrφ⟩ := exists_forces_of_not_forces_neg hR hq hqn
    exact ⟨r, hr, hrq, Or.inl hrφ⟩

/-- Double negation does not change the forcing set. -/
theorem forcingFormula_neg_neg {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    (φ : SetTheorySemisentence n) (b : V) :
    forcingFormula P R (∼∼φ) b = forcingFormula P R φ b := by
  rw [forcingFormula_neg hR, forcingFormula_neg hR,
    forcingNegation_negation hR (forcingFormula_regular hR φ b)]

/-! ### Implication -/

/-- The deduction rule: a condition forces `φ 🡒 ψ` as soon as every extension of it that forces
`φ` forces `ψ`. -/
theorem forcingFormula_imp_intro {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    {φ ψ : SetTheorySemisentence n} {b p : V} (hp : p ∈ P)
    (h : ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → q ∈ forcingFormula P R φ b → q ∈ forcingFormula P R ψ b) :
    p ∈ forcingFormula P R (φ 🡒 ψ) b := by
  show p ∈ forcingFormula P R ((∼φ) ⋎ ψ) b
  rw [forcingFormula_or_dense_iff hR]
  refine ⟨hp, fun q hq hqp ↦ ?_⟩
  by_cases hqn : q ∈ forcingFormula P R (∼φ) b
  · exact ⟨q, hq, hR.2.1 q hq, Or.inl hqn⟩
  · obtain ⟨s, hs, hsq, hsφ⟩ := exists_forces_of_not_forces_neg hR hq hqn
    exact ⟨s, hs, hsq, Or.inr (h s hs (hR.2.2 s hs q hq p hp hsq hqp) hsφ)⟩

/-! ### Disjunction elimination -/

/-- Disjunction elimination: from `φ ⋎ ψ` and the two implications into `χ`, the condition
forces `χ`. -/
theorem forcingFormula_or_elim {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    {φ ψ χ : SetTheorySemisentence n} {b p : V}
    (hor : p ∈ forcingFormula P R (φ ⋎ ψ) b)
    (h₁ : p ∈ forcingFormula P R (φ 🡒 χ) b)
    (h₂ : p ∈ forcingFormula P R (ψ 🡒 χ) b) :
    p ∈ forcingFormula P R χ b := by
  obtain ⟨hp, hd⟩ := (forcingFormula_or_dense_iff hR φ ψ b p).mp hor
  refine (forcingFormula_regular hR χ b).2.2 p hp fun q hq hqp ↦ ?_
  obtain ⟨r, hr, hrq, hcase⟩ := hd q hq hqp
  have hrp : ⟨r, p⟩ₖ ∈ R := hR.2.2 r hr q hq p hp hrq hqp
  rcases hcase with h | h
  · exact ⟨r, forcingFormula_imp_mp hR (forcingFormula_mono hR h₁ hr hrp) h, hrq⟩
  · exact ⟨r, forcingFormula_imp_mp hR (forcingFormula_mono hR h₂ hr hrp) h, hrq⟩

/-! ### Universal generalization -/

/-- Universal generalization: a condition forcing `φ(ν)` for every name `ν` forces `∀ x, φ(x)`. -/
theorem forcingFormula_all_intro {P R : V} {n : ℕ} {φ : SetTheorySemisentence (n + 1)} {b p : V}
    (hp : p ∈ P)
    (h : ∀ ν, IsForcingName P ν → p ∈ forcingFormula P R φ (assignmentPrepend (n : V) b ν)) :
    p ∈ forcingFormula P R (.all φ) b := by
  rw [forcingFormula_all, mem_forcingClassIntersection_iff]
  exact ⟨hp, h⟩

/-! ### Localization over generic filters -/

/-- Localization, easy direction: a condition forcing `φ` makes `φ` true in the extension by any
generic filter containing it. The library's `forcingFormula_iff_all_generics` has both directions
but assumes `[Countable V]`, which is needed only for the converse, to produce generic filters.
This direction needs no such assumption. -/
theorem forcingFormula_truth_of_mem_generic {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → ForcingName P)
    (h : p ∈ forcingFormula P R φ (standardTuple (fun i ↦ (v i).val)))
    (G : Set V) (hG : IsExternalForcingGeneric P R G) (hpG : p ∈ G) :
    φ.Evalb (fun i ↦ (ForcingContext.mk P R one G hR htop hG).ofName (v i)) :=
  ((ForcingContext.mk P R one G hR htop hG).formula_truth φ v).mpr ⟨p, hpG, h⟩

/-! ### Consequences for the Boolean value -/

namespace ForcingContext

/-- If every condition of the Boolean completion forcing `φ` also forces `ψ`, then the Boolean
value of `φ` is below that of `ψ`. -/
theorem booleanValue_subset_of_forces_subset (A : ForcingContext V) {n : ℕ}
    {φ ψ : SetTheorySemisentence n} {v : Fin n → V}
    (h : forcingFormula (booleanConditions A.P A.R) (booleanOrder A.P A.R) φ (standardTuple v) ⊆
      forcingFormula (booleanConditions A.P A.R) (booleanOrder A.P A.R) ψ (standardTuple v)) :
    A.booleanValue φ v ⊆ A.booleanValue ψ v :=
  regularJoin_mono h

/-- Modus ponens at the level of Boolean values: the value of `φ ⋏ (φ 🡒 ψ)` is below the value
of `ψ`. -/
theorem booleanValue_imp_subset (A : ForcingContext V) {n : ℕ}
    (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    A.booleanValue (φ ⋏ (φ 🡒 ψ)) v ⊆ A.booleanValue ψ v := by
  refine A.booleanValue_subset_of_forces_subset (fun q hq ↦ ?_)
  obtain ⟨hφ, himp⟩ := forcingFormula_and_elim hq
  exact forcingFormula_imp_mp (booleanOrder_poset A.P A.R).1 himp hφ

end ForcingContext

end ZFVP
