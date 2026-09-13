import ZFVP.SetTheory.ClassForcingCongruence
import ZFVP.SetTheory.ForcingBoundedQuantifiers
import ZFVP.SetTheory.BoundedFormulas

/-! The bounded-quantifier forcing clauses for external formulas and finite assignments. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingAtomic_boundedGuard (P R : V) {n : ℕ} (t : SetTheorySemiterm Empty n)
    (v : Fin n → V) (x : V) :
    forcingAtomic P R Language.Set.Rel.mem ![.bvar 0, Rew.bShift t] (standardTuple (x :> v)) =
      atomicMembership P R x (forcingTermValue t (standardTuple v)) := by
  cases t with
  | bvar i =>
    simp [forcingAtomic, forcingTermValue, value_standardTuple]
    exact congrArg₂ (atomicMembership P R) (value_standardTuple (x :> v) 0)
      (value_standardTuple (x :> v) i.succ)
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

theorem classForcingFormula_section_definable (P R : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    ℒₛₑₜ-function₁[V] (fun x ↦ classForcingFormula P R N hN φ (standardTuple (x :> v))) := by
  change ℒₛₑₜ-function₁[V] (fun x ↦ classForcingFormula P R N hN φ (assignmentPrepend (n : V) (standardTuple v) x))
  definability

theorem classForcingFormula_boundedExs_eq (P R : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    {n : ℕ} (t : SetTheorySemiterm Empty n) (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    classForcingFormula P R N hN (boundedSetExs t φ) (standardTuple v) =
      forcingExistential P R N hN (fun x ↦ atomicMembership P R x (forcingTermValue t (standardTuple v)) ∩
        classForcingFormula P R N hN φ (standardTuple (x :> v))) (by
          have := classForcingFormula_section_definable P R N hN φ v
          definability) := by
  rw [boundedSetExs, classForcingFormula_exs]
  congr 1
  funext x
  change classForcingFormula P R N hN (.and (.rel _ _) φ) (standardTuple (x :> v)) = _
  rw [classForcingFormula_and, classForcingFormula_rel, forcingAtomic_boundedGuard]

theorem classForcingFormula_boundedAll_eq (P R : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    {n : ℕ} (t : SetTheorySemiterm Empty n) (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    classForcingFormula P R N hN (boundedSetAll t φ) (standardTuple v) =
      forcingClassIntersection P N hN (fun x ↦ forcingClosure P R
        (forcingNegation P R (atomicMembership P R x (forcingTermValue t (standardTuple v))) ∪
          classForcingFormula P R N hN φ (standardTuple (x :> v)))) (by
            have := classForcingFormula_section_definable P R N hN φ v
            definability) := by
  rw [boundedSetAll, classForcingFormula_all]
  congr 1
  funext x
  change classForcingFormula P R N hN (.or (.nrel _ _) φ) (standardTuple (x :> v)) = _
  rw [classForcingFormula_or, classForcingFormula_nrel, forcingAtomic_boundedGuard]

theorem classForcingFormula_section_congr {P R : V} (hR : IsForcingPreorder P R)
    (N : V → Prop) (hN : ℒₛₑₜ-predicate N) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → V) (x y p : V) (hp : p ∈ P) (he : p ∈ atomicEquality P R x y) :
    p ∈ classForcingFormula P R N hN φ (standardTuple (x :> v)) ↔
      p ∈ classForcingFormula P R N hN φ (standardTuple (y :> v)) := by
  apply classForcingFormula_congr hR N hN φ _ _ hp
  intro i
  refine Fin.cases he (fun j ↦ ?_) i
  change p ∈ atomicEquality P R (v j) (v j)
  rw [atomicEquality_refl hR]
  exact hp

theorem classForcingFormula_boundedExs_iff {P R : V} (hR : IsForcingPreorder P R)
    (N : V → Prop) (hN : ℒₛₑₜ-predicate N) {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V)
    (ht : IsForcingName P (forcingTermValue t (standardTuple v)))
    (hsub : ∀ υ s, ⟨υ, s⟩ₖ ∈ forcingTermValue t (standardTuple v) → N υ) (p : V) :
    p ∈ classForcingFormula P R N hN (boundedSetExs t φ) (standardTuple v) ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        ∃ υ s, ⟨υ, s⟩ₖ ∈ forcingTermValue t (standardTuple v) ∧ ⟨r, s⟩ₖ ∈ R ∧
          r ∈ classForcingFormula P R N hN φ (standardTuple (υ :> v)) := by
  rw [classForcingFormula_boundedExs_eq]
  exact forcingBoundedExistential_iff hR N hN _ (classForcingFormula_section_definable P R N hN φ v)
    ht hsub (fun x ↦ classForcingFormula_regular N hN hR φ _)
      (fun x y r ↦ classForcingFormula_section_congr hR N hN φ v x y r)

theorem classForcingFormula_boundedAll_iff {P R : V} (hR : IsForcingPreorder P R)
    (N : V → Prop) (hN : ℒₛₑₜ-predicate N) {n : ℕ} (t : SetTheorySemiterm Empty n)
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V)
    (ht : IsForcingName P (forcingTermValue t (standardTuple v)))
    (hsub : ∀ υ s, ⟨υ, s⟩ₖ ∈ forcingTermValue t (standardTuple v) → N υ) (p : V) :
    p ∈ classForcingFormula P R N hN (boundedSetAll t φ) (standardTuple v) ↔
      p ∈ P ∧ ∀ υ s, ⟨υ, s⟩ₖ ∈ forcingTermValue t (standardTuple v) → ∀ q ∈ P,
        ⟨q, p⟩ₖ ∈ R → ⟨q, s⟩ₖ ∈ R →
          q ∈ classForcingFormula P R N hN φ (standardTuple (υ :> v)) := by
  rw [classForcingFormula_boundedAll_eq]
  exact forcingBoundedUniversal_iff hR N hN _ (classForcingFormula_section_definable P R N hN φ v)
    ht hsub (fun x ↦ classForcingFormula_regular N hN hR φ _)
      (fun x y r ↦ classForcingFormula_section_congr hR N hN φ v x y r)

end ZFVP
