import ZFVP.ModelTheory.ConservativeExtension
import ZFVP.SetTheory.Collection

/-! Amenability means full Separation and Replacement in the language with
one additional unary predicate. All formulas may carry finitely many parameters. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

inductive PredicateRelation : ℕ → Type where
  | predicate : PredicateRelation 1

def predicateExtraLanguage : Language := ⟨fun _ ↦ Empty, PredicateRelation⟩
def predicateLanguage : Language := Language.add ℒₛₑₜ predicateExtraLanguage
def predicateSetEmbedding : ℒₛₑₜ →ᵥ predicateLanguage := Language.Hom.add₁ _ _

@[instance_reducible] def predicateExpansion {V : Type*} [SetStructure V]
    (X : V → Prop) : Structure predicateLanguage V where
  func := fun {_} f a ↦ match f with
    | .inl f => Structure.func f a
    | .inr f => Empty.elim f
  rel := fun {_} r a ↦ match r with
    | .inl r => Structure.rel r a
    | .inr r => match r with | .predicate => X (a 0)

namespace PredicateExpansion
variable {V : Type*} [SetStructure V] (X : V → Prop)
abbrev Definable {n : ℕ} (P : (Fin n → V) → Prop) :=
  @Language.Definable predicateLanguage V (predicateExpansion X) n P
abbrev Pred (P : V → Prop) := Definable X (fun v : Fin 1 → V ↦ P (v 0))
abbrev Rel (P : V → V → Prop) := Definable X (fun v : Fin 2 → V ↦ P (v 0) (v 1))
abbrev Fun (F : V → V) := Definable X (fun v : Fin 2 → V ↦ v 0 = F (v 1))

theorem base {n : ℕ} (P : (Fin n → V) → Prop) [h : Language.Definable ℒₛₑₜ P] : Definable X P := by
  let : Structure predicateLanguage V := predicateExpansion X
  obtain ⟨φ, hφ⟩ := h.definable
  refine ⟨Semiformula.lMap predicateSetEmbedding φ, fun v ↦ ?_⟩
  exact Semiformula.eval_lMap.trans (hφ v)

instance predicate : Pred X X := by
  let : Structure predicateLanguage V := predicateExpansion X
  refine ⟨.rel (.inr PredicateRelation.predicate) ![.bvar 0], fun v ↦ ?_⟩
  rfl
end PredicateExpansion

/-- The extra schemes of ZF(X). The reduct is required separately to model
ZF, so the unchanged non-schematic axioms are already present. -/
structure IsAmenablePredicate {V : Type*} [SetStructure V] (X : V → Prop) : Prop where
  separation : ∀ (P : V → Prop), PredicateExpansion.Pred X P →
    ∀ a : V, ∃ b : V, ∀ x : V, x ∈ b ↔ x ∈ a ∧ P x
  replacement : ∀ (R : V → V → Prop), PredicateExpansion.Rel X R →
    (∀ x : V, ∃! y : V, R x y) →
    ∀ a : V, ∃ b : V, ∀ y : V, y ∈ b ↔ ∃ x ∈ a, R x y

namespace IsAmenablePredicate
variable {V : Type*} [SetStructure V] {X : V → Prop}
theorem isClass (h : IsAmenablePredicate X) : IsClass V X :=
  h.separation X (PredicateExpansion.predicate X)
end IsAmenablePredicate

/-- Enayat Definition 2.4(d), restricted to membership end extensions. -/
def MembershipEndExtension.IsFaithful {V W : Type*} [SetStructure V] [SetStructure W]
    (j : MembershipEndExtension V W) : Prop :=
  ∀ D : W → Prop, (ℒₛₑₜ-predicate[W] D) → IsAmenablePredicate (fun x ↦ D (j x))

end ZFVP
