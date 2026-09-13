import ZFVP.ModelTheory.CodedZFModel
import ZFVP.ModelTheory.BinaryRelationZFModel
import ZFVP.SetTheory.FiniteDictionary
import ZFVP.SetTheory.ForcingOrder
import ZFVP.SetTheory.HartogsDictionary
import ZFVP.ModelTheory.SchmerlInternalCodedHullClosure
import Mathlib.Tactic.FinCases

/-! First-order source conditions for the internal Schmerl construction.
Definitions use internal syntax, parameter tuples, sets, and countability. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def codedSatisfies (M n φ b : V) : Prop := Satisfies membershipLanguageCode ∅ M ∅ n φ b

instance codedSatisfies_definable : ℒₛₑₜ-relation₄[V] codedSatisfies := by
  let : ℒₛₑₜ-function₄[V] satisfactionGraph := satisfactionGraphFormula_defined.to_definable
  unfold codedSatisfies Satisfies
  definability

def codedUnary (M φ x : V) : Prop := codedSatisfies M 1 φ (standardTuple ![x])

def codedBinary (M φ x y : V) : Prop := codedSatisfies M 2 φ (standardTuple ![x, y])

instance codedUnary_definable : ℒₛₑₜ-relation₃[V] codedUnary := by
  unfold codedUnary
  simp only [standardTuple, Matrix.cons_val_zero]
  definability

instance codedBinary_definable : ℒₛₑₜ-relation₄[V] codedBinary := by
  unfold codedBinary
  simp only [standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ]
  definability

/-- The represented membership relation, with no identification with ambient membership. -/
def codedMember (M x a : V) : Prop :=
  codedBinary M (encodeMembershipFormula (“x a. x ∈ a” : SetTheorySemisentence 2)) x a

instance codedMember_definable : ℒₛₑₜ-relation₃[V] codedMember := by unfold codedMember; definability

noncomputable def codedMemberTrace (M a : V) : V := {x ∈ structureDomain M ; codedMember M x a}

theorem mem_codedMemberTrace (M a x : V) :
    x ∈ codedMemberTrace M a ↔ x ∈ structureDomain M ∧ codedMember M x a := mem_sep_iff

instance codedMemberTrace_definable : ℒₛₑₜ-function₂[V] codedMemberTrace := by
  have h : ℒₛₑₜ-relation₃[V] (fun T M a ↦ ∀ x, x ∈ T ↔ x ∈ structureDomain M ∧ codedMember M x a) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_codedMemberTrace]
  rfl

/-- Every set called finite by the coded model has an ambient internally countable trace. -/
def IsCodedFinSmall (M : V) : Prop := ∀ a ∈ structureDomain M,
  codedUnary M (encodeMembershipFormula internallyFiniteFormula) a → IsInternallyCountable (codedMemberTrace M a)

instance isCodedFinSmall_definable : ℒₛₑₜ-predicate[V] IsCodedFinSmall := by
  unfold IsCodedFinSmall
  definability

/-- A definition may use any internal formula and any internally finite tuple of parameters. -/
def IsCodedDefinableSet (M A : V) : Prop := A ⊆ structureDomain M ∧
  ∃ n ∈ (ω : V), ∃ φ ∈ formulaSet membershipLanguageCode ∅ (succ n),
    ∃ b ∈ structureDomain M ^ n, ∀ x ∈ structureDomain M,
      x ∈ A ↔ codedSatisfies M (succ n) φ (assignmentPrepend n b x)

def IsCodedDefinableRelation (M R : V) : Prop := R ⊆ structureDomain M ×ˢ structureDomain M ∧
  ∃ n ∈ (ω : V), ∃ φ ∈ formulaSet membershipLanguageCode ∅ (succ (succ n)),
    ∃ b ∈ structureDomain M ^ n, ∀ x ∈ structureDomain M, ∀ y ∈ structureDomain M,
      ⟨x, y⟩ₖ ∈ R ↔ codedSatisfies M (succ (succ n)) φ
        (assignmentPrepend (succ n) (assignmentPrepend n b y) x)

instance isCodedDefinableSet_definable : ℒₛₑₜ-relation[V] IsCodedDefinableSet := by
  unfold IsCodedDefinableSet
  definability

instance isCodedDefinableRelation_definable : ℒₛₑₜ-relation[V] IsCodedDefinableRelation := by
  unfold IsCodedDefinableRelation
  definability

def IsInternalDirectedNoMax (P R : V) : Prop := IsNonempty P ∧
  (∀ x ∈ P, ∀ y ∈ P, ∃ z ∈ P, ⟨x, z⟩ₖ ∈ R ∧ ⟨y, z⟩ₖ ∈ R) ∧
  ¬∃ m ∈ P, ∀ x ∈ P, ⟨x, m⟩ₖ ∈ R

def IsInternalCofinalStrictChain (κ P R c : V) : Prop := c ∈ P ^ κ ∧
  (∀ i ∈ κ, ∀ j ∈ κ, i ∈ j → ⟨c ‘ i, c ‘ j⟩ₖ ∈ R ∧ c ‘ i ≠ c ‘ j) ∧
  ∀ x ∈ P, ∃ i ∈ κ, ⟨x, c ‘ i⟩ₖ ∈ R

/-- Compatibility uses common upper bounds, as in the corrected Rubin clause. -/
def IsInternalMaximallyCompatible (P R F : V) : Prop := F ⊆ P ∧
  (∀ x ∈ F, ∀ y ∈ F, ∃ z ∈ F, ⟨x, z⟩ₖ ∈ R ∧ ⟨y, z⟩ₖ ∈ R) ∧
  ∀ q ∈ P, (∀ p ∈ F, ∃ z ∈ P, ⟨p, z⟩ₖ ∈ R ∧ ⟨q, z⟩ₖ ∈ R) → q ∈ F

instance isInternalDirectedNoMax_definable : ℒₛₑₜ-relation[V] IsInternalDirectedNoMax := by
  unfold IsInternalDirectedNoMax; definability

instance isInternalCofinalStrictChain_definable : ℒₛₑₜ-relation₄[V] IsInternalCofinalStrictChain := by
  unfold IsInternalCofinalStrictChain; definability

instance isInternalMaximallyCompatible_definable : ℒₛₑₜ-relation₃[V] IsInternalMaximallyCompatible := by
  unfold IsInternalMaximallyCompatible; definability

/-- Rubin's two corrected clauses, fully reified inside the ambient model. -/
def IsCodedRubin (M κ : V) : Prop :=
  (∀ P R, IsCodedDefinableSet M P → IsCodedDefinableRelation M R →
    IsForcingPoset P R → IsInternalDirectedNoMax P R → ∃ c, IsInternalCofinalStrictChain κ P R c) ∧
  (∀ P R, IsCodedDefinableSet M P → IsCodedDefinableRelation M R → IsForcingPoset P R →
    ∀ F, IsInternalMaximallyCompatible P R F →
      (∃ c, IsInternalCofinalStrictChain κ F R c) → IsCodedDefinableSet M F)

instance isCodedRubin_definable : ℒₛₑₜ-relation[V] IsCodedRubin := by unfold IsCodedRubin; definability

/-- The exact source target. Its existence is a separate construction obligation. -/
def IsCodedRubinFinSmallSource (M : V) : Prop :=
  (∃ D E, M = binaryRelationStructureCode D E ∧ E ⊆ D ×ˢ D) ∧ IsCodedZFModel M ∧
  structureDomain M ≤# hartogsNumber (ω : V) ∧
  IsCodedRubin M (hartogsNumber (ω : V)) ∧ IsCodedFinSmall M

instance isCodedRubinFinSmallSource_definable : ℒₛₑₜ-predicate[V] IsCodedRubinFinSmallSource := by
  unfold IsCodedRubinFinSmallSource
  definability

theorem codedMember_binary_iff {D E x a : V} (hD : IsNonempty D) (hx : x ∈ D) (ha : a ∈ D) :
    codedMember (binaryRelationStructureCode D E) x a ↔ ⟨x, a⟩ₖ ∈ E := by
  have h := satisfies_encodeBinaryRelationFormula hD (“x a. x ∈ a” : SetTheorySemisentence 2)
    (![⟨x, hx⟩, ⟨a, ha⟩] : Fin 2 → BinaryRelationDomain D E)
  have he : (fun i ↦ ((![⟨x, hx⟩, ⟨a, ha⟩] : Fin 2 → BinaryRelationDomain D E) i).val) = ![x, a] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  change codedMember (binaryRelationStructureCode D E) x a ↔ ⟨x, a⟩ₖ ∈ E at h
  exact h

theorem codedMemberTrace_binary_iff {D E a x : V} (hD : IsNonempty D) (ha : a ∈ D) :
    x ∈ codedMemberTrace (binaryRelationStructureCode D E) a ↔ x ∈ D ∧ ⟨x, a⟩ₖ ∈ E := by
  rw [mem_codedMemberTrace, binaryRelationStructureCode_domain]
  exact and_congr_right (fun hx ↦ codedMember_binary_iff hD hx ha)

theorem codedUnary_finite_iff {D E : V} (hD : IsNonempty D)
    [Nonempty (BinaryRelationDomain D E)] [(BinaryRelationDomain D E)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (a : BinaryRelationDomain D E) :
    codedUnary (binaryRelationStructureCode D E) (encodeMembershipFormula internallyFiniteFormula) a.val ↔
      IsInternallyFinite a := by
  have h := satisfies_encodeBinaryRelationFormula hD internallyFiniteFormula ![a]
  have he : (fun i ↦ ((![a] : Fin 1 → BinaryRelationDomain D E) i).val) = ![a.val] := by
    funext i
    fin_cases i
    rfl
  rw [he] at h
  simpa [codedUnary, codedSatisfies] using h

end ZFVP.Schmerl
