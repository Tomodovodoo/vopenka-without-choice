import Mathlib.Order.Preorder.Chain
import Mathlib.SetTheory.Cardinal.Regular
import Foundation.FirstOrder.Basic.Definability

/-! Enayat, Appendix, Lemma A.6: weak specialization gives a uniform definition of
each branch of uncountable cofinality. This is a component of Schmerl's diamond
elimination, not the model-existence or absoluteness theorem.
-/

namespace ZFVP.Schmerl

open Set Order Cardinal LO LO.FirstOrder

universe u v w

/-- In a tree order, two predecessors of the same node are comparable. -/
def IsTreeOrder (T : Type u) [PartialOrder T] : Prop :=
  ∀ ⦃x y z : T⦄, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x

/-- Enayat's weak specialization condition. A monochromatic fork cannot split. -/
def WeaklySpecializes {T : Type u} {C : Type v} (r : T → T → Prop)
    (f : T → C) : Prop :=
  ∀ ⦃x y z⦄, r x y → r x z → f x = f y → f x = f z → r y z ∨ r z y

/-- The cone used in the formula in Lemma A.6. -/
def colorCone {T : Type u} {C : Type v} (r : T → T → Prop) (f : T → C)
    (b x : T) : Prop := r x b ∨ r b x ∧ f b = f x

/-- The downward closure of the monochromatic cone above the parameter. -/
def branchDefinition {T : Type u} {C : Type v} (r : T → T → Prop) (f : T → C)
    (b x : T) : Prop := ∃ y, colorCone r f b y ∧ r x y

/-- A countable coloring of an order of uncountable cofinality has a cofinal fiber. -/
theorem exists_cofinal_fiber {I C : Type u} [LinearOrder I] [Countable C]
    (hI : Cardinal.aleph0 < Order.cof I) (f : I → C) :
    ∃ c, IsCofinal {i | f i = c} := by
  apply isCofinal_of_isCofinal_iUnion
  · intro i
    exact ⟨i, Set.mem_iUnion.mpr ⟨f i, rfl⟩, le_rfl⟩
  · exact Cardinal.mk_le_aleph0.trans_lt hI

section Tree

variable {T : Type u} [PartialOrder T]

/-- A node comparable with every member of a maximal chain lies on that chain. -/
theorem mem_of_comparable {B : Set T} (hB : IsMaxChain (· ≤ ·) B) {x : T}
    (hx : ∀ y ∈ B, x ≤ y ∨ y ≤ x) : x ∈ B := by
  have heq := hB.2 (hB.1.insert (fun y hy _ ↦ hx y hy)) (Set.subset_insert x B)
  rw [heq]
  exact Set.mem_insert x B

/-- Maximal chains in a tree are downward closed. -/
theorem branch_downward_closed (hT : IsTreeOrder T) {B : Set T}
    (hB : IsMaxChain (· ≤ ·) B) {x y : T} (hy : y ∈ B) (hxy : x ≤ y) : x ∈ B := by
  apply mem_of_comparable hB
  intro z hz
  rcases hB.1.total hy hz with hyz | hzy
  · exact Or.inl (hxy.trans hyz)
  · exact hT hxy hzy

/-- Every monochromatic cone is a chain. -/
theorem colorCone_isChain {C : Type v} (hT : IsTreeOrder T) {f : T → C}
    (hf : WeaklySpecializes (· ≤ ·) f) (b : T) :
    IsChain (· ≤ ·) {x | colorCone (· ≤ ·) f b x} := by
  intro x hx y hy _
  rcases hx with hx | ⟨hbx, hfx⟩ <;> rcases hy with hy | ⟨hby, hfy⟩
  · exact hT hx hy
  · exact Or.inl (hx.trans hby)
  · exact Or.inr (hy.trans hbx)
  · exact hf hbx hby hfx hfy

/-- Downward closure preserves chains in a tree. -/
theorem downwardClosure_isChain (hT : IsTreeOrder T) {A : Set T}
    (hA : IsChain (· ≤ ·) A) : IsChain (· ≤ ·) {x | ∃ y ∈ A, x ≤ y} := by
  rintro x ⟨a, ha, hxa⟩ y ⟨b, hb, hyb⟩ _
  rcases hA.total ha hb with hab | hba
  · exact hT (hxa.trans hab) hyb
  · exact hT hxa (hyb.trans hba)

/-- The formula in Lemma A.6 defines a chain for every node parameter. -/
theorem branchDefinition_isChain {C : Type v} (hT : IsTreeOrder T) {f : T → C}
    (hf : WeaklySpecializes (· ≤ ·) f) (b : T) :
    IsChain (· ≤ ·) {x | branchDefinition (· ≤ ·) f b x} :=
  downwardClosure_isChain hT (colorCone_isChain hT hf b)

/-- A cofinal monochromatic subset of a branch identifies the parameter defining that branch. -/
theorem branchDefinition_eq_of_cofinal_color {C : Type v} (hT : IsTreeOrder T)
    {f : T → C} (hf : WeaklySpecializes (· ≤ ·) f) {B : Set T}
    (hB : IsMaxChain (· ≤ ·) B) {b : T} (_hb : b ∈ B)
    (hcof : ∀ x ∈ B, ∃ y ∈ B, x ≤ y ∧ b ≤ y ∧ f b = f y) :
    ∀ x, branchDefinition (· ≤ ·) f b x ↔ x ∈ B := by
  have hsub : B ⊆ {x | branchDefinition (· ≤ ·) f b x} := by
    intro x hx
    obtain ⟨y, _, hxy, hby, hfy⟩ := hcof x hx
    exact ⟨y, Or.inr ⟨hby, hfy⟩, hxy⟩
  have heq := hB.2 (branchDefinition_isChain hT hf b) hsub
  intro x
  exact Set.ext_iff.mp heq.symm x

/-- Lemma A.6 for a branch equipped with a monotone cofinal chain. The only
cardinal assumption is uncountable cofinality of the index order. -/
theorem exists_branchDefinition {I C : Type v} [LinearOrder I] [Nonempty I] [Countable C]
    (hI : Cardinal.aleph0 < Order.cof I) (hT : IsTreeOrder T) {f : T → C}
    (hf : WeaklySpecializes (· ≤ ·) f) {B : Set T} (hB : IsMaxChain (· ≤ ·) B)
    (p : I → T) (hp : ∀ i, p i ∈ B) (hmono : Monotone p)
    (hcof : ∀ x ∈ B, ∃ i, x ≤ p i) :
    ∃ b ∈ B, ∀ x, branchDefinition (· ≤ ·) f b x ↔ x ∈ B := by
  obtain ⟨c, hc⟩ := exists_cofinal_fiber hI (f ∘ p)
  obtain ⟨i₀, hi₀, _⟩ := hc (Classical.arbitrary I)
  refine ⟨p i₀, hp i₀, branchDefinition_eq_of_cofinal_color hT hf hB (hp i₀) ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hcof x hx
  obtain ⟨j, hj, hij⟩ := hc (max i i₀)
  exact ⟨p j, hp j, hi.trans (hmono ((le_max_left i i₀).trans hij)),
    hmono ((le_max_right i i₀).trans hij), hi₀.trans hj.symm⟩

/-- The precise omega-one instance used in Schmerl's construction. -/
theorem exists_branchDefinition_omegaOne (hT : IsTreeOrder T) {f : T → ℕ}
    (hf : WeaklySpecializes (· ≤ ·) f) {B : Set T} (hB : IsMaxChain (· ≤ ·) B)
    (p : Ordinal.ToType (Ordinal.omega.{0} 1) → T) (hp : ∀ i, p i ∈ B)
    (hmono : Monotone p) (hcof : ∀ x ∈ B, ∃ i, x ≤ p i) :
    ∃ b ∈ B, ∀ x, branchDefinition (· ≤ ·) f b x ↔ x ∈ B := by
  let : Nonempty (Ordinal.ToType (Ordinal.omega.{0} 1)) :=
    Ordinal.nonempty_toType_iff.mpr (Ordinal.omega_pos 1).ne'
  apply exists_branchDefinition (p := p) _ hT hf hB hp hmono hcof
  rw [Ordinal.cof_toType, Cardinal.cof_omega_one]
  exact Cardinal.aleph0_lt_aleph_one

end Tree

section Definability

variable {L : Language.{w}} {T : Type u} [L.Eq] [Structure L T]
  [Structure.Eq L T] {C : Type v}

/-- The displayed branch definition is first order when the order and the equality
of colors are first-order definable in the expanded structure. -/
theorem branchDefinition_definable (r : T → T → Prop) (f : T → C)
    [L-relation[T] r] [L-relation[T] (fun x y ↦ f x = f y)] (b : T) :
    L-predicate[T] (branchDefinition r f b) := by
  unfold branchDefinition colorCone
  apply Language.Definable.exs
  apply Language.Definable.and
  · apply Language.Definable.or
    · definability
    · apply Language.Definable.and
      · definability
      · exact Language.DefinableRel.comp (P := fun x y ↦ f x = f y)
          (by definability) (by definability)
  · definability

end Definability

end ZFVP.Schmerl
