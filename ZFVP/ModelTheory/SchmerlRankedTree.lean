import ZFVP.ModelTheory.SchmerlWeakSpecialization

/-! Ranked trees and the complete ranked-tree formulation of Enayat's Lemma A.6.
The branch definition is also characterized by its cofinal rank, as used to
replace branch quantification in Stage 2 of the Appendix.
-/

namespace ZFVP.Schmerl

open Set Order Cardinal LO LO.FirstOrder

universe u v w

/-- The tree and rank data in Enayat's Definition 5.6. The assumption of
uncountable cofinality below ensures that the rank order has no last element.
Strict order preservation records that distinct comparable nodes have different ranks. -/
structure RankedTree (T : Type u) (I : Type v) [PartialOrder T] [LinearOrder I] where
  tree : IsTreeOrder T
  rank : T → I
  strictMono : StrictMono rank
  onto : Function.Surjective rank
  predecessor : ∀ t i, i < rank t → ∃ s, s < t ∧ rank s = i

namespace RankedTree

variable {T : Type u} {I : Type v} [PartialOrder T] [LinearOrder I]

/-- A branch is a chain meeting every rank, as in Enayat's Definition 5.7. -/
def IsBranch (R : RankedTree T I) (B : Set T) : Prop :=
  IsChain (· ≤ ·) B ∧ ∀ i, ∃ b ∈ B, R.rank b = i

/-- Ranks determine the order of two nodes on a chain. -/
theorem le_iff_rank_le (R : RankedTree T I) {B : Set T}
    (hB : IsChain (· ≤ ·) B) {x y : T} (hx : x ∈ B) (hy : y ∈ B) :
    x ≤ y ↔ R.rank x ≤ R.rank y := by
  constructor
  · intro hxy
    exact R.strictMono.monotone hxy
  · intro h
    by_contra hxy
    have hyx := hB.lt_of_not_ge hx hy hxy
    exact (R.strictMono hyx).not_ge h

/-- Every branch is a maximal chain. -/
theorem IsBranch.isMaxChain {R : RankedTree T I} {B : Set T} (hB : R.IsBranch B) :
    IsMaxChain (· ≤ ·) B := by
  refine ⟨hB.1, ?_⟩
  intro A hA hBA
  apply Set.Subset.antisymm hBA
  intro x hx
  obtain ⟨y, hy, heq⟩ := hB.2 (R.rank x)
  have hxy : x = y := by
    apply le_antisymm
    · exact (R.le_iff_rank_le hA hx (hBA hy)).mpr heq.ge
    · exact (R.le_iff_rank_le hA (hBA hy) hx).mpr heq.le
  exact hxy ▸ hy

/-- The unique node on a branch at a given rank. -/
noncomputable def IsBranch.node {R : RankedTree T I} {B : Set T}
    (hB : R.IsBranch B) (i : I) : T := Classical.choose (hB.2 i)

theorem IsBranch.node_mem {R : RankedTree T I} {B : Set T}
    (hB : R.IsBranch B) (i : I) : hB.node i ∈ B :=
  (Classical.choose_spec (hB.2 i)).1

@[simp] theorem IsBranch.rank_node {R : RankedTree T I} {B : Set T}
    (hB : R.IsBranch B) (i : I) : R.rank (hB.node i) = i :=
  (Classical.choose_spec (hB.2 i)).2

theorem IsBranch.node_monotone {R : RankedTree T I} {B : Set T}
    (hB : R.IsBranch B) : Monotone hB.node := by
  intro i j hij
  apply (R.le_iff_rank_le hB.1 (hB.node_mem i) (hB.node_mem j)).mpr
  simpa using hij

theorem IsBranch.node_cofinal {R : RankedTree T I} {B : Set T}
    (hB : R.IsBranch B) : ∀ x ∈ B, ∃ i, x ≤ hB.node i := by
  intro x hx
  refine ⟨R.rank x, (R.le_iff_rank_le hB.1 hx (hB.node_mem _)).mpr ?_⟩
  simp

/-- Lemma A.6, with uncountable rank cofinality and a countable color set.
No cofinal sequence is an additional assumption; it is extracted from the branch. -/
theorem IsBranch.exists_branchDefinition {C : Type v} [Countable C] [Nonempty I]
    {R : RankedTree T I} (hI : Cardinal.aleph0 < Order.cof I) {f : T → C}
    (hf : WeaklySpecializes (· ≤ ·) f) {B : Set T} (hB : R.IsBranch B) :
    ∃ b ∈ B, ∀ x, branchDefinition (· ≤ ·) f b x ↔ x ∈ B :=
  Schmerl.exists_branchDefinition hI R.tree hf hB.isMaxChain hB.node
    hB.node_mem hB.node_monotone hB.node_cofinal

/-- A downward-closed chain meeting cofinally many ranks meets every rank. -/
theorem isBranch_of_cofinal_rank (R : RankedTree T I) {B : Set T}
    (hB : IsChain (· ≤ ·) B)
    (hdown : ∀ ⦃x y⦄, y ∈ B → x ≤ y → x ∈ B)
    (hcof : IsCofinal (R.rank '' B)) : R.IsBranch B := by
  refine ⟨hB, ?_⟩
  intro i
  obtain ⟨j, ⟨t, ht, rfl⟩, hij⟩ := hcof i
  rcases hij.eq_or_lt with heq | hlt
  · exact ⟨t, ht, heq.symm⟩
  · obtain ⟨s, hst, hsi⟩ := R.predecessor t i hlt
    exact ⟨s, hdown ht hst.le, hsi⟩

/-- A candidate from Lemma A.6 is a branch exactly when its rank is cofinal.
This is the antecedent used in the infinitary sentence in Stage 2. -/
theorem branchDefinition_isBranch_iff (R : RankedTree T I) {C : Type w} {f : T → C}
    (hf : WeaklySpecializes (· ≤ ·) f) (b : T) :
    R.IsBranch {x | branchDefinition (· ≤ ·) f b x} ↔
      IsCofinal (R.rank '' {x | branchDefinition (· ≤ ·) f b x}) := by
  constructor
  · intro h i
    obtain ⟨x, hx, hxi⟩ := h.2 i
    exact ⟨i, ⟨x, hx, hxi⟩, le_rfl⟩
  · apply R.isBranch_of_cofinal_rank (branchDefinition_isChain R.tree hf b)
    rintro x y ⟨z, hz, hyz⟩ hxy
    exact ⟨z, hz, hxy.trans hyz⟩

/-- The second-order branch assertion reduces to the explicit family of
first-order candidates from Lemma A.6. The conclusion property is arbitrary,
so this applies in particular to definability in the original language. -/
theorem forall_branches_iff {C : Type v} [Countable C] [Nonempty I]
    (R : RankedTree T I) (hI : Cardinal.aleph0 < Order.cof I) {f : T → C}
    (hf : WeaklySpecializes (· ≤ ·) f) (P : Set T → Prop) :
    (∀ B, R.IsBranch B → P B) ↔
      ∀ b, IsCofinal (R.rank '' {x | branchDefinition (· ≤ ·) f b x}) →
        P {x | branchDefinition (· ≤ ·) f b x} := by
  constructor
  · intro h b hb
    exact h _ ((R.branchDefinition_isBranch_iff hf b).mpr hb)
  · intro h B hB
    obtain ⟨b, _, hb⟩ := hB.exists_branchDefinition hI hf
    have heq : {x | branchDefinition (· ≤ ·) f b x} = B := Set.ext hb
    have hbranch : R.IsBranch {x | branchDefinition (· ≤ ·) f b x} := heq.symm ▸ hB
    have hP := h b ((R.branchDefinition_isBranch_iff hf b).mp hbranch)
    exact heq ▸ hP

/-- Every branch of a weakly specialized ranked tree is definable with parameters
in any first-order structure defining the order and equality of colors. -/
theorem IsBranch.definable {L : Language.{w}} [L.Eq] [Structure L T]
    [Structure.Eq L T] {C : Type v} [Countable C] [Nonempty I]
    {R : RankedTree T I} (hI : Cardinal.aleph0 < Order.cof I) {f : T → C}
    [L-relation[T] (· ≤ ·)] [L-relation[T] (fun x y ↦ f x = f y)]
    (hf : WeaklySpecializes (· ≤ ·) f) {B : Set T} (hB : R.IsBranch B) :
    L-predicate[T] (· ∈ B) := by
  obtain ⟨b, _, hb⟩ := hB.exists_branchDefinition hI hf
  exact Language.DefinablePred.of_iff (branchDefinition_definable (· ≤ ·) f b)
    (fun x ↦ (hb x).symm)

end RankedTree

end ZFVP.Schmerl
