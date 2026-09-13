import ZFVP.ModelTheory.SchmerlCofinalRanks
import ZFVP.ModelTheory.SchmerlBranchPreservation

/-! Branch definitions obtained by specializing only a cofinal rank restriction.
This applies to rank orders of cofinality omega-one even when their bounded
initial segments are uncountable. The complete tree's branches are recovered
as downward closures of color cones on the selected levels.
-/

namespace ZFVP.Schmerl

open Set Order Cardinal LO LO.FirstOrder

universe u v w z

variable {T : Type u} {I : Type v} {K : Type w}
  [PartialOrder T] [LinearOrder I] [LinearOrder K]

namespace RankedTree

/-- The natural-color form of Lemma A.6, with independent tree/rank universes. -/
theorem IsBranch.exists_branchDefinition_nat [Nonempty I]
    {R : RankedTree T I} (hI : Cardinal.aleph0 < Order.cof I) {f : T → ℕ}
    (hf : WeaklySpecializes (· ≤ ·) f) {B : Set T} (hB : R.IsBranch B) :
    ∃ b ∈ B, ∀ x, branchDefinition (· ≤ ·) f b x ↔ x ∈ B := by
  let g : T → ULift.{v} ℕ := fun x ↦ ⟨f x⟩
  have hg : WeaklySpecializes (· ≤ ·) g := by
    intro x y z hxy hxz hfy hfz
    exact hf hxy hxz (congrArg ULift.down hfy) (congrArg ULift.down hfz)
  obtain ⟨b, hb, hdef⟩ := hB.exists_branchDefinition hI hg
  refine ⟨b, hb, fun x ↦ ?_⟩
  simpa only [branchDefinition, colorCone, g, ULift.up.injEq] using hdef x

end RankedTree

/-- A branch candidate using only the selected levels. -/
def cofinalBranchDefinition (S : Set T) (f : T → ℕ) (b x : T) : Prop :=
  ∃ y ∈ S, colorCone (· ≤ ·) f b y ∧ x ≤ y

namespace RankedTree

variable (R : RankedTree T I) (c : K ↪o I)

/-- The cofinal-level candidate is the expansion of its restricted candidate. -/
theorem cofinalBranchDefinition_iff (f : T → ℕ) (b : R.RankRestriction c) (x : T) :
    cofinalBranchDefinition {y | R.rank y ∈ Set.range c} f b.val x ↔
      x ∈ R.expandBranch c {y | branchDefinition (· ≤ ·) (fun z ↦ f z.val) b y} := by
  constructor
  · rintro ⟨y, hy, hcone, hxy⟩
    exact ⟨⟨y, hy⟩, ⟨⟨y, hy⟩, hcone, le_rfl⟩, hxy⟩
  · rintro ⟨y, ⟨z, hcone, hyz⟩, hxy⟩
    exact ⟨z.val, z.property, hcone, hxy.trans hyz⟩

/-- Specializing the cofinal rank restriction defines every full branch. -/
theorem exists_cofinalBranchDefinition [Nonempty K]
    (hK : Cardinal.aleph0 < Order.cof K) (hcof : IsCofinal (Set.range c))
    {f : T → ℕ} (hf : WeaklySpecializes (· ≤ ·)
      (fun x : R.RankRestriction c ↦ f x.val)) {B : Set T} (hB : R.IsBranch B) :
    ∃ b ∈ B, R.rank b ∈ Set.range c ∧
      ∀ x, cofinalBranchDefinition {y | R.rank y ∈ Set.range c} f b x ↔ x ∈ B := by
  obtain ⟨b, hb, hdef⟩ := (R.restrictBranch_isBranch c hB).exists_branchDefinition_nat hK hf
  have heq : {y | branchDefinition (· ≤ ·) (fun z ↦ f z.val) b y} =
      R.restrictBranch c B := Set.ext hdef
  refine ⟨b.val, hb, b.property, fun x ↦ ?_⟩
  rw [R.cofinalBranchDefinition_iff c f b x, heq, R.expand_restrictBranch c hcof hB]

theorem cofinalBranchDefinition_isChain {f : T → ℕ}
    (hf : WeaklySpecializes (· ≤ ·) (fun x : R.RankRestriction c ↦ f x.val))
    (b : R.RankRestriction c) :
    IsChain (· ≤ ·) {x | cofinalBranchDefinition {y | R.rank y ∈ Set.range c} f b.val x} := by
  have hcone : IsChain (fun x y : R.RankRestriction c ↦ x ≤ y)
      {x | colorCone (· ≤ ·) (fun z ↦ f z.val) b x} :=
    colorCone_isChain (R.restrictRanks c).tree hf b
  rintro x ⟨a, ha, hca, hxa⟩ y ⟨d, hd, hcd, hyd⟩ _
  have hcomp : (⟨a, ha⟩ : R.RankRestriction c) ≤ ⟨d, hd⟩ ∨
      (⟨d, hd⟩ : R.RankRestriction c) ≤ ⟨a, ha⟩ := by
    by_cases had : (⟨a, ha⟩ : R.RankRestriction c) = ⟨d, hd⟩
    · exact Or.inl had.le
    · exact hcone hca hcd had
  rcases hcomp with had | hda
  · exact R.tree (hxa.trans had) hyd
  · exact R.tree hxa (hyd.trans hda)

/-- The explicit candidate is a branch exactly when its full-tree ranks are cofinal. -/
theorem cofinalBranchDefinition_isBranch_iff {f : T → ℕ}
    (hf : WeaklySpecializes (· ≤ ·) (fun x : R.RankRestriction c ↦ f x.val))
    (b : R.RankRestriction c) :
    R.IsBranch {x | cofinalBranchDefinition {y | R.rank y ∈ Set.range c} f b.val x} ↔
      IsCofinal (R.rank '' {x |
        cofinalBranchDefinition {y | R.rank y ∈ Set.range c} f b.val x}) := by
  constructor
  · intro h i
    obtain ⟨x, hx, hxi⟩ := h.2 i
    exact ⟨i, ⟨x, hx, hxi⟩, le_rfl⟩
  · apply R.isBranch_of_cofinal_rank (R.cofinalBranchDefinition_isChain c hf b)
    rintro x y ⟨a, ha, hca, hya⟩ hxy
    exact ⟨a, ha, hca, hxy.trans hya⟩

/-- Quantification over branches reduces to one-node candidates and their
first-order cofinal-rank test. This is the semantic reduction used in the
infinitary branch-definability clause. -/
theorem forall_branches_iff_cofinal_candidates [Nonempty K]
    (hK : Cardinal.aleph0 < Order.cof K) (hcof : IsCofinal (Set.range c))
    {f : T → ℕ} (hf : WeaklySpecializes (· ≤ ·)
      (fun x : R.RankRestriction c ↦ f x.val)) (P : Set T → Prop) :
    (∀ B, R.IsBranch B → P B) ↔
      ∀ b : R.RankRestriction c,
        IsCofinal (R.rank '' {x |
          cofinalBranchDefinition {y | R.rank y ∈ Set.range c} f b.val x}) →
        P {x | cofinalBranchDefinition {y | R.rank y ∈ Set.range c} f b.val x} := by
  constructor
  · intro h b hb
    exact h _ ((R.cofinalBranchDefinition_isBranch_iff c hf b).mpr hb)
  · intro h B hB
    obtain ⟨b, hb, hbrank, hdef⟩ := R.exists_cofinalBranchDefinition c hK hcof hf hB
    have heq : {x | cofinalBranchDefinition {y | R.rank y ∈ Set.range c} f b x} = B :=
      Set.ext hdef
    have hbranch : R.IsBranch {x |
        cofinalBranchDefinition {y | R.rank y ∈ Set.range c} f b x} := heq.symm ▸ hB
    have hresult := h ⟨b, hbrank⟩
      ((R.cofinalBranchDefinition_isBranch_iff c hf ⟨b, hbrank⟩).mp hbranch)
    simpa only [heq] using hresult

end RankedTree

/-- The cofinal-level candidate is first order in the expanded structure. -/
theorem cofinalBranchDefinition_definable {L : Language.{z}} [L.Eq] [Structure L T]
    [Structure.Eq L T] (S : Set T) (f : T → ℕ)
    [L-predicate[T] (· ∈ S)] [L-relation[T] (· ≤ ·)]
    [L-relation[T] (fun x y ↦ f x = f y)] (b : T) :
    L-predicate[T] (cofinalBranchDefinition S f b) := by
  unfold cofinalBranchDefinition colorCone
  apply Language.Definable.exs
  apply Language.Definable.and
  · definability
  · apply Language.Definable.and
    · apply Language.Definable.or
      · definability
      · apply Language.Definable.and
        · definability
        · exact Language.DefinableRel.comp (P := fun x y ↦ f x = f y)
            (by definability) (by definability)
    · definability

/-- Corrected specialization for every rank order of cofinality omega-one.
The poset has ccc square, and every directed union meeting its deciding sets
provides explicit one-parameter definitions of all branches of the original tree.
This removes the countable-initial-segment assumption on its rank order. -/
theorem exists_ccc_cofinal_branch_definitions
    (R : RankedTree T I) (hI : Order.cof I = Cardinal.aleph 1)
    (hcard : Cardinal.mk {B : Set T // R.IsBranch B} ≤ Cardinal.aleph 1) :
    ∃ c : Ordinal.ToType (Ordinal.omega.{v} 1) ↪o I, IsCofinal (Set.range c) ∧
      ∃ D : BranchMarkers (R.restrictRanks c)
        {B : Set (R.RankRestriction c) // (R.restrictRanks c).IsBranch B},
        (∀ A : Set (StrictCondition D.core × StrictCondition D.core),
          A.Pairwise (fun p q ↦ ¬ Poset.Compatible p q) → A.Countable) ∧
        (∀ G : Set (StrictCondition D.core), DirectedOn (· ≥ ·) G →
          (∀ x, ∃ p ∈ G, p ∈ StrictCondition.decides x) →
          ∃ f : T → ℕ, ∀ B, R.IsBranch B → ∃ b ∈ B, R.rank b ∈ Set.range c ∧
            ∀ x, cofinalBranchDefinition {y | R.rank y ∈ Set.range c} f b x ↔ x ∈ B) := by
  classical
  obtain ⟨c, hcof⟩ := exists_omegaOne_cofinal_embedding hI
  have hnewcard : Cardinal.mk {B : Set (R.RankRestriction c) //
      (R.restrictRanks c).IsBranch B} ≤ Cardinal.aleph 1 := by
    rw [← Cardinal.mk_congr (R.branchRestrictionEquiv c hcof)]
    exact hcard
  obtain ⟨D, _, hchains⟩ := exists_aronszajn_core (R.restrictRanks c) hnewcard
  refine ⟨c, hcof, D,
    StrictCondition.product_countable_antichains D.core_tree D.core_tree hchains hchains, ?_⟩
  intro G hG hmeets
  obtain ⟨g, hg⟩ := D.exists_weak_coloring_of_directed hG hmeets
  let f (x : T) : ℕ := if h : R.rank x ∈ Set.range c then g ⟨x, h⟩ else 0
  have heq : (fun x : R.RankRestriction c ↦ f x.val) = g := by
    funext x
    simp only [f, dite_eq_left x.property]
    exact congrArg g (Subtype.ext rfl)
  have hf : WeaklySpecializes (· ≤ ·) (fun x : R.RankRestriction c ↦ f x.val) := by
    rw [heq]; exact hg
  let : Nonempty (Ordinal.ToType (Ordinal.omega.{v} 1)) :=
    Ordinal.nonempty_toType_iff.mpr (Ordinal.omega_pos 1).ne'
  have hK : Cardinal.aleph0 < Order.cof (Ordinal.ToType (Ordinal.omega.{v} 1)) := by
    rw [Ordinal.cof_toType, Cardinal.cof_omega_one]
    exact Cardinal.aleph0_lt_aleph_one
  exact ⟨f, fun _ hB ↦ R.exists_cofinalBranchDefinition c hK hcof hf hB⟩

end ZFVP.Schmerl
