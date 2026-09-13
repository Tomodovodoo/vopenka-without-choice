import ZFVP.ModelTheory.SchmerlInfinitaryClassSentence
import ZFVP.ModelTheory.SchmerlInfinitaryBranchConstruction

/-! The construction direction of the fixed class-tree sentence. A selected
cofinal rank predicate and a weak coloring suffice when all original branches
remain definable in the set-language reduct. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory Set Order
open ZFVP.Infinitary (Formula)

universe u

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The exact semantic Q requirements on the chosen ordinal levels. -/
structure ClassRankSelection (D : V → Prop) : Prop where
  uncountable : ¬ ({x | D x} : Set V).Countable
  ordinal : ∀ x, D x → IsOrdinal x
  initial : ∀ a : SetTheory.Ordinal V, ({x | D x ∧ x ⊆ a.val} : Set V).Countable
  cofinal : ∀ a : SetTheory.Ordinal V, ∃ x : V, D x ∧ a.val ⊆ x

/-- A cofinal omega-one sequence supplies the exact Q witness required by
the sentence, even when the full ordinal order has uncountable initial segments. -/
theorem classRankSelection_of_cofinal_embedding
    (c : Ordinal.ToType (Ordinal.omega.{u} 1) ↪o SetTheory.Ordinal V)
    (hc : IsCofinal (Set.range c)) :
    ClassRankSelection (fun x : V ↦ x ∈ Set.range (fun i ↦ (c i).val)) := by
  let Ω := Ordinal.ToType (Ordinal.omega.{u} 1)
  let e : Ω → V := fun i ↦ (c i).val
  have he : Function.Injective e := (ordinalCodeEmbedding (V := V)).injective.comp c.injective
  have hI : Cardinal.aleph0 < Order.cof Ω := by
    rw [Ordinal.cof_toType, Cardinal.cof_omega_one]
    exact Cardinal.aleph0_lt_aleph_one
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hcount
    change (Set.range e).Countable at hcount
    have hu : (Set.univ : Set Ω).Countable :=
      Set.countable_of_injective_of_countable_image he.injOn
        (by simpa only [Set.image_univ] using hcount)
    have hcard := Cardinal.mk_le_aleph0_iff.mpr (Set.countable_univ_iff.mp hu)
    rw [Cardinal.mk_toType, Ordinal.card_omega] at hcard
    exact (not_le_of_gt Cardinal.aleph0_lt_aleph_one) hcard
  · rintro x ⟨i, rfl⟩
    exact (c i).ordinal
  · intro a
    obtain ⟨_, ⟨i, rfl⟩, hai⟩ := hc a
    obtain ⟨j, hj⟩ := exists_bound_of_countable hI (Set.countable_singleton i)
    apply ((omegaOne_initial_countable j).image e).mono
    rintro x ⟨⟨k, rfl⟩, hka⟩
    have hki : k ≤ i := c.le_iff_le.mp
      (show c k ≤ c i from (show c k ≤ a from hka).trans hai)
    exact ⟨k, hki.trans_lt (hj i (Set.mem_singleton i)), rfl⟩
  · intro a
    obtain ⟨_, ⟨i, rfl⟩, hai⟩ := hc a
    exact ⟨(c i).val, ⟨i, rfl⟩, hai⟩

/-- Constructing satisfaction is separate from the arbitrary-model reduct
theorem. The hypotheses describe the preserved classes and the new coloring. -/
theorem classTreeSentence_of_semanticData (D : V → Prop) (f : V → V)
    (hD : ClassRankSelection D) (hcount : (Set.range f).Countable)
    (hweak : ∀ x y z : ClassTreeNode V,
      D x.level.val → D y.level.val → D z.level.val →
      x ≤ y → x ≤ z → f x.code = f y.code → f x.code = f z.code → y ≤ z ∨ z ≤ y)
    (hclasses : ∀ X : V → Prop, IsAmenableClass V X → ℒₛₑₜ-predicate[V] X) :
    @Formula.Eval classLanguage V (classExpansion D f) 0 classTreeSentence ![] := by
  classical
  let : Structure classLanguage V := classExpansion D f
  let R := ClassTreeNode.rankedTree (V := V)
  let e := ClassTreeNode.codeEmbedding (V := V)
  let o := ordinalCodeEmbedding (V := V)
  let A : Set (SetTheory.Ordinal V) := {a | D a.val}
  let c : A ↪o SetTheory.Ordinal V := OrderEmbedding.subtype (· ∈ A)
  let N := classOriginal classNodeFormula
  let O := classOriginal ordinalNodeFormula
  let r := classOriginal classOrderFormula
  let rO := classOriginal ordinalOrderFormula
  let J := classOriginal classRankFormula
  let selected := selectedRankNodes classSelected J
  let E := equalityOfColors classColor
  let H := nodeRankAbove J rO
  have hN (x : V) : N.Eval ![x] ↔ x ∈ Set.range e :=
    (eval_classOriginal D f classNodeFormula ![x]).trans (eval_classNodeFormula x)
  have hO (x : V) : O.Eval ![x] ↔ x ∈ Set.range o :=
    (eval_classOriginal D f ordinalNodeFormula ![x]).trans (eval_ordinalNodeFormula x)
  have hr (x y : ClassTreeNode V) : r.Eval ![e x, e y] ↔ x ≤ y :=
    (eval_classOriginal D f classOrderFormula ![x.code, y.code]).trans (eval_classOrderFormula x y)
  have hJ (x : ClassTreeNode V) (a : V) : J.Eval ![e x, a] ↔ a = x.level.val :=
    (eval_classOriginal D f classRankFormula ![x.code, a]).trans (eval_classRankFormula x a)
  have hrO (a b : SetTheory.Ordinal V) : rO.Eval ![o a, o b] ↔ a ≤ b :=
    (eval_classOriginal D f ordinalOrderFormula ![a.val, b.val]).trans (eval_ordinalOrderFormula a b)
  have hselected (x : ClassTreeNode V) : selected.Eval ![e x] ↔ D x.level.val := by
    simp only [selected, eval_selectedRankNodes, hJ, eval_classSelected]
    exact ⟨fun ⟨a, ha, he⟩ ↦ he ▸ ha, fun hx ↦ ⟨x.level.val, hx, rfl⟩⟩
  have hrange (a : SetTheory.Ordinal V) : a ∈ Set.range c ↔ D a.val := by
    exact ⟨fun ⟨b, he⟩ ↦ he ▸ b.property, fun ha ↦ ⟨⟨a, ha⟩, rfl⟩⟩
  have hE (x y : ClassTreeNode V) : E.Eval ![e x, e y] ↔ f x.code = f y.code := by
    simp [E, eval_equalityOfColors, eval_classColor]
    rfl
  have hH (x : ClassTreeNode V) (a : SetTheory.Ordinal V) : H.Eval ![e x, o a] ↔ a ≤ R.rank x := by
    rw [eval_nodeRankAbove]
    simp only [hJ]
    constructor
    · rintro ⟨_, rfl, hb⟩
      exact (hrO a x.level).mp hb
    · intro hx
      exact ⟨x.level.val, rfl, (hrO a x.level).mpr hx⟩
  have hcof : (cofinalityWitnessClause O classSelected rO).Eval (M := V) ![] := by
    apply (eval_cofinalityWitnessClause O classSelected rO).mpr
    refine ⟨hD.uncountable, ?_, ?_, ?_⟩
    · intro x hx
      exact (hO x).mpr ⟨⟨x, hD.ordinal x hx⟩, rfl⟩
    · intro a ha
      obtain ⟨a, rfl⟩ := (hO a).mp ha
      have he (x : V) : rO.Eval ![x, o a] ↔ x ⊆ a.val := by
        rw [eval_classOriginal D f ordinalOrderFormula]
        simp [ordinalOrderFormula]
        rfl
      simpa only [eval_classSelected, he] using hD.initial a
    · intro a ha
      obtain ⟨a, rfl⟩ := (hO a).mp ha
      obtain ⟨x, hx, hax⟩ := hD.cofinal a
      refine ⟨x, hx, ?_⟩
      rw [eval_classOriginal D f ordinalOrderFormula]
      have he : o a = a.val := rfl
      simpa [ordinalOrderFormula, he] using hax
  have hcountClause : (countableRangeClause classColor).Eval (M := V) ![] := by
    apply (eval_countableRangeClause classColor).mpr
    simp only [eval_classColor]
    apply hcount.mono
    rintro c ⟨x, he⟩
    exact ⟨x, he.symm⟩
  have hweakClause : (weakSpecializationClause N selected r E).Eval (M := V) ![] := by
    apply (eval_weakSpecializationClause N selected r E).mpr
    intro x y z hx hy hz hdx hdy hdz hxy hxz hexy hexz
    obtain ⟨x, rfl⟩ := (hN x).mp hx
    obtain ⟨y, rfl⟩ := (hN y).mp hy
    obtain ⟨z, rfl⟩ := (hN z).mp hz
    exact (or_congr (hr y z) (hr z y)).mpr
      (hweak x y z ((hselected x).mp hdx) ((hselected y).mp hdy) ((hselected z).mp hdz)
        ((hr x y).mp hxy) ((hr x z).mp hxz) ((hE x y).mp hexy) ((hE x z).mp hexz))
  have hf : WeaklySpecializes (· ≤ ·) (fun x : R.RankRestriction c ↦ f x.val.code) := by
    intro x y z hxy hxz hfx hfy
    exact hweak x.val y.val z.val ((hrange _).mp x.property)
      ((hrange _).mp y.property) ((hrange _).mp z.property) hxy hxz hfx hfy
  have hdefs : (branchDefinabilityClause classLanguageEmbedding N selected O r E H).Eval (M := V) ![] := by
    apply branchDefinabilityClause_of_branches_definable classLanguageEmbedding R c e o
      (fun x ↦ f x.code) (hcount.mono (Set.range_comp_subset_range _ _)) hf
      N selected O r E H hN (fun x ↦ (hselected x).trans (hrange x.level).symm) hr hE hO hH
    dsimp only
    intro B hB
    exact classTree_branches_definable hclasses hB
  have htotal : classColorTotal.Eval (M := V) ![] := by
    apply (eval_classColorTotal (classExpansion D f) rfl).mpr
    exact fun x ↦ ⟨f x, rfl, fun _ he ↦ he⟩
  exact (Formula.eval_and _ _ _).mpr ⟨htotal,
    by simpa only [treeDefinitionSentence, Formula.eval_and] using
      (show (cofinalityWitnessClause O classSelected rO).Eval (M := V) ![] ∧
        (countableRangeClause classColor).Eval (M := V) ![] ∧
        (weakSpecializationClause N selected r E).Eval (M := V) ![] ∧
        (branchDefinabilityClause classLanguageEmbedding N selected O r E H).Eval (M := V) ![] from
          ⟨hcof, hcountClause, hweakClause, hdefs⟩)⟩

end ZFVP.Schmerl
