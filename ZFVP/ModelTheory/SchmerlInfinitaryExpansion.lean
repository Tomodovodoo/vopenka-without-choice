import ZFVP.ModelTheory.SchmerlInfinitaryDeadEndSentence
import ZFVP.ModelTheory.SchmerlInfinitaryClassConstruction

/-! Interpreting the fixed sentence from the selected ranks, weak colorings,
and preserved class/filter definitions furnished by the specialization step. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary (Formula)

universe u

variable {V : Type u} [SetStructure V]

/-- One structure interprets all four added relations. -/
@[instance_reducible] def deadEndExpansion
    (Dc : V → Prop) (fc : V → V) (Ds : V → V → Prop) (fs : V → V → V) :
    Structure deadEndLanguage V where
  func := fun {_} F a ↦ match F with
    | .inl F => @Structure.func classLanguage V (classExpansion Dc fc) _ F a
    | .inr F => Empty.elim F
  rel := fun {_} R a ↦ match R with
    | .inl R => @Structure.rel classLanguage V (classExpansion Dc fc) _ R a
    | .inr R => match R with
      | .selected => Ds (a 0) (a 1)
      | .color => a 1 = fs (a 0) (a 2)

theorem deadEndExpansion_class_reduct (Dc : V → Prop) (fc : V → V)
    (Ds : V → V → Prop) (fs : V → V → V) :
    (deadEndExpansion Dc fc Ds fs).lMap deadEndClassEmbedding = classExpansion Dc fc := rfl

theorem deadEndExpansion_set_reduct (Dc : V → Prop) (fc : V → V)
    (Ds : V → V → Prop) (fs : V → V → V) :
    (deadEndExpansion Dc fc Ds fs).lMap deadEndSetEmbedding =
      (inferInstance : Structure ℒₛₑₜ V) := rfl

theorem eval_functionSelected (Dc : V → Prop) (fc : V → V)
    (Ds : V → V → Prop) (fs : V → V → V) (s d : V) :
    @Formula.Eval deadEndLanguage V (deadEndExpansion Dc fc Ds fs) 2 functionSelected ![s, d] ↔
      Ds s d := Iff.rfl

theorem eval_functionColor (Dc : V → Prop) (fc : V → V)
    (Ds : V → V → Prop) (fs : V → V → V) (s c x : V) :
    @Formula.Eval deadEndLanguage V (deadEndExpansion Dc fc Ds fs) 3 functionColor ![s, c, x] ↔
      c = fs s x := Iff.rfl

variable [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The concrete expansion satisfies the fixed sentence. The hypotheses are
the mathematical output needed from the two forcing stages; no sentence
satisfaction, dead-end, or absoluteness premise is assumed. -/
theorem deadEndSentence_of_semanticData
    (Dc : V → Prop) (fc : V → V) (Ds : V → V → Prop) (fs : V → V → V)
    (hDc : ClassRankSelection Dc) (hfc : (Set.range fc).Countable)
    (hwc : ∀ x y z : ClassTreeNode V,
      Dc x.level.val → Dc y.level.val → Dc z.level.val →
      x ≤ y → x ≤ z → fc x.code = fc y.code → fc x.code = fc z.code → y ≤ z ∨ z ≤ y)
    (hclasses : ∀ X : V → Prop, IsAmenableClass V X → ℒₛₑₜ-predicate[V] X)
    (hDs : ∀ s : V, IsInternallyInfinite s → SelectedDomainClauses s (Ds s))
    (hfs : ∀ s : V, IsInternallyInfinite s → (Set.range (fs s)).Countable)
    (hws : ∀ s : V, IsInternallyInfinite s → ∀ x y z : V,
      x ∈ finitePartialFunctions s ((2 : ℕ) : V) → Ds s (domain x) →
      y ∈ finitePartialFunctions s ((2 : ℕ) : V) → Ds s (domain y) →
      z ∈ finitePartialFunctions s ((2 : ℕ) : V) → Ds s (domain z) →
      x ⊆ y → x ⊆ z → fs s x = fs s y → fs s x = fs s z → y ⊆ z ∨ z ⊆ y)
    (hcodes : ∀ s : V, ∀ hs : IsInternallyInfinite s,
      let hD := hDs s hs
      let : LinearOrder {d // Ds s d} := hD.order
      ∀ B : Set (FunctionTreeNode hD.chain),
        (FunctionTreeNode.rankedTree (C := hD.chain)).IsBranch B →
        ∃ m : V, ∀ p : V, p ∈ m ↔ filterOfBranch hD.chain B p) :
    @Formula.Eval deadEndLanguage V (deadEndExpansion Dc fc Ds fs) 0 deadEndSentence ![] := by
  let S := deadEndExpansion Dc fc Ds fs
  let : Structure deadEndLanguage V := S
  apply (Formula.eval_and _ _ _).mpr
  constructor
  · apply (eval_mapLanguage deadEndClassEmbedding S classTreeSentence ![]).mpr
    exact classTreeSentence_of_semanticData Dc fc hDc hfc hwc hclasses
  · apply (eval_functionTreeFamilySentence deadEndSetEmbedding S rfl
      functionSelected functionColor).mpr
    intro s hs
    exact functionTreeDataClause_of_semanticData deadEndSetEmbedding S rfl
      functionSelected functionColor s (fs s)
      (fun c x ↦ eval_functionColor Dc fc Ds fs s c x)
      (hDs s hs) (hfs s hs) (hws s hs) (hcodes s hs)

end ZFVP.Schmerl
