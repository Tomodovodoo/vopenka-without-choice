import ZFVP.ModelTheory.SchmerlInfinitaryTreeSentence

/-! The construction direction of the branch sentence: preserved original
branch definitions and a weak coloring imply its one-node definition clause. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder Set Order
open ZFVP.Infinitary (Formula)

universe u v w z

variable {T : Type u} {I : Type v} {K : Type w} {C : Type z}
  [PartialOrder T] [LinearOrder I] [LinearOrder K]

theorem RankedTree.cofinalColorBranchDefinition_isBranch_iff
    (R : RankedTree T I) (c : K ↪o I) (f : T → C)
    (hcolor : (Set.range f).Countable)
    (hf : WeaklySpecializes (· ≤ ·) (fun x : R.RankRestriction c ↦ f x.val))
    (b : R.RankRestriction c) :
    R.IsBranch {x | cofinalColorBranchDefinition {y | R.rank y ∈ Set.range c} f b.val x} ↔
      IsCofinal (R.rank '' {x |
        cofinalColorBranchDefinition {y | R.rank y ∈ Set.range c} f b.val x}) := by
  have hcode : WeaklySpecializes (· ≤ ·)
      (fun x : R.RankRestriction c ↦ countableColorCode f hcolor x.val) := by
    intro x y z hxy hxz hfy hfz
    exact hf hxy hxz ((countableColorCode_eq_iff f hcolor _ _).mp hfy)
      ((countableColorCode_eq_iff f hcolor _ _).mp hfz)
  have he : {x | cofinalBranchDefinition {y | R.rank y ∈ Set.range c}
      (countableColorCode f hcolor) b.val x} =
      {x | cofinalColorBranchDefinition {y | R.rank y ∈ Set.range c} f b.val x} := by
    ext x
    exact cofinalColorBranchDefinition_countableColorCode_iff _ f hcolor b.val x
  simpa only [he] using R.cofinalBranchDefinition_isBranch_iff c hcode b

/-- This is the reverse direction needed when constructing a model of the
sentence in a specializing extension. Only definitions in the original reduct
are used to meet its countable disjunction. -/
theorem branchDefinabilityClause_of_branches_definable
    {L₀ : Language.{0}} [L₀.Encodable] {L : Language.{0}}
    {M : Type*} [s : Structure L M] [Nonempty M]
    (η : L₀ →ᵥ L) (R : RankedTree T I) (c : K ↪o I)
    (e : T ↪ M) (o : I ↪ M) (f : T → C)
    (hcolor : (Set.range f).Countable)
    (hf : WeaklySpecializes (· ≤ ·) (fun x : R.RankRestriction c ↦ f x.val))
    (N D O : Formula L 1) (r E H : Formula L 2)
    (hN : ∀ x : M, N.Eval ![x] ↔ x ∈ Set.range e)
    (hD : ∀ t : T, D.Eval ![e t] ↔ R.rank t ∈ Set.range c)
    (hr : ∀ a b : T, r.Eval ![e a, e b] ↔ a ≤ b)
    (hE : ∀ a b : T, E.Eval ![e a, e b] ↔ f a = f b)
    (hO : ∀ x : M, O.Eval ![x] ↔ x ∈ Set.range o)
    (hH : ∀ t : T, ∀ i : I, H.Eval ![e t, o i] ↔ i ≤ R.rank t)
    (hbranches : let : Structure L₀ M := s.lMap η
      ∀ B : Set T, R.IsBranch B → L₀-predicate[M] (fun x ↦ x ∈ e '' B)) :
    (branchDefinabilityClause η N D O r E H).Eval (M := M) ![] := by
  let : Structure L₀ M := s.lMap η
  apply (eval_branchDefinabilityClause η N D O r E H).mpr
  dsimp only
  intro b hb hd htest
  obtain ⟨b, rfl⟩ := (hN b).mp hb
  let B : Set T := {t | cofinalColorBranchDefinition {y | R.rank y ∈ Set.range c} f b t}
  have hψ (x : M) : (canonicalBranchCandidate N D r E).Eval ![x, e b] ↔ x ∈ e '' B :=
    canonicalBranchCandidate_image_iff e f {y | R.rank y ∈ Set.range c}
      N D r E hN hD hr hE b x
  have hcof : IsCofinal (R.rank '' B) :=
    (candidateCofinalityTest_iff R e o O H (canonicalBranchCandidate N D r E)
      (e b) B hO hH hψ).mp ((eval_candidateCofinalityTest O H _ _).mpr htest)
  have hB : R.IsBranch B :=
    (R.cofinalColorBranchDefinition_isBranch_iff c f hcolor hf ⟨b, (hD b).mp hd⟩).mpr hcof
  exact Language.DefinablePred.of_iff (hbranches B hB) hψ

end ZFVP.Schmerl
