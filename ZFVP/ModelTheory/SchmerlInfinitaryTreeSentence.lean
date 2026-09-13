import ZFVP.ModelTheory.SchmerlInfinitaryBranches

/-! The tree part of the corrected Schmerl sentence. It combines an explicit
Q cofinality witness, a countable color range, weak specialization, and original
language definitions. Its semantic consequence is proved without assuming any
of those global properties separately.
-/

namespace ZFVP.Schmerl

open LO LO.FirstOrder Set Order
open ZFVP.Infinitary (Formula)

universe u v w z

variable {L : Language.{v}}

/-- Select a node precisely when its rank lies in the chosen rank predicate. -/
def selectedRankNodes (D : Formula L 1) (J : Formula L 2) : Formula L 1 :=
  .exs (.and (D.rename ![0]) J.swapFirstTwo)

theorem eval_selectedRankNodes {M : Type u} [Structure L M]
    (D : Formula L 1) (J : Formula L 2) (x : M) :
    (selectedRankNodes D J).Eval ![x] ↔ ∃ a : M, D.Eval ![a] ∧ J.Eval ![x, a] := by
  simp [selectedRankNodes, Formula.eval_exs, Formula.eval_and,
    Formula.eval_rename, Formula.eval_swapFirstTwo]

/-- The graph `J(x,a)` gives the node rank; `r(a,b)` is rank order. -/
def nodeRankAbove (J r : Formula L 2) : Formula L 2 :=
  .exs (.and (J.rename ![1, 0]) (r.rename ![2, 0]))

theorem eval_nodeRankAbove {M : Type u} [Structure L M]
    (J r : Formula L 2) (x a : M) :
    (nodeRankAbove J r).Eval ![x, a] ↔ ∃ b : M, J.Eval ![x, b] ∧ r.Eval ![a, b] := by
  simp [nodeRankAbove, Formula.eval_exs, Formula.eval_and, Formula.eval_rename]

/-- The graph `F(c,x)` gives node colors. -/
def equalityOfColors (F : Formula L 2) : Formula L 2 :=
  .exs (.and (F.rename ![0, 1]) (F.rename ![0, 2]))

theorem eval_equalityOfColors {M : Type u} [Structure L M]
    (F : Formula L 2) (x y : M) :
    (equalityOfColors F).Eval ![x, y] ↔ ∃ c : M, F.Eval ![c, x] ∧ F.Eval ![c, y] := by
  simp [equalityOfColors, Formula.eval_exs, Formula.eval_and, Formula.eval_rename]

/-- Fixed syntax, independent of the model later satisfying it. `N` is the
node sort, `O` the rank sort, `D` selected ranks, `r` tree order, `rO` rank order,
`J` the rank graph, and `F` the color graph. -/
noncomputable def treeDefinitionSentence {L₀ : Language.{0}} [L₀.Encodable]
    (η : L₀ →ᵥ L) (N O D : Formula L 1) (r rO J F : Formula L 2) : Formula L 0 :=
  let selected := selectedRankNodes D J
  let E := equalityOfColors F
  .and (cofinalityWitnessClause O D rO) (.and (countableRangeClause F)
    (.and (weakSpecializationClause N selected r E)
      (branchDefinabilityClause η N selected O r E (nodeRankAbove J rO))))

/-- Any standard model of the tree sentence has every branch definable in its
original reduct. The hypotheses identify only the interpretations of the fixed
node/rank/color syntax; uncountable cofinality, countability, weak specialization,
and branch definability are all extracted from the sentence itself. -/
theorem branches_definable_of_treeDefinitionSentence
    {L₀ : Language.{0}} [L₀.Encodable] {M : Type u} [s : Structure L M] [Nonempty M]
    {T : Type w} {I : Type z} [PartialOrder T] [LinearOrder I]
    (η : L₀ →ᵥ L) (R : RankedTree T I) (e : T ↪ M) (o : I ↪ M) (f : T → M)
    (N O D : Formula L 1) (r rO J F : Formula L 2)
    (hN : ∀ x : M, N.Eval ![x] ↔ x ∈ Set.range e)
    (hO : ∀ x : M, O.Eval ![x] ↔ x ∈ Set.range o)
    (hr : ∀ a b : T, r.Eval ![e a, e b] ↔ a ≤ b)
    (hrO : ∀ i j : I, rO.Eval ![o i, o j] ↔ i ≤ j)
    (hJ : ∀ t : T, ∀ a : M, J.Eval ![e t, a] ↔ a = o (R.rank t))
    (hF : ∀ t : T, ∀ c : M, F.Eval ![c, e t] ↔ c = f t)
    (h : (treeDefinitionSentence η N O D r rO J F).Eval (M := M) ![]) :
    let : Structure L₀ M := s.lMap η
    ∀ B : Set T, R.IsBranch B → L₀-predicate[M] (fun x ↦ x ∈ e '' B) := by
  have hh := h
  simp only [treeDefinitionSentence, Formula.eval_and] at hh
  obtain ⟨hcof, hcount, hweak, hdefs⟩ := hh
  let A : Set I := {i | D.Eval ![o i]}
  obtain ⟨hAunc, hAcof, hAcf⟩ :=
    selected_ranks_of_cofinalityWitnessClause o O D rO hO hrO hcof
  change ¬ A.Countable at hAunc
  change IsCofinal A at hAcof
  have hAne : A.Nonempty := by
    by_contra hn
    have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    apply hAunc
    rw [he]
    exact Set.countable_empty
  let : Nonempty A := hAne.to_subtype
  let c : A ↪o I := OrderEmbedding.subtype (· ∈ A)
  have hcrange : Set.range c = A := by
    ext i
    exact ⟨fun ⟨j, he⟩ ↦ he ▸ j.property, fun hi ↦ ⟨⟨i, hi⟩, rfl⟩⟩
  have hc : IsCofinal (Set.range c) := by simpa only [hcrange] using hAcof
  have hD (t : T) : (selectedRankNodes D J).Eval ![e t] ↔ R.rank t ∈ Set.range c := by
    rw [eval_selectedRankNodes, hcrange]
    constructor
    · rintro ⟨a, ha, hja⟩
      change D.Eval ![o (R.rank t)]
      exact (hJ t a).mp hja ▸ ha
    · intro ht
      exact ⟨o (R.rank t), ht, (hJ t _).mpr rfl⟩
  have hE (a b : T) : (equalityOfColors F).Eval ![e a, e b] ↔ f a = f b := by
    rw [eval_equalityOfColors]
    simp only [hF]
    exact ⟨fun ⟨_, ha, hb⟩ ↦ ha.symm.trans hb, fun he ↦ ⟨f a, rfl, he⟩⟩
  have hH (t : T) (i : I) : (nodeRankAbove J rO).Eval ![e t, o i] ↔ i ≤ R.rank t := by
    rw [eval_nodeRankAbove]
    simp only [hJ]
    exact ⟨fun ⟨a, he, ha⟩ ↦ (hrO i (R.rank t)).mp (he ▸ ha),
      fun hi ↦ ⟨o (R.rank t), rfl, (hrO i _).mpr hi⟩⟩
  have hcolor : (Set.range f).Countable := by
    apply ((eval_countableRangeClause F).mp hcount).mono
    rintro x ⟨t, rfl⟩
    exact ⟨e t, (hF t _).mpr rfl⟩
  have hf : WeaklySpecializes (· ≤ ·) (fun x : R.RankRestriction c ↦ f x.val) := by
    intro x y z hxy hxz hfx hfy
    have hw := (eval_weakSpecializationClause N (selectedRankNodes D J) r
      (equalityOfColors F)).mp hweak (e x.val) (e y.val) (e z.val)
      ((hN _).mpr (Set.mem_range_self x.val)) ((hN _).mpr (Set.mem_range_self y.val))
      ((hN _).mpr (Set.mem_range_self z.val)) ((hD _).mpr x.property)
      ((hD _).mpr y.property) ((hD _).mpr z.property)
      ((hr _ _).mpr hxy) ((hr _ _).mpr hxz) ((hE _ _).mpr hfx) ((hE _ _).mpr hfy)
    exact (or_congr (hr y.val z.val) (hr z.val y.val)).mp hw
  exact branches_definable_of_branchDefinabilityClause η R c hAcf hc e o f hcolor hf
    N (selectedRankNodes D J) O r (equalityOfColors F) (nodeRankAbove J rO)
    hN hD hr hE hO hH hdefs

end ZFVP.Schmerl
