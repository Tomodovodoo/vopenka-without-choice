import ZFVP.ModelTheory.SchmerlInfinitaryCofinality
import ZFVP.ModelTheory.SchmerlClassTree

/-! Actual formulas for the selected-level branch candidates, the cofinal-rank
test, and the corrected original-language definability requirement.
-/

namespace ZFVP.Schmerl

open LO LO.FirstOrder Set Order
open ZFVP.Infinitary (Formula)

universe u v w z

variable {L : Language.{v}}

/-- `ψ(x,b)`: the full downward closure of the same-color cone through `b`
on the selected levels. Variables inside the existential are `y,x,b`. -/
def canonicalBranchCandidate (N D : Formula L 1) (r E : Formula L 2) : Formula L 2 :=
  .and (N.rename ![0]) (.and (N.rename ![1])
    (.exs (.and (N.rename ![0]) (.and (D.rename ![0])
      (.and (.or (r.rename ![0, 2])
        (.and (r.rename ![2, 0]) (E.rename ![2, 0]))) (r.rename ![1, 0]))))))

theorem eval_canonicalBranchCandidate {M : Type u} [Structure L M]
    (N D : Formula L 1) (r E : Formula L 2) (x b : M) :
    (canonicalBranchCandidate N D r E).Eval ![x, b] ↔
      N.Eval ![x] ∧ N.Eval ![b] ∧ ∃ y : M, N.Eval ![y] ∧ D.Eval ![y] ∧
        (r.Eval ![y, b] ∨ r.Eval ![b, y] ∧ E.Eval ![b, y]) ∧ r.Eval ![x, y] := by
  simp [canonicalBranchCandidate, Formula.eval_and, Formula.eval_or,
    Formula.eval_exs, Formula.eval_rename]

/-- Test every rank for a candidate node at least that high. The rank-node
relation `H(x,a)` means that node `x` has rank at least `a`. -/
def candidateCofinalityTest (O : Formula L 1) (H ψ : Formula L 2) : Formula L 1 :=
  .all (.imp (O.rename ![0])
    (.exs (.and (ψ.rename ![0, 2]) (H.rename ![0, 1]))))

theorem eval_candidateCofinalityTest {M : Type u} [Structure L M]
    (O : Formula L 1) (H ψ : Formula L 2) (b : M) :
    (candidateCofinalityTest O H ψ).Eval ![b] ↔
      ∀ a : M, O.Eval ![a] → ∃ x : M, ψ.Eval ![x, b] ∧ H.Eval ![x, a] := by
  simp [candidateCofinalityTest, Formula.eval_all, Formula.eval_imp,
    Formula.eval_exs, Formula.eval_and, Formula.eval_rename]

/-- Only cofinal candidates through selected tree nodes are required to have
an original-language definition. -/
noncomputable def branchDefinabilityClause {L₀ : Language.{0}} [L₀.Encodable]
    (η : L₀ →ᵥ L) (N D O : Formula L 1) (r E H : Formula L 2) : Formula L 0 :=
  let ψ := canonicalBranchCandidate N D r E
  .all (.imp (.and N (.and D (candidateCofinalityTest O H ψ)))
    (originalDefinabilityClause η ψ))

theorem eval_branchDefinabilityClause {L₀ : Language.{0}} [L₀.Encodable]
    {M : Type u} [s : Structure L M] [Nonempty M]
    (η : L₀ →ᵥ L) (N D O : Formula L 1) (r E H : Formula L 2) :
    (branchDefinabilityClause η N D O r E H).Eval (M := M) ![] ↔
      let : Structure L₀ M := s.lMap η
      ∀ b : M, N.Eval ![b] → D.Eval ![b] →
        (∀ a : M, O.Eval ![a] → ∃ x : M,
          (canonicalBranchCandidate N D r E).Eval ![x, b] ∧ H.Eval ![x, a]) →
        L₀-predicate[M] (fun x ↦ (canonicalBranchCandidate N D r E).Eval ![x, b]) := by
  simp only [branchDefinabilityClause, Formula.eval_all, Formula.eval_imp,
    Formula.eval_and, eval_originalDefinabilityClause, eval_candidateCofinalityTest]
  simp only [and_imp]

/-- The fork condition uses only first-order quantifiers and color equality. -/
def weakSpecializationClause (N D : Formula L 1) (r E : Formula L 2) : Formula L 0 :=
  let guards : Formula L 3 := .and
    (.and (N.rename ![0]) (D.rename ![0])) (.and
      (.and (N.rename ![1]) (D.rename ![1]))
      (.and (N.rename ![2]) (D.rename ![2])))
  let fork : Formula L 3 := .and (r.rename ![0, 1])
    (.and (r.rename ![0, 2]) (.and (E.rename ![0, 1]) (E.rename ![0, 2])))
  .all (.all (.all (.imp (.and guards fork)
    (.or (r.rename ![1, 2]) (r.rename ![2, 1])))))

theorem eval_weakSpecializationClause {M : Type u} [Structure L M]
    (N D : Formula L 1) (r E : Formula L 2) :
    (weakSpecializationClause N D r E).Eval (M := M) ![] ↔
      ∀ x y z : M, N.Eval ![x] → N.Eval ![y] → N.Eval ![z] →
        D.Eval ![x] → D.Eval ![y] → D.Eval ![z] →
        r.Eval ![x, y] → r.Eval ![x, z] → E.Eval ![x, y] → E.Eval ![x, z] →
        r.Eval ![y, z] ∨ r.Eval ![z, y] := by
  simp [weakSpecializationClause, Formula.eval_all, Formula.eval_imp,
    Formula.eval_and, Formula.eval_or, Formula.eval_rename, and_imp]
  constructor
  · intro h x y z hNx hNy hNz hDx hDy hDz
    exact h z y x hNx hDx hNy hDy hNz hDz
  · intro h z y x hNx hDx hNy hDy hNz hDz
    exact h x y z hNx hNy hNz hDx hDy hDz

variable {M : Type u} [s : Structure L M]
variable {T : Type w} {I : Type z} [PartialOrder T] [LinearOrder I]

/-- The candidate formula denotes exactly the image of the mathematical
cofinal-level candidate. Every quantifier in the syntax ranges over model elements. -/
theorem canonicalBranchCandidate_image_iff (e : T ↪ M)
    {C : Type*} (f : T → C) (S : Set T)
    (N D : Formula L 1) (r E : Formula L 2)
    (hN : ∀ x : M, N.Eval ![x] ↔ x ∈ Set.range e)
    (hD : ∀ t : T, D.Eval ![e t] ↔ t ∈ S)
    (hr : ∀ a b : T, r.Eval ![e a, e b] ↔ a ≤ b)
    (hE : ∀ a b : T, E.Eval ![e a, e b] ↔ f a = f b)
    (b : T) (x : M) :
    (canonicalBranchCandidate N D r E).Eval ![x, e b] ↔
      x ∈ e '' {t | cofinalColorBranchDefinition S f b t} := by
  rw [eval_canonicalBranchCandidate]
  constructor
  · rintro ⟨hxN, _, y, hyN, hyD, hcone, hxy⟩
    obtain ⟨a, rfl⟩ := (hN x).mp hxN
    obtain ⟨d, rfl⟩ := (hN y).mp hyN
    refine ⟨a, ⟨d, (hD d).mp hyD, ?_, (hr a d).mp hxy⟩, rfl⟩
    exact (or_congr (hr d b) (and_congr (hr b d) (hE b d))).mp hcone
  · rintro ⟨a, ⟨d, hd, hcone, had⟩, rfl⟩
    exact ⟨(hN _).mpr (Set.mem_range_self a), (hN _).mpr (Set.mem_range_self b),
      e d, (hN _).mpr (Set.mem_range_self d), (hD d).mpr hd,
      (or_congr (hr d b) (and_congr (hr b d) (hE b d))).mpr hcone, (hr a d).mpr had⟩

/-- The syntactic cofinality test agrees with cofinality of branch ranks. -/
theorem candidateCofinalityTest_iff (R : RankedTree T I) (e : T ↪ M) (o : I ↪ M)
    (O : Formula L 1) (H ψ : Formula L 2) (b : M) (B : Set T)
    (hO : ∀ x : M, O.Eval ![x] ↔ x ∈ Set.range o)
    (hH : ∀ t : T, ∀ i : I, H.Eval ![e t, o i] ↔ i ≤ R.rank t)
    (hψ : ∀ x : M, ψ.Eval ![x, b] ↔ x ∈ e '' B) :
    (candidateCofinalityTest O H ψ).Eval ![b] ↔ IsCofinal (R.rank '' B) := by
  rw [eval_candidateCofinalityTest]
  constructor
  · intro h i
    obtain ⟨x, hx, hix⟩ := h (o i) ((hO _).mpr (Set.mem_range_self i))
    obtain ⟨t, ht, rfl⟩ := (hψ x).mp hx
    exact ⟨R.rank t, ⟨t, ht, rfl⟩, (hH t i).mp hix⟩
  · intro h x hx
    obtain ⟨i, rfl⟩ := (hO x).mp hx
    obtain ⟨_, ⟨t, ht, rfl⟩, hit⟩ := h i
    exact ⟨e t, (hψ _).mpr ⟨t, ht, rfl⟩, (hH t i).mpr hit⟩

/-- The corrected infinitary clause makes every mathematical branch definable
in the original reduct. All syntactic interpretations are given at individual
nodes/ranks; no branch-definability conclusion is assumed. -/
theorem branches_definable_of_branchDefinabilityClause
    {L₀ : Language.{0}} [L₀.Encodable] [Nonempty M]
    {K : Type*} [LinearOrder K] [Nonempty K]
    (η : L₀ →ᵥ L) (R : RankedTree T I) (c : K ↪o I)
    (hK : Cardinal.aleph0 < Order.cof K) (hcof : IsCofinal (Set.range c))
    (e : T ↪ M) (o : I ↪ M) {C : Type*} (f : T → C)
    (hcolor : (Set.range f).Countable)
    (hf : WeaklySpecializes (· ≤ ·) (fun x : R.RankRestriction c ↦ f x.val))
    (N D O : Formula L 1) (r E H : Formula L 2)
    (hN : ∀ x : M, N.Eval ![x] ↔ x ∈ Set.range e)
    (hD : ∀ t : T, D.Eval ![e t] ↔ R.rank t ∈ Set.range c)
    (hr : ∀ a b : T, r.Eval ![e a, e b] ↔ a ≤ b)
    (hE : ∀ a b : T, E.Eval ![e a, e b] ↔ f a = f b)
    (hO : ∀ x : M, O.Eval ![x] ↔ x ∈ Set.range o)
    (hH : ∀ t : T, ∀ i : I, H.Eval ![e t, o i] ↔ i ≤ R.rank t)
    (hclause : (branchDefinabilityClause η N D O r E H).Eval (M := M) ![]) :
    let : Structure L₀ M := s.lMap η
    ∀ B : Set T, R.IsBranch B → L₀-predicate[M] (fun x ↦ x ∈ e '' B) := by
  let : Structure L₀ M := s.lMap η
  dsimp only
  intro B hB
  obtain ⟨b, _, hbrank, hdef⟩ :=
    R.exists_cofinalColorBranchDefinition c hK hcof hcolor hf hB
  have heq : {t | cofinalColorBranchDefinition {y | R.rank y ∈ Set.range c} f b t} = B :=
    Set.ext hdef
  have hψ : ∀ x : M, (canonicalBranchCandidate N D r E).Eval ![x, e b] ↔ x ∈ e '' B := by
    intro x
    have h := canonicalBranchCandidate_image_iff e f {y | R.rank y ∈ Set.range c}
      N D r E hN hD hr hE b x
    simpa only [heq] using h
  have hBcof : IsCofinal (R.rank '' B) := by
    intro i
    obtain ⟨t, ht, hti⟩ := hB.2 i
    exact ⟨i, ⟨t, ht, hti⟩, le_rfl⟩
  have htest := (candidateCofinalityTest_iff R e o O H
    (canonicalBranchCandidate N D r E) (e b) B hO hH hψ).mpr hBcof
  have hd := (eval_branchDefinabilityClause η N D O r E H).mp hclause (e b)
    ((hN _).mpr (Set.mem_range_self b)) ((hD b).mpr hbrank)
    ((eval_candidateCofinalityTest O H _ (e b)).mp htest)
  exact Language.DefinablePred.of_iff hd (fun x ↦ (hψ x).symm)

end ZFVP.Schmerl
