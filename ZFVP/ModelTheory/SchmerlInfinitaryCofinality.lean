import ZFVP.ModelTheory.SchmerlInfinitaryDefinitions
import ZFVP.ModelTheory.SchmerlCountableRanges

/-! Explicit standard-Q formulas witnessing uncountable cofinality of a
definable rank sort. Uncountably many ranks alone would not suffice.
-/

namespace ZFVP.Schmerl

open LO LO.FirstOrder Set Order
open ZFVP.Infinitary (Formula)

universe u v w

variable {L : Language.{v}}

/-- A cofinal uncountable predicate inside the rank sort, with countable
intersection with every bounded initial segment of that sort. -/
def cofinalityWitnessClause (O D : Formula L 1) (r : Formula L 2) : Formula L 0 :=
  .and (.q D) (.and
    (.all (.imp D O)) (.and
      (.all (.imp O (.neg (.q (.and (D.rename (fun _ ↦ 0)) r)))))
      (.all (.imp O (.exs (.and (D.rename (fun _ ↦ 0)) r.swapFirstTwo))))))

theorem eval_cofinalityWitnessClause {M : Type u} [Structure L M]
    (O D : Formula L 1) (r : Formula L 2) :
    (cofinalityWitnessClause O D r).Eval (M := M) ![] ↔
      (¬ ({x : M | D.Eval ![x]} : Set M).Countable) ∧
      (∀ x : M, D.Eval ![x] → O.Eval ![x]) ∧
      (∀ a : M, O.Eval ![a] → ({x : M | D.Eval ![x] ∧ r.Eval ![x, a]}).Countable) ∧
      (∀ a : M, O.Eval ![a] → ∃ x : M, D.Eval ![x] ∧ r.Eval ![a, x]) := by
  classical
  simp only [cofinalityWitnessClause, Formula.eval_and, Formula.eval_q,
    Formula.eval_all, Formula.eval_imp, Formula.eval_neg, Formula.eval_exs,
    Formula.eval_rename, Formula.eval_swapFirstTwo, not_not]
  have he (x a : M) : (x :> a :> ![]) ∘ (fun _ : Fin 1 ↦ (0 : Fin 2)) = ![x] := by
    funext i
    have hi := Fin.eq_zero i
    subst i
    rfl
  simp only [he]

/-- Evaluation of the explicit clause forces the actual rank order to have
uncountable external cofinality. The rank coding need only be injective. -/
theorem uncountable_cof_of_cofinalityWitnessClause {M : Type u} [Structure L M]
    {I : Type w} [LinearOrder I] (e : I ↪ M)
    (O D : Formula L 1) (r : Formula L 2)
    (hO : ∀ x : M, O.Eval ![x] ↔ x ∈ Set.range e)
    (hr : ∀ i j : I, r.Eval ![e i, e j] ↔ i ≤ j)
    (h : (cofinalityWitnessClause O D r).Eval (M := M) ![]) :
    Cardinal.aleph0 < Order.cof I := by
  obtain ⟨hunc, hsub, hsec, hcof⟩ := (eval_cofinalityWitnessClause O D r).mp h
  let A : Set I := {i | D.Eval ![e i]}
  have himage : e '' A = {x : M | D.Eval ![x]} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hx
      obtain ⟨i, rfl⟩ := (hO x).mp (hsub x hx)
      exact ⟨i, hx, rfl⟩
  have hA : ¬A.Countable := by
    intro hc
    exact hunc (himage ▸ hc.image e)
  have hsections (i : I) : {x ∈ A | x ≤ i}.Countable := by
    have hc := (hsec (e i) ((hO _).mpr (Set.mem_range_self i))).preimage e.injective
    apply hc.mono
    intro j hj
    exact ⟨hj.1, (hr j i).mpr hj.2⟩
  apply uncountable_cof_of_cofinal_countable_sections A hA hsections
  intro i
  obtain ⟨x, hxD, hix⟩ := hcof (e i) ((hO _).mpr (Set.mem_range_self i))
  obtain ⟨j, rfl⟩ := (hO x).mp (hsub x hxD)
  exact ⟨j, hxD, (hr i j).mp hix⟩

/-- The chosen rank predicate itself is a cofinal order of uncountable
cofinality. Thus the sentence supplies the selected order used by A.6. -/
theorem selected_ranks_of_cofinalityWitnessClause {M : Type u} [Structure L M]
    {I : Type w} [LinearOrder I] (e : I ↪ M)
    (O D : Formula L 1) (r : Formula L 2)
    (hO : ∀ x : M, O.Eval ![x] ↔ x ∈ Set.range e)
    (hr : ∀ i j : I, r.Eval ![e i, e j] ↔ i ≤ j)
    (h : (cofinalityWitnessClause O D r).Eval (M := M) ![]) :
    let A : Set I := {i | D.Eval ![e i]}
    ¬ A.Countable ∧ IsCofinal A ∧ Cardinal.aleph0 < Order.cof A := by
  dsimp only
  let A : Set I := {i | D.Eval ![e i]}
  obtain ⟨hunc, hsub, _, hcof⟩ := (eval_cofinalityWitnessClause O D r).mp h
  have hAunc : ¬A.Countable := by
    intro hA
    apply hunc
    apply (hA.image e).mono
    intro x hx
    obtain ⟨i, rfl⟩ := (hO x).mp (hsub x hx)
    exact ⟨i, hx, rfl⟩
  have hAcof : IsCofinal A := by
    intro i
    obtain ⟨x, hxD, hix⟩ := hcof (e i) ((hO _).mpr (Set.mem_range_self i))
    obtain ⟨j, rfl⟩ := (hO x).mp (hsub x hxD)
    exact ⟨j, hxD, (hr i j).mp hix⟩
  refine ⟨hAunc, hAcof, ?_⟩
  rw [Order.cof_eq_of_isCofinal hAcof]
  exact uncountable_cof_of_cofinalityWitnessClause e O D r hO hr h

/-- A separate negated-Q clause exactly expresses a countable color range. -/
def countableRangeClause (F : Formula L 2) : Formula L 0 :=
  .neg (.q (.exs F.swapFirstTwo))

theorem eval_countableRangeClause {M : Type u} [Structure L M]
    (F : Formula L 2) :
    (countableRangeClause F).Eval (M := M) ![] ↔
      ({c : M | ∃ x : M, F.Eval ![c, x]}).Countable := by
  classical
  simp only [countableRangeClause, Formula.eval_neg, Formula.eval_q,
    Formula.eval_exs, Formula.eval_swapFirstTwo, not_not]

theorem countable_range_of_countableRangeClause {M : Type u} [Structure L M]
    (F : Formula L 2) (f : M → M)
    (hF : ∀ c x : M, F.Eval ![c, x] ↔ c = f x)
    (h : (countableRangeClause F).Eval (M := M) ![]) : (Set.range f).Countable := by
  have hc := (eval_countableRangeClause F).mp h
  apply hc.mono
  rintro c ⟨x, rfl⟩
  exact ⟨x, (hF _ _).mpr rfl⟩

end ZFVP.Schmerl
