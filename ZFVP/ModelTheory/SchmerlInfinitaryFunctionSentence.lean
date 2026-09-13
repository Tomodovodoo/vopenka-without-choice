import ZFVP.ModelTheory.SchmerlInfinitaryFunctionClauses
import ZFVP.ModelTheory.SchmerlFunctionTreeEndExtension

/-! A single uniform sentence for all finite-function trees and its arbitrary
model reduct theorem. Standard satisfaction supplies every selected domain,
coloring and internal filter code used by the end-extension argument. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory Set Order
open ZFVP.Infinitary (Formula)

universe u v

variable {L : Language.{0}}

def functionTreeDataClause (η : ℒₛₑₜ →ᵥ L) (D : Formula L 2)
    (F : Formula L 3) : Formula L 1 :=
  .and (selectedDomainClause η D) (.and (functionColorTotal η F)
    (.and (functionColorCountable F)
      (.and (functionWeakClause η D F) (functionCodesClause η D F))))

/-- The set parameter is universally bound, even when the model is uncountable. -/
def functionTreeFamilySentence (η : ℒₛₑₜ →ᵥ L) (D : Formula L 2)
    (F : Formula L 3) : Formula L 0 :=
  .all (.imp (functionOriginal η internallyInfiniteFormula) (functionTreeDataClause η D F))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (η : ℒₛₑₜ →ᵥ L) (S : Structure L V)
  (hS : S.lMap η = (inferInstance : Structure ℒₛₑₜ V))
  (D : Formula L 2) (F : Formula L 3)

include hS

theorem eval_functionTreeFamilySentence :
    @Formula.Eval L V S 0 (functionTreeFamilySentence η D F) ![] ↔
      ∀ s : V, IsInternallyInfinite s →
        @Formula.Eval L V S 1 (functionTreeDataClause η D F) ![s] := by
  let : Structure L V := S
  have hi (s : V) : (functionOriginal η internallyInfiniteFormula).Eval ![s] ↔
      IsInternallyInfinite s := by
    rw [eval_functionOriginal_of_reduct η S hS]
    simp
  simp [functionTreeFamilySentence, Formula.eval_all, Formula.eval_imp, hi]

/-- Every branch filter has an internal code. No externally chosen chain or
color function appears among the hypotheses. -/
theorem filters_coded_of_functionTreeDataClause (s : V)
    (h : @Formula.Eval L V S 1 (functionTreeDataClause η D F) ![s]) :
    ∃ hD : SelectedDomainClauses s (fun d ↦ @Formula.Eval L V S 2 D ![s, d]),
      let : LinearOrder {d // @Formula.Eval L V S 2 D ![s, d]} := hD.order
      ∀ B : Set (FunctionTreeNode hD.chain),
        (FunctionTreeNode.rankedTree (C := hD.chain)).IsBranch B →
        ∃ m : V, ∀ p : V, p ∈ m ↔ filterOfBranch hD.chain B p := by
  classical
  let : Structure L V := S
  simp only [functionTreeDataClause, Formula.eval_and] at h
  obtain ⟨hdom, htotal, hcount, hweak, hcodes⟩ := h
  let hD := (eval_selectedDomainClause η S hS D s).mp hdom
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice ((eval_functionColorTotal η S hS F s).mp htotal)
  have hF (c x : V) : F.Eval ![s, c, x] ↔ c = f x :=
    ⟨fun hc ↦ (hf x).2 c hc, fun he ↦ he ▸ (hf x).1⟩
  have hfcount : (Set.range f).Countable := by
    apply ((eval_functionColorCountable S F s).mp hcount).mono
    rintro c ⟨x, rfl⟩
    exact ⟨x, (hF _ _).mpr rfl⟩
  refine ⟨hD, hD.filters_coded f hfcount ?_ ?_⟩
  · exact (eval_functionWeakClause η S hS D F f s hF).mp hweak
  · exact (eval_functionCodesClause η S hS D F f s hF).mp hcodes

/-- The construction direction: the new coloring and preserved branch-filter
codes establish the actual formula, including its first-order code clause. -/
theorem functionTreeDataClause_of_semanticData (s : V) (f : V → V)
    (hF : ∀ c x : V, @Formula.Eval L V S 3 F ![s, c, x] ↔ c = f x)
    (hD : SelectedDomainClauses s (fun d ↦ @Formula.Eval L V S 2 D ![s, d]))
    (hcount : (Set.range f).Countable)
    (hweak : ∀ x y z : V,
      x ∈ finitePartialFunctions s ((2 : ℕ) : V) → @Formula.Eval L V S 2 D ![s, domain x] →
      y ∈ finitePartialFunctions s ((2 : ℕ) : V) → @Formula.Eval L V S 2 D ![s, domain y] →
      z ∈ finitePartialFunctions s ((2 : ℕ) : V) → @Formula.Eval L V S 2 D ![s, domain z] →
      x ⊆ y → x ⊆ z → f x = f y → f x = f z → y ⊆ z ∨ z ⊆ y)
    (hfilters : let : LinearOrder {d // @Formula.Eval L V S 2 D ![s, d]} := hD.order
      ∀ B : Set (FunctionTreeNode hD.chain),
        (FunctionTreeNode.rankedTree (C := hD.chain)).IsBranch B →
        ∃ m : V, ∀ p : V, p ∈ m ↔ filterOfBranch hD.chain B p) :
    @Formula.Eval L V S 1 (functionTreeDataClause η D F) ![s] := by
  let : Structure L V := S
  have htotal : (functionColorTotal η F).Eval ![s] := by
    apply (eval_functionColorTotal η S hS F s).mpr
    exact fun x ↦ ⟨f x, (hF _ _).mpr rfl, fun d hd ↦ (hF _ _).mp hd⟩
  have hc : (functionColorCountable F).Eval ![s] := by
    apply (eval_functionColorCountable S F s).mpr
    apply hcount.mono
    rintro c ⟨x, hx⟩
    exact ⟨x, ((hF c x).mp hx).symm⟩
  have hcodes := hD.candidates_coded f hcount hweak hfilters
  simpa only [functionTreeDataClause, Formula.eval_and] using
    (show (selectedDomainClause η D).Eval ![s] ∧ (functionColorTotal η F).Eval ![s] ∧
      (functionColorCountable F).Eval ![s] ∧ (functionWeakClause η D F).Eval ![s] ∧
      (functionCodesClause η D F).Eval ![s] from
      ⟨(eval_selectedDomainClause η S hS D s).mpr hD, htotal, hc,
        (eval_functionWeakClause η S hS D F f s hF).mpr hweak,
        (eval_functionCodesClause η S hS D F f s hF).mpr hcodes⟩)

variable {W : Type v} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

/-- The uniform sentence forces powerset preservation in every ZF end extension
of its set-theoretic reduct. Internally finite domains use finite absoluteness. -/
theorem powersetPreserving_of_functionTreeFamilySentence
    (h : @Formula.Eval L V S 0 (functionTreeFamilySentence η D F) ![]) :
    j.IsPowersetPreserving := by
  classical
  intro s Y hY
  by_cases hs : IsInternallyFinite s
  · obtain ⟨Z, _, hZ⟩ := j.exists_eq_map_of_finite_subset hY
      (internallyFinite_subset (j.map_internallyFinite hs) hY)
    exact ⟨Z, hZ.symm⟩
  · have hdata := (eval_functionTreeFamilySentence η S hS D F).mp h s hs
    obtain ⟨hD, hfilters⟩ := filters_coded_of_functionTreeDataClause η S hS D F s hdata
    let : LinearOrder {d // @Formula.Eval L V S 2 D ![s, d]} := hD.order
    have hdef (B : Set (FunctionTreeNode hD.chain))
        (hB : (FunctionTreeNode.rankedTree (C := hD.chain)).IsBranch B) :
        ℒₛₑₜ-predicate[V] (filterOfBranch hD.chain B) :=
      (filterOfBranch_definable_iff_coded hD.chain B).mpr (hfilters B hB)
    obtain ⟨Z, _, hZ⟩ := subset_closed_of_functionTree_filters_definable hD.chain j hdef hY
    exact ⟨Z, hZ⟩

/-- Combining the class and function conclusions makes all ZF end extensions
conservative over the original set language. -/
theorem definable_trace_of_functionTreeFamilySentence
    (hclass : ∀ X : V → Prop, IsAmenableClass V X → ℒₛₑₜ-predicate[V] X)
    (h : @Formula.Eval L V S 0 (functionTreeFamilySentence η D F) ![])
    {X : W → Prop} (hX : ℒₛₑₜ-predicate[W] X) :
    ℒₛₑₜ-predicate[V] (fun x ↦ X (j x)) :=
  hclass _ (definable_trace_amenable j
    (powersetPreserving_of_functionTreeFamilySentence η S hS D F j h) hX)

end ZFVP.Schmerl
