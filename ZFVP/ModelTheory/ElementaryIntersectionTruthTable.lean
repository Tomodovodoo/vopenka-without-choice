import ZFVP.ModelTheory.CollapsedElementarySubmodel
import ZFVP.ModelTheory.FixedSyntaxEmbeddingRestriction
import ZFVP.SetTheory.FormulaFamilyRank

/-! A truth table in an elementary submodel makes its intersection with the
table's domain elementary. Low-rank containment fixes the internal syntax. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem elementaryIntersection_of_truthTable {X B C f a U T : V}
    [IsTransitive B] [IsTransitive a] [IsSequenceSupport U]
    (hX : IsElementaryInclusion X B)
    (hf : IsTransitiveCollapse (membershipRelation X) X C f)
    (hlow : hierarchy (succ (ω : V)) ⊆ X)
    (ha : a ∈ X) (hne : IsNonempty a) (hU : U ∈ X) (haU : a ⊆ U)
    (hT : T ∈ X) (ht : IsMembershipTruthTable a T) :
    IsElementaryInclusion (X ∩ a) a := by
  let := hf.1
  let := hierarchy_transitive (succ (ω : V))
  let := hierarchy_transitive (ω : V)
  let g := converseGraph f
  have hg := transitiveCollapse_inverse_elementary hX hf
  let := IsFunction.of_mem hg.function
  have haC : f ‘ a ∈ C := function_value_mem hf.2.1 ha
  have hUC : f ‘ U ∈ C := function_value_mem hf.2.1 hU
  have hTC : f ‘ T ∈ C := function_value_mem hf.2.1 hT
  have hga := transitiveCollapse_inverse_value hf ha
  have hgU := transitiveCollapse_inverse_value hf hU
  have hgT := transitiveCollapse_inverse_value hf hT
  have hfix : ∀ z ∈ hierarchy (succ (ω : V)), z ∈ C ∧ g ‘ z = z :=
    fun z hz ↦ transitiveCollapse_inverse_fixes hf hlow hz
  have hωlow : (ω : V) ∈ hierarchy (succ (ω : V)) :=
    ordinal_subset_hierarchy _ _ (by simp)
  have hω := hfix _ hωlow
  have hF := hfix _ formulaFamily_mem_hierarchy_succ_omega
  have hnat : ∀ n ∈ (ω : V), n ∈ C ∧ g ‘ n = n :=
    fun n hn ↦ hfix n ((hierarchy_transitive _).mem_trans hn hωlow)
  have hcode : ∀ n φ : V, IsMembershipFormulaCode n φ → φ ∈ C ∧ g ‘ φ = φ := by
    intro n φ hφ
    have hp := formulaFamily_subset_hierarchy_omega _ hφ
    have hφω := (kpair_components_mem_transitive hp).2
    exact hfix φ (hierarchy_mono (fun z hz ↦ mem_succ_iff.mpr (Or.inr hz)) _ hφω)
  have hsupport : IsSequenceSupport (f ‘ U) := by
    apply (hg.bounded_defined_iff sequenceSupportFormula_bounded
      (fun v ↦ IsSequenceSupport (v 0)) ![f ‘ U] (by simp [hUC])).mpr
    simpa only [Matrix.cons_val_zero, hgU] using (inferInstance : IsSequenceSupport U)
  let := hsupport
  have hasub : f ‘ a ⊆ f ‘ U := by
    apply (hg.bounded_defined_iff isSubsetOf_bounded
      (fun v ↦ v 0 ⊆ v 1) ![f ‘ a, f ‘ U] (by simp [haC, hUC])).mpr
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, hgU, hga] using haU
  have hnon : IsNonempty (f ‘ a) := by
    apply (hg.bounded_defined_iff boundedNonemptyFormula_bounded
      (fun v ↦ IsNonempty (v 0)) ![f ‘ a] (by simp [haC])).mpr
    simpa only [Matrix.cons_val_zero, hga] using hne
  have htable : IsMembershipTruthTable (f ‘ a) (f ‘ T) := by
    apply (eval_membershipTruthTableFormula hasub (f ‘ T)).mp
    apply (hg.bounded_formula_iff membershipTruthTableFormula_bounded
      ![f ‘ U, ω, formulaFamily membershipLanguageCode ∅, f ‘ a, f ‘ T]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hUC, hω.1, hF.1, haC, hTC])).mpr
    have hv : (fun i ↦ (converseGraph f) ‘
        (![f ‘ U, ω, formulaFamily membershipLanguageCode ∅, f ‘ a, f ‘ T] i)) =
        ![U, ω, formulaFamily membershipLanguageCode ∅, a, T] := by
      funext i
      exact Fin.cases hgU (fun j ↦ Fin.cases hω.2 (fun k ↦ Fin.cases hF.2
        (fun l ↦ Fin.cases hga (fun m ↦ Fin.cases hgT (fun t ↦ Fin.elim0 t) m) l) k) j) i
    rw [hv]
    exact (eval_membershipTruthTableFormula haU T).mpr ht
  have hr := hg.restrict_of_fixed_syntax_truthTable hnon haC hUC hasub
    hω.1 hF.1 hF.2 hnat hcode hTC htable
  rw [hga] at hr
  have hrange : range ((converseGraph f) ↾ (f ‘ a)) = X ∩ a := by
    apply mem_ext
    intro z
    rw [mem_range_iff]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨hyg, hya⟩ := kpair_mem_restrict_iff.mp hy
      obtain ⟨x, hx, hxa, he⟩ := (transitiveCollapse_mem_value hf ha).mp hya
      have hv := value_eq_of_kpair_mem hyg
      rw [← he, transitiveCollapse_inverse_value hf hx] at hv
      exact hv ▸ mem_inter_iff.mpr ⟨hx, hxa⟩
    · intro hz
      obtain ⟨hzX, hza⟩ := mem_inter_iff.mp hz
      have hy : f ‘ z ∈ f ‘ a := (transitiveCollapse_mem_value hf ha).mpr ⟨z, hzX, hza, rfl⟩
      have hyC : f ‘ z ∈ C := function_value_mem hf.2.1 hzX
      refine ⟨f ‘ z, kpair_mem_restrict_iff.mpr ⟨?_, hy⟩⟩
      have hv := kpair_value_mem (f := converseGraph f)
        (domain_eq_of_mem_function hg.function |>.symm ▸ hyC)
      rwa [transitiveCollapse_inverse_value hf hzX] at hv
  rw [← hrange]
  exact hr.range_elementary

end ZFVP
