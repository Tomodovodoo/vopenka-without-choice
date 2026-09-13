import ZFVP.ModelTheory.WoodinSparseCarrierRecovery
import ZFVP.SetTheory.UniformLevyForcing
import ZFVP.SetTheory.UniformParameterizedRecursion
import Mathlib.Tactic.FinCases

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

noncomputable def sparseSubsetComparisonFormula : SetTheorySemisentence 5 :=
  Classical.choose (IsLevyFormula.ordinaryForcing_definition_uniform.{u}
    (pol := .sigma) (k := 1) (IsLevyFormula.bounded isSubsetOf_bounded) (by omega))

def sparseCarrierOrderStepFormula (ψ : SetTheorySemisentence 5) : SetTheorySemisentence 3 :=
  f“r S H. ∀ z, z ∈ r ↔ ∃ p ∈ S, ∃ q ∈ S,
    z = !kpair.dfn p q ∧ !domain.dfn p ⊆ !domain.dfn H ∧
    !domain.dfn q ⊆ !domain.dfn H ∧
    ∀ b ∈ !domain.dfn H, ∃ B, (∀ x, x ∈ B ↔ x ∈ S ∧ !domain.dfn x ⊆ b) ∧
      !ψ B (!value.dfn H b) (!restrict.dfn p b) (!value.dfn q b) (!value.dfn p b)”

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def SparseSubsetComparison (P R p σ τ : V) : Prop :=
  sparseSubsetComparisonFormula.{u}.Evalb ![P, R, p, σ, τ]

instance sparseSubsetComparison_defined :
    Defined (fun v : Fin 5 → V ↦ SparseSubsetComparison (v 0) (v 1) (v 2) (v 3) (v 4)) sparseSubsetComparisonFormula.{u} :=
  ⟨fun (v : Fin 5 → V) ↦ by
    have hv : ![v 0, v 1, v 2, v 3, v 4] = v := by ext i; fin_cases i <;> rfl
    simp [SparseSubsetComparison, hv]⟩

instance sparseSubsetComparison_definable : ℒₛₑₜ-relation₅[V] SparseSubsetComparison :=
  sparseSubsetComparison_defined.to_definable

attribute [local aesop safe (rule_sets := [Definability])] Language.DefinableRel₅.comp

noncomputable def sparseCarrierOrderStep (S H : V) : V :=
  sep (sparseCarrierCut S (domain H) ×ˢ sparseCarrierCut S (domain H))
    (fun z ↦ ∀ b ∈ domain H, SparseSubsetComparison (sparseCarrierCut S b) (H ‘ b)
      (restrict (kpair.π₁ z) b) ((kpair.π₂ z) ‘ b) ((kpair.π₁ z) ‘ b)) (by definability)

instance sparseCarrierOrderStep_defined :
    ℒₛₑₜ-function₂[V] sparseCarrierOrderStep via
      sparseCarrierOrderStepFormula sparseSubsetComparisonFormula.{u} := by
  refine ⟨fun v ↦ ?_⟩
  simp [sparseCarrierOrderStepFormula]
  symm
  change v 0 = sparseCarrierOrderStep (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [sparseCarrierOrderStep, mem_sep_iff, mem_prod_iff,
    mem_sparseCarrierCut_iff]
  have hcut (B S b : V) : (∀ x, x ∈ B ↔ x ∈ S ∧ domain x ⊆ b) ↔
      B = sparseCarrierCut S b := by
    rw [mem_ext_iff]
    simp only [mem_sparseCarrierCut_iff]
  simp only [hcut, exists_eq_left]
  apply forall_congr'
  intro z
  apply iff_congr Iff.rfl
  constructor
  · rintro ⟨⟨p, ⟨hp, hpd⟩, q, ⟨hq, hqd⟩, rfl⟩, hc⟩
    exact ⟨p, hp, q, hq, rfl, hpd, hqd, by simpa using hc⟩
  · rintro ⟨p, hp, q, hq, rfl, hpd, hqd, hc⟩
    exact ⟨⟨p, ⟨hp, hpd⟩, q, ⟨hq, hqd⟩, rfl⟩, by simpa using hc⟩

theorem sparseSubsetComparison_iff {P R p σ τ : V} (hR : IsForcingPreorder P R)
    (hσ : IsForcingName P σ) (hτ : IsForcingName P τ) :
    SparseSubsetComparison P R p σ τ ↔
      p ∈ forcingFormula P R isSubsetOf (standardTuple ![σ, τ]) := by
  have he := (Classical.choose_spec (IsLevyFormula.ordinaryForcing_definition_uniform.{u}
    (pol := .sigma) (k := 1) (IsLevyFormula.bounded isSubsetOf_bounded) (by omega))).2
  exact he V P R hR ![σ, τ] (by intro i; fin_cases i <;> assumption) p

instance sparseCarrierOrderStep_definable : ℒₛₑₜ-function₂[V] sparseCarrierOrderStep :=
  sparseCarrierOrderStep_defined.to_definable

noncomputable def sparseCarrierOrder (S a : V) : V :=
  parameterRecursion sparseCarrierOrderStep sparseCarrierOrderStep_definable S a

instance sparseCarrierOrder_defined : ℒₛₑₜ-function₂[V] sparseCarrierOrder via
    parameterRecursionFormula (sparseCarrierOrderStepFormula sparseSubsetComparisonFormula.{u}) :=
  parameterRecursionFormula_defined _ _

instance sparseCarrierOrder_definable : ℒₛₑₜ-function₂[V] sparseCarrierOrder :=
  sparseCarrierOrder_defined.to_definable

noncomputable def sparseCarrierOrderTable (S a : V) : V :=
  definableGraph a (sparseCarrierOrder S) (by definability)

instance sparseCarrierOrderTable_function (S a : V) : IsFunction (sparseCarrierOrderTable S a) := by
  unfold sparseCarrierOrderTable
  infer_instance

theorem sparseCarrierOrder_eq (S a : V) [IsOrdinal a] :
    sparseCarrierOrder S a = sparseCarrierOrderStep S (sparseCarrierOrderTable S a) :=
  Replacement.transfiniteRec_spec (sparseCarrierOrderStep S) (by definability)
    (IsOrdinal.toOrdinal a)

theorem sparseCarrierOrder_row {S a p q : V} [IsOrdinal a] :
    ⟨p, q⟩ₖ ∈ sparseCarrierOrder S a ↔
      p ∈ sparseCarrierCut S a ∧ q ∈ sparseCarrierCut S a ∧
      ∀ b ∈ a, SparseSubsetComparison (sparseCarrierCut S b) (sparseCarrierOrder S b)
        (restrict p b) (q ‘ b) (p ‘ b) := by
  rw [sparseCarrierOrder_eq]
  simp only [sparseCarrierOrderStep, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair, sparseCarrierOrderTable, domain_definableGraph]
  have hv (b : V) (hb : b ∈ a) :
      (definableGraph a (sparseCarrierOrder S) (by definability)) ‘ b = sparseCarrierOrder S b :=
    value_definableGraph _ _ _ hb
  simp (config := { contextual := true }) only [hv, and_assoc]

theorem sparseCarrierOrderTable_attempt (S a : V) [IsOrdinal a] :
    IsAttempt (sparseCarrierOrderStep S) a (sparseCarrierOrderTable S a) := by
    refine ⟨inferInstance, inferInstance, domain_definableGraph _ _ _, ?_⟩
    intro b hb y
    have : IsOrdinal b := IsOrdinal.of_mem hb
    have hr : restrict (sparseCarrierOrderTable S a) b = sparseCarrierOrderTable S b :=
      restrict_definableGraph_of_subset ((inferInstance : IsTransitive a).transitive b hb) _ _
    rw [hr, ← sparseCarrierOrder_eq]
    simp [sparseCarrierOrderTable, mem_definableGraph_iff, hb]

theorem sparseCarrierOrderTable_unique {S a H : V}
    (hH : IsAttempt (sparseCarrierOrderStep S) a H) :
    H = sparseCarrierOrderTable S a := by
  have : IsOrdinal a := hH.1
  have : IsFunction H := hH.2.1
  exact IsAttempt.isAttempt_unique (α := IsOrdinal.toOrdinal a) hH
    (sparseCarrierOrderTable_attempt S a)

theorem sparseCarrierOrderStep_row {S H p q : V} :
    ⟨p, q⟩ₖ ∈ sparseCarrierOrderStep S H ↔
      p ∈ sparseCarrierCut S (domain H) ∧ q ∈ sparseCarrierCut S (domain H) ∧
      ∀ b ∈ domain H, SparseSubsetComparison (sparseCarrierCut S b) (H ‘ b)
        (restrict p b) (q ‘ b) (p ‘ b) := by
  simp only [sparseCarrierOrderStep, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

end ZFVP



