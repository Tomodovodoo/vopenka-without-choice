import ZFVP.SetTheory.UltrapowerLos
import ZFVP.SetTheory.UltrapowerEmbeddingMap
import ZFVP.ModelTheory.CodedMembershipEmbedding
import ZFVP.ModelTheory.CriticalPoint

/-! The canonical map of the internal ultrapower is elementary.

Los's theorem computes satisfaction in the ultrapower from the index sets of a formula. Feeding it
an assignment of constant functions makes the index set of a formula either all of `P` or empty,
depending only on whether the formula holds of the underlying assignment in `A`. Since `P` is in the
ultrafilter and the empty set is not, that is exactly elementarity of the canonical map. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The `i`-th value of the constant assignment: the constant function on `P` at `b ‘ i`. -/
noncomputable def constantAssignmentValue (P b i : V) : V := constantGraph P (b ‘ i)

instance constantAssignmentValue_definable : ℒₛₑₜ-function₃[V] constantAssignmentValue := by
  have h : ℒₛₑₜ-relation₄ (fun y P b i : V ↦ ∃ z, z = b ‘ i ∧ y = constantGraph P z) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = constantAssignmentValue (v 1) (v 2) (v 3) ↔ _
  unfold constantAssignmentValue
  constructor
  · intro hy
    exact ⟨_, rfl, hy⟩
  · rintro ⟨z, hz, hy⟩
    rw [hy, hz]

/-- The assignment of constant functions attached to an assignment in `A`. -/
noncomputable def constantAssignment (P n b : V) : V :=
  definableGraph n (constantAssignmentValue P b) (by definability)

instance constantAssignment_isFunction (P n b : V) : IsFunction (constantAssignment P n b) :=
  definableGraph_isFunction _ _ _

@[simp] theorem domain_constantAssignment (P n b : V) :
    domain (constantAssignment P n b) = n :=
  domain_definableGraph _ _ _

theorem value_constantAssignment {P n b i : V} (hi : i ∈ n) :
    (constantAssignment P n b) ‘ i = constantGraph P (b ‘ i) :=
  value_definableGraph n (constantAssignmentValue P b) (by definability) hi

theorem constantAssignment_mem_function {P A n b : V} (hb : b ∈ A ^ n) :
    constantAssignment P n b ∈ (A ^ P) ^ n := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  exact constantGraph_mem_ultraFunctions (function_value_mem hb hi)

/-- At every index the constant assignment evaluates back to the assignment it came from. -/
theorem pointwiseAssignment_constantAssignment {P A n b p : V} (hb : b ∈ A ^ n) (hp : p ∈ P) :
    pointwiseAssignment n (constantAssignment P n b) p = b := by
  apply function_eq_of_values
    (pointwiseAssignment_mem_function (constantAssignment_mem_function (A := A) hb) hp) hb
  intro i hi
  rw [value_pointwiseAssignment hi, value_constantAssignment hi, value_constantGraph P _ hp]

/-- Collapsing the constant assignment is the same as composing with the canonical map. -/
theorem compose_constantAssignment {P U A n b : V} (hb : b ∈ A ^ n)
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P)) :
    compose (constantAssignment P n b) (ultraCollapse P U A) =
      compose b (ultraEmbedding P U A) := by
  have hc : constantAssignment P n b ∈ (A ^ P) ^ n := constantAssignment_mem_function (A := A) hb
  have hcol : ultraCollapse P U A ∈ (ultraTarget P U A) ^ (A ^ P) := ultraCollapse_mem_function hwf
  have hemb : ultraEmbedding P U A ∈ (ultraTarget P U A) ^ A := ultraEmbedding_mem_function hwf
  apply function_eq_of_values (compose_function hc hcol) (compose_function hb hemb)
  intro i hi
  rw [value_compose_of_mem_function hc hcol hi, value_compose_of_mem_function hb hemb hi,
    value_constantAssignment hi, value_ultraEmbedding (function_value_mem hb hi)]

/-- The index set of a formula at a constant assignment is all of `P` when the formula holds. -/
theorem losSet_constantAssignment_of_holds {P A n φ b : V} (hb : b ∈ A ^ n)
    (h : MembershipSatisfies A n φ b) : losSet P A n φ (constantAssignment P n b) = P := by
  apply mem_ext
  intro p
  rw [mem_losSet_iff]
  refine ⟨fun hq ↦ hq.1, fun hq ↦ ⟨hq, ?_⟩⟩
  rw [pointwiseAssignment_constantAssignment hb hq]
  exact h

/-- And it is empty when the formula fails. -/
theorem losSet_constantAssignment_of_not_holds {P A n φ b : V} (hb : b ∈ A ^ n)
    (h : ¬MembershipSatisfies A n φ b) : losSet P A n φ (constantAssignment P n b) = (∅ : V) := by
  apply mem_ext
  intro p
  constructor
  · intro hq
    obtain ⟨hp, hs⟩ := mem_losSet_iff.mp hq
    rw [pointwiseAssignment_constantAssignment hb hp] at hs
    exact absurd hs h
  · intro hq
    exact absurd hq not_mem_empty

/-- Los's theorem at a constant assignment: the ultrapower satisfies a formula of the embedded
assignment exactly when the base does. -/
theorem membershipSatisfies_ultraTarget_iff (hAC : InternalChoice V) {P U A κ : V} [IsOrdinal κ]
    [IsTransitive A] (hU : IsSetUltrafilter P U) (hcomp : IsOrdinalCompleteOn P κ U)
    (hω : (ω : V) ∈ κ) (hA : IsNonempty A) {n φ b : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ A ^ n) :
    MembershipSatisfies A n φ b ↔
      MembershipSatisfies (ultraTarget P U A) n φ (compose b (ultraEmbedding P U A)) := by
  have hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P) :=
    ultraMemRelation_wellFounded hAC hU hcomp hω
  have hc : constantAssignment P n b ∈ (A ^ P) ^ n := constantAssignment_mem_function (A := A) hb
  have hlos := los hAC (κ := κ) hU hcomp hω hA n hn φ hφ _ hc
  rw [compose_constantAssignment hb hwf] at hlos
  rw [hlos]
  constructor
  · intro h
    rw [losSet_constantAssignment_of_holds hb h]
    exact ultraIndex_mem hU
  · intro h
    by_contra hnot
    rw [losSet_constantAssignment_of_not_holds hb hnot] at h
    exact hU.empty_not_mem h

/-- The canonical map of the ultrapower is a coded elementary embedding of membership
structures. -/
theorem ultraEmbedding_codedMembershipEmbedding (hAC : InternalChoice V) {P U A κ : V}
    [IsOrdinal κ] [IsTransitive A] (hU : IsSetUltrafilter P U) (hcomp : IsOrdinalCompleteOn P κ U)
    (hω : (ω : V) ∈ κ) (hA : IsNonempty A) :
    IsCodedMembershipEmbedding A (ultraTarget P U A) (ultraEmbedding P U A) := by
  have hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P) :=
    ultraMemRelation_wellFounded hAC hU hcomp hω
  refine ⟨membershipStructureCode_valid hA,
    membershipStructureCode_valid (ultraTarget_nonempty hwf hA), ?_, ?_⟩
  · simpa using ultraEmbedding_mem_function hwf
  · intro n hn φ hφ b hb
    rw [membershipStructureCode_domain] at hb
    exact membershipSatisfies_ultraTarget_iff hAC (κ := κ) hU hcomp hω hA hn hφ hb

/-- External form: every first order formula of set theory is preserved and reflected. -/
theorem ultraEmbedding_eval (hAC : InternalChoice V) {P U A κ : V} [IsOrdinal κ] [IsTransitive A]
    (hU : IsSetUltrafilter P U) (hcomp : IsOrdinalCompleteOn P κ U) (hω : (ω : V) ∈ κ)
    (hA : IsNonempty A) {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → SetDomain A) :
    φ.Evalb b ↔
      φ.Evalb ((ultraEmbedding_codedMembershipEmbedding hAC hU hcomp hω hA (κ := κ)).toFunction ∘ b) :=
  (ultraEmbedding_codedMembershipEmbedding hAC hU hcomp hω hA (κ := κ)).eval_semisentence φ b

end ZFVP
