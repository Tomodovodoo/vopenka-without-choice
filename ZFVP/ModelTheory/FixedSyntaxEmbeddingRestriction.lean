import ZFVP.ModelTheory.BoundedSupportEmbeddingRestriction

/-! Truth-table restriction for transitive sources whose embeddings fix internal syntax. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCodedMembershipEmbedding

variable {A B f a : V} [hA : IsTransitive A] [IsTransitive B]

theorem value_sequenceSupport_of_transitive (h : IsCodedMembershipEmbedding A B f)
    {U : V} (hU : U ∈ A) (hs : IsSequenceSupport U) : IsSequenceSupport (f ‘ U) :=
  (h.bounded_defined_iff sequenceSupportFormula_bounded (fun v ↦ IsSequenceSupport (v 0))
    ![U] (by simp [hU])).mp hs

theorem value_assignment_of_fixed_naturals (h : IsCodedMembershipEmbedding A B f)
    (hfix : ∀ n ∈ (ω : V), n ∈ A ∧ f ‘ n = n)
    {n b : V} (hn : n ∈ (ω : V)) (hbA : b ∈ A) (hb : b ∈ A ^ n) :
    f ‘ b = compose b f := by
  have hfun : IsFunction b := IsFunction.of_mem hb
  have hm := h.value_function_domain hbA (hfix n hn).1 hfun (domain_eq_of_mem_function hb)
  have : IsFunction (f ‘ b) := hm.1
  have : IsFunction (compose b f) := IsFunction.of_mem (compose_function hb h.function)
  apply functions_eq_of_domain_values
  · rw [hm.2, (hfix n hn).2, domain_eq_of_mem_function (compose_function hb h.function)]
  · intro i hi
    have hin : i ∈ n := by simpa [hm.2, (hfix n hn).2] using hi
    have hiω := IsOrdinal.toIsTransitive.mem_trans hin hn
    have he := h.value_apply hbA (hfix n hn).1 hfun (domain_eq_of_mem_function hb) hin
    rw [(hfix i hiω).2] at he
    exact he.trans (value_compose_of_mem_function hb h.function hin).symm

theorem value_membershipTruthTable_of_fixed_family (h : IsCodedMembershipEmbedding A B f)
    (ha : a ∈ A) {U : V} (hU : U ∈ A) [hUS : IsSequenceSupport U] (haU : a ⊆ U)
    (hω : (ω : V) ∈ A)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ A)
    (hfixF : f ‘ (formulaFamily membershipLanguageCode ∅ : V) = formulaFamily membershipLanguageCode ∅)
    {T : V} (hT : T ∈ A) (ht : IsMembershipTruthTable a T) :
    IsMembershipTruthTable (f ‘ a) (f ‘ T) := by
  let := h.value_sequenceSupport_of_transitive hU hUS
  have hs := (eval_membershipTruthTableFormula haU T).mpr ht
  have he := (h.bounded_formula_iff membershipTruthTableFormula_bounded
    ![U, ω, formulaFamily membershipLanguageCode ∅, a, T]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hU, hω, hF, hT])).mp hs
  have hv : (fun i ↦ f ‘ (![U, ω, formulaFamily membershipLanguageCode ∅, a, T] i)) =
      ![f ‘ U, f ‘ (ω : V), f ‘ (formulaFamily membershipLanguageCode ∅ : V), f ‘ a, f ‘ T] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) m) l) k) j) i
  rw [hv, h.value_omega hω, hfixF] at he
  exact (eval_membershipTruthTableFormula (h.value_subset ha hU haU) (f ‘ T)).mp he

theorem setSatisfaction_of_fixed_syntax_truthTable (h : IsCodedMembershipEmbedding A B f)
    (ha : a ∈ A) {U : V} (hU : U ∈ A) [hUS : IsSequenceSupport U] (haU : a ⊆ U)
    (hω : (ω : V) ∈ A)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ A)
    (hfixF : f ‘ (formulaFamily membershipLanguageCode ∅ : V) = formulaFamily membershipLanguageCode ∅)
    (hfixNat : ∀ n ∈ (ω : V), n ∈ A ∧ f ‘ n = n)
    (hfixCode : ∀ n φ : V, IsMembershipFormulaCode n φ → φ ∈ A ∧ f ‘ φ = φ)
    {T : V} (hT : T ∈ A) (ht : IsMembershipTruthTable a T)
    {n φ b : V} (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ a ^ n) :
    MembershipSatisfies a n φ b ↔ MembershipSatisfies (f ‘ a) n φ (compose b f) := by
  let := h.value_sequenceSupport_of_transitive hU hUS
  have hnA := (hfixNat n hφ.context).1
  have hφA := (hfixCode n φ hφ).1
  have hbA : b ∈ A := hA.mem_trans (function_mem_sequenceSupport haU hφ.context hb) hU
  have hbt : b ∈ A ^ n := mem_function_of_mem_function_of_subset hb (hA.transitive a ha)
  have hfb : f ‘ b ∈ (f ‘ a) ^ n := by
    simpa only [(hfixNat n hφ.context).2] using h.value_function hbA hnA ha hb
  have ht' := h.value_membershipTruthTable_of_fixed_family ha hU haU hω hF hfixF hT ht
  have he := h.bounded_formula_iff (boundedTableAnswerFormula_bounded true)
    ![U, T, n, φ, b] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hU, hT, hnA, hφA, hbA])
  have hv : (fun i ↦ f ‘ (![U, T, n, φ, b] i)) = ![f ‘ U, f ‘ T, f ‘ n, f ‘ φ, f ‘ b] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) m) l) k) j) i
  rw [hv, (hfixNat n hφ.context).2, (hfixCode n φ hφ).2] at he
  rw [eval_truthTableAnswer ht hφ hb, eval_truthTableAnswer ht' hφ hfb,
    h.value_assignment_of_fixed_naturals hfixNat hφ.context hbA hbt] at he
  exact he

theorem restrict_of_fixed_syntax_truthTable (h : IsCodedMembershipEmbedding A B f)
    (hne : IsNonempty a) (ha : a ∈ A) {U : V} (hU : U ∈ A)
    [hUS : IsSequenceSupport U] (haU : a ⊆ U)
    (hω : (ω : V) ∈ A)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ A)
    (hfixF : f ‘ (formulaFamily membershipLanguageCode ∅ : V) = formulaFamily membershipLanguageCode ∅)
    (hfixNat : ∀ n ∈ (ω : V), n ∈ A ∧ f ‘ n = n)
    (hfixCode : ∀ n φ : V, IsMembershipFormulaCode n φ → φ ∈ A ∧ f ‘ φ = φ)
    {T : V} (hT : T ∈ A) (ht : IsMembershipTruthTable a T) :
    IsCodedMembershipEmbedding a (f ‘ a) (f ↾ a) := by
  have himage : IsNonempty (f ‘ a) := by
    obtain ⟨x, hx⟩ := hne.nonempty
    exact ⟨f ‘ x, (h.value_mem_iff (hA.mem_trans hx ha) ha).mpr hx⟩
  refine ⟨membershipStructureCode_valid hne, membershipStructureCode_valid himage,
    by simpa using h.restriction_function ha, ?_⟩
  intro n hn φ hφ b hb
  have hb' : b ∈ a ^ n := by simpa using hb
  have he := h.setSatisfaction_of_fixed_syntax_truthTable ha hU haU hω hF hfixF hfixNat hfixCode hT ht
    ((mem_formulaSet_iff _ _ _ _).mp hφ) hb'
  rw [← graph_compose_restrict hb' f] at he
  exact he

end IsCodedMembershipEmbedding

end ZFVP
