import ZFVP.ModelTheory.LimitRankEmbedding
import ZFVP.ModelTheory.BoundedEmbeddingTables
import ZFVP.ModelTheory.CodedEmbeddingRestriction
import ZFVP.Syntax.BoundedMembershipTruthCertificate

/-! A truth table inside the source domain suffices to restrict an embedding to a coding support. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCodedMembershipEmbedding

variable {A B f a : V} [hA : IsCodingSupport A] [IsTransitive B]

theorem value_sequenceSupport (h : IsCodedMembershipEmbedding A B f) (ha : a ∈ A)
    (hs : IsSequenceSupport a) : IsSequenceSupport (f ‘ a) :=
  (h.bounded_defined_iff sequenceSupportFormula_bounded (fun v ↦ IsSequenceSupport (v 0))
    ![a] (by simp [ha])).mp hs

theorem value_membershipFamily_of_support (h : IsCodedMembershipEmbedding A B f)
    (ha : a ∈ A) [IsCodingSupport a]
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ a)
    (hiF : SetTheory.identity (formulaFamily membershipLanguageCode ∅ : V) ∈ a) :
    f ‘ (formulaFamily membershipLanguageCode ∅ : V) = formulaFamily membershipLanguageCode ∅ := by
  have hs := (eval_membershipFamilyWitnessFormula a (formulaFamily membershipLanguageCode ∅)).mpr
    ⟨inferInstance, hF, hiF, rfl⟩
  have he := (h.bounded_formula_iff membershipFamilyWitnessFormula_bounded
    ![a, formulaFamily membershipLanguageCode ∅] (by simp [ha, hA.mem_trans hF ha])).mp hs
  have hv : (fun i ↦ f ‘ (![a, formulaFamily membershipLanguageCode ∅] i)) =
      ![f ‘ a, f ‘ (formulaFamily membershipLanguageCode ∅ : V)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
  rw [hv] at he
  exact ((eval_membershipFamilyWitnessFormula _ _).mp he).2.2.2

theorem value_membershipTruthTable (h : IsCodedMembershipEmbedding A B f)
    (ha : a ∈ A) [haS : IsSequenceSupport a]
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ a)
    (hiF : SetTheory.identity (formulaFamily membershipLanguageCode ∅ : V) ∈ a)
    {T : V} (hT : T ∈ A) (ht : IsMembershipTruthTable a T) :
    IsMembershipTruthTable (f ‘ a) (f ‘ T) := by
  let := h.value_sequenceSupport ha haS
  have hs := (eval_membershipTruthTableFormula (subset_refl a) T).mpr ht
  have he := (h.bounded_formula_iff membershipTruthTableFormula_bounded
    ![a, ω, formulaFamily membershipLanguageCode ∅, a, T]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hA.omega_mem, hA.mem_trans hF ha, hT])).mp hs
  have hv : (fun i ↦ f ‘ (![a, ω, formulaFamily membershipLanguageCode ∅, a, T] i)) =
      ![f ‘ a, f ‘ (ω : V), f ‘ (formulaFamily membershipLanguageCode ∅ : V), f ‘ a, f ‘ T] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) m) l) k) j) i
  rw [hv, h.value_omega hA.omega_mem, h.value_membershipFamily_of_support ha hF hiF] at he
  exact (eval_membershipTruthTableFormula (subset_refl (f ‘ a)) (f ‘ T)).mp he

theorem setSatisfaction_of_truthTable (h : IsCodedMembershipEmbedding A B f)
    (ha : a ∈ A) [haS : IsSequenceSupport a]
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ a)
    (hiF : SetTheory.identity (formulaFamily membershipLanguageCode ∅ : V) ∈ a)
    {T : V} (hT : T ∈ A) (ht : IsMembershipTruthTable a T)
    {n φ b : V} (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ a ^ n) :
    MembershipSatisfies a n φ b ↔ MembershipSatisfies (f ‘ a) n φ (compose b f) := by
  let := h.value_sequenceSupport ha haS
  have hnA : n ∈ A := IsCodingSupport.natural_mem hφ.context
  have hφA : φ ∈ A := membershipFormulaCode_formula_mem_support hφ
  have hbA : b ∈ A := hA.mem_trans (function_mem_sequenceSupport (subset_refl a) hφ.context hb) ha
  have hbt : b ∈ A ^ n := mem_function_of_mem_function_of_subset hb (hA.transitive a ha)
  have hfb : f ‘ b ∈ (f ‘ a) ^ n := by
    simpa only [h.value_natural hφ.context] using h.value_function hbA hnA ha hb
  have ht' := h.value_membershipTruthTable ha hF hiF hT ht
  have he := h.bounded_formula_iff (boundedTableAnswerFormula_bounded true)
    ![a, T, n, φ, b] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hT, hnA, hφA, hbA])
  have hv : (fun i ↦ f ‘ (![a, T, n, φ, b] i)) = ![f ‘ a, f ‘ T, f ‘ n, f ‘ φ, f ‘ b] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) m) l) k) j) i
  rw [hv, h.value_natural hφ.context, h.value_formulaCode hφ] at he
  rw [eval_truthTableAnswer ht hφ hb, eval_truthTableAnswer ht' hφ hfb,
    h.value_assignment hφ.context hbA hbt] at he
  exact he

theorem restrict_of_truthTable (h : IsCodedMembershipEmbedding A B f)
    (ha : a ∈ A) [haS : IsSequenceSupport a]
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ a)
    (hiF : SetTheory.identity (formulaFamily membershipLanguageCode ∅ : V) ∈ a)
    {T : V} (hT : T ∈ A) (ht : IsMembershipTruthTable a T) :
    IsCodedMembershipEmbedding a (f ‘ a) (f ↾ a) := by
  have hne : IsNonempty a := ⟨ω, haS.omega_mem⟩
  have himage : IsNonempty (f ‘ a) := by
    obtain ⟨x, hx⟩ := hne.nonempty
    exact ⟨f ‘ x, (h.value_mem_iff (hA.mem_trans hx ha) ha).mpr hx⟩
  refine ⟨membershipStructureCode_valid hne, membershipStructureCode_valid himage,
    by simpa using h.restriction_function ha, ?_⟩
  intro n hn φ hφ b hb
  have hb' : b ∈ a ^ n := by simpa using hb
  have he := h.setSatisfaction_of_truthTable ha hF hiF hT ht ((mem_formulaSet_iff _ _ _ _).mp hφ) hb'
  rw [← graph_compose_restrict hb' f] at he
  exact he

end IsCodedMembershipEmbedding

end ZFVP
