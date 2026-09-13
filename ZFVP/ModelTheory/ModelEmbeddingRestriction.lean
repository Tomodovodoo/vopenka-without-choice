import ZFVP.ModelTheory.RankEmbeddingRestriction
import ZFVP.ModelTheory.TransitiveZFCoding

/-! Restriction preserves all internal formula codes between transitive ZF models. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {U W f : V} [IsTransitive U] [IsTransitive W]
  [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
  [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem modelEmbedding_setSatisfaction (h : IsCodedMembershipEmbedding U W f)
    {a n φ b : V} (ha : a ∈ U) (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ a ^ n) :
    MembershipSatisfies a n φ b ↔ MembershipSatisfies (f ‘ a) n φ (compose b f) := by
  let := TransitiveZF.sequenceSupport U
  let := TransitiveZF.sequenceSupport W
  have hnU : n ∈ U := IsCodingSupport.natural_mem hφ.context
  have hφU : φ ∈ U := membershipFormulaCode_formula_mem_support hφ
  have hsub : a ⊆ U := IsTransitive.transitive a ha
  have hbU : b ∈ U := function_mem_sequenceSupport hsub hφ.context hb
  have hbtyped : b ∈ U ^ n := mem_function_of_mem_function_of_subset hb hsub
  let v : Fin 4 → SetDomain U := ![⟨a, ha⟩, ⟨n, hnU⟩, ⟨φ, hφU⟩, ⟨b, hbU⟩]
  have hs : piOneMembershipTruthFormula.Evalb v ↔ MembershipSatisfies a n φ b :=
    (Defined.eval_iff _).trans (TransitiveZF.satisfies_iff U (v 0) (v 1) (v 2) (v 3))
  have ht : piOneMembershipTruthFormula.Evalb (h.toFunction ∘ v) ↔
      MembershipSatisfies (f ‘ a) (f ‘ n) (f ‘ φ) (f ‘ b) :=
    (Defined.eval_iff _).trans (TransitiveZF.satisfies_iff W
      (h.toFunction (v 0)) (h.toFunction (v 1)) (h.toFunction (v 2)) (h.toFunction (v 3)))
  have he := hs.symm.trans ((h.eval_semisentence piOneMembershipTruthFormula v).trans ht)
  rw [h.value_natural hφ.context, h.value_formulaCode hφ, h.value_assignment hφ.context hbU hbtyped] at he
  exact he

theorem modelEmbedding_restrict (h : IsCodedMembershipEmbedding U W f)
    {a : V} (ha : a ∈ U) (hne : IsNonempty a) :
    IsCodedMembershipEmbedding a (f ‘ a) (f ↾ a) := by
  have himage : IsNonempty (f ‘ a) := by
    obtain ⟨x, hx⟩ := hne.nonempty
    exact ⟨⟨f ‘ x, (h.value_mem_iff
      ((inferInstance : IsTransitive U).mem_trans hx ha) ha).mpr hx⟩⟩
  refine ⟨membershipStructureCode_valid hne, membershipStructureCode_valid himage,
    by simpa using h.restriction_function ha, ?_⟩
  intro n hn φ hφ b hb
  have hb' : b ∈ a ^ n := by simpa using hb
  have he := modelEmbedding_setSatisfaction h ha ((mem_formulaSet_iff _ _ _ _).mp hφ) hb'
  rw [← graph_compose_restrict hb' f] at he
  exact he

end ZFVP
