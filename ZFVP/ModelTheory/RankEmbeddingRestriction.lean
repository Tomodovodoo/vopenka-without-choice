import ZFVP.ModelTheory.EmbeddingAssignments
import ZFVP.ModelTheory.EmbeddingCodeFixation
import ZFVP.ModelTheory.CodedEmbeddingRestriction
import ZFVP.ModelTheory.EmbeddingAbsoluteness

/-! Restrictions of embeddings between positive C(n) ranks preserve every internal formula code. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_setSatisfaction {k l : ℕ} {δ ε f a n φ b : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (ha : a ∈ hierarchy δ) (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ a ^ n) :
    MembershipSatisfies a n φ b ↔ MembershipSatisfies (f ‘ a) n φ (compose b f) := by
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff k δ).mp hδ).2.support
  let : IsSequenceSupport (hierarchy ε) := ((cn_successor_iff l ε).mp hε).2.support
  have hnA : n ∈ hierarchy δ := IsCodingSupport.natural_mem hφ.context
  have hφA : φ ∈ hierarchy δ := membershipFormulaCode_formula_mem_support hφ
  have hsub : a ⊆ hierarchy δ := IsTransitive.transitive a ha
  have hbA : b ∈ hierarchy δ := function_mem_sequenceSupport hsub hφ.context hb
  have hbtyped : b ∈ hierarchy δ ^ n := mem_function_of_mem_function_of_subset hb hsub
  let v : Fin 4 → SetDomain (hierarchy δ) := ![⟨a, ha⟩, ⟨n, hnA⟩, ⟨φ, hφA⟩, ⟨b, hbA⟩]
  have hs := hδ.defined_correct (piOneMembershipTruthFormula_piOne.mono (by omega))
    (fun v ↦ MembershipSatisfies (v 0) (v 1) (v 2) (v 3)) v
  have ht := hε.defined_correct (piOneMembershipTruthFormula_piOne.mono (by omega))
    (fun v ↦ MembershipSatisfies (v 0) (v 1) (v 2) (v 3)) (h.toFunction ∘ v)
  have he := hs.symm.trans ((h.eval_semisentence piOneMembershipTruthFormula v).trans ht)
  change MembershipSatisfies a n φ b ↔ MembershipSatisfies (f ‘ a) (f ‘ n) (f ‘ φ) (f ‘ b) at he
  rw [h.value_natural hφ.context, h.value_formulaCode hφ, h.value_assignment hφ.context hbA hbtyped] at he
  exact he

theorem rankEmbedding_restrict {k l : ℕ} {δ ε f a : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (ha : a ∈ hierarchy δ) (hne : IsNonempty a) :
    IsCodedMembershipEmbedding a (f ‘ a) (f ↾ a) := by
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff k δ).mp hδ).2.support
  let : IsSequenceSupport (hierarchy ε) := ((cn_successor_iff l ε).mp hε).2.support
  have himage : IsNonempty (f ‘ a) := by
    obtain ⟨x, hx⟩ := hne.nonempty
    exact ⟨⟨f ‘ x, (h.value_mem_iff
      ((inferInstance : IsTransitive (hierarchy δ)).mem_trans hx ha) ha).mpr hx⟩⟩
  refine ⟨membershipStructureCode_valid hne, membershipStructureCode_valid himage,
    by simpa using h.restriction_function ha, ?_⟩
  intro n hn φ hφ b hb
  have hb' : b ∈ a ^ n := by simpa using hb
  have he := rankEmbedding_setSatisfaction hδ hε h ha ((mem_formulaSet_iff _ _ _ _).mp hφ) hb'
  rw [← graph_compose_restrict hb' f] at he
  exact he

end ZFVP
