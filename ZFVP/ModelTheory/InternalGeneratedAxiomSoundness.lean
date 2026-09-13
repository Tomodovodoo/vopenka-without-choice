import ZFVP.ModelTheory.InternalGeneratedAxiomProgram

/-! Every internally accepted enumerated axiom is a true sentence in each coded ZF+VP model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def NaturalSentenceTrue (U c : V) : Prop :=
  requirementFits ((formulaRequirement false).evalSet c) 0 ∧ MembershipSatisfies U 0 (decodedNaturalFormula c) ∅

instance naturalSentenceTrue_definable : ℒₛₑₜ-relation[V] NaturalSentenceTrue := by
  unfold NaturalSentenceTrue
  definability

theorem naturalSuccessor_injective {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V))
    (he : succ a = succ b) : a = b := by
  have : IsOrdinal a := IsOrdinal.of_mem ha
  have : IsOrdinal b := IsOrdinal.of_mem hb
  simpa only [sUnion_succ_of_transitive] using congrArg sUnion he

theorem naturalSentenceTrue_fixed {U : V} (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes)
    (ψ : SetTheorySentence) (hψ : ψ ∈ fixedZFTheory) : NaturalSentenceTrue U (Encodable.encode ψ : V) := by
  refine ⟨?_, ?_⟩
  · exact requirementFits_encode false Empty.elim ψ
  · rw [decodedNaturalFormula_membership]
    have hax : IsZFVPOpenAxiom (0 : V) (encodeMembershipFormula ψ) := Or.inl (Or.inl ⟨rfl, fixedZFTheory_encode hψ⟩)
    exact (hU.2 0 _ ((mem_zfVPOpenAxiomCodes_iff _ _).mpr hax)).2 ∅
      (by apply mem_function.intro <;> simp [zero_def])

theorem naturalSentenceTrue_fixed_some {U c : V} (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes)
    (hc : c ∈ (ω : V)) (ψ : SetTheorySentence) (hψ : ψ ∈ fixedZFTheory)
    (he : ((Encodable.encode ψ + 1 : ℕ) : V) = succ c) : NaturalSentenceTrue U c := by
  rw [num_succ_def] at he
  have heq := naturalSuccessor_injective (by simp) hc he
  rw [← heq]
  exact naturalSentenceTrue_fixed hU ψ hψ

theorem naturalSentenceTrue_template_some {a : ℕ} (t : MembershipTemplate a 0) {U k c φ : V}
    (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes) (hk : k ∈ (ω : V)) (hc : c ∈ (ω : V)) (hφ : φ ∈ (ω : V))
    (he : (templateOptionProgram t).evalSet (naturalSquarePair k c) = succ φ)
    (hax : requirementFits ((formulaRequirement false).evalSet c) (prefixSize a k) →
      IsZFVPOpenAxiom k (t.compileTail k (decodedNaturalFormula c))) : NaturalSentenceTrue U φ := by
  obtain ⟨hv, heq⟩ := (evalSet_templateOptionProgram_some t hk hc hφ).mp he
  rw [← heq]
  refine ⟨t.closedTailProgram_requirementFits hk hc hv, t.membershipSatisfies_closedTailProgram hk hc hv ?_⟩
  exact (hU.2 k _ ((mem_zfVPOpenAxiomCodes_iff _ _).mpr (hax hv))).2

theorem naturalSentenceTrue_separation_some {U k c φ : V}
    (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes) (hk : k ∈ (ω : V)) (hc : c ∈ (ω : V)) (hφ : φ ∈ (ω : V))
    (he : (templateOptionProgram separationTemplate).evalSet (naturalSquarePair k c) = succ φ) : NaturalSentenceTrue U φ := by
  apply naturalSentenceTrue_template_some separationTemplate hU hk hc hφ he
  intro hv
  have hvalid := decodedNaturalFormula_valid false hc (ω_succ_closed hk) hv
  exact Or.inl (Or.inr (Or.inl ⟨hk, decodedNaturalFormula c, (mem_formulaSet_iff _ _ _ _).mp hvalid, rfl⟩))

theorem naturalSentenceTrue_replacement_some {U k c φ : V}
    (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes) (hk : k ∈ (ω : V)) (hc : c ∈ (ω : V)) (hφ : φ ∈ (ω : V))
    (he : (templateOptionProgram replacementTemplate).evalSet (naturalSquarePair k c) = succ φ) : NaturalSentenceTrue U φ := by
  apply naturalSentenceTrue_template_some replacementTemplate hU hk hc hφ he
  intro hv
  have hvalid := decodedNaturalFormula_valid false hc (ω_succ_closed (ω_succ_closed hk)) hv
  exact Or.inl (Or.inr (Or.inr ⟨hk, decodedNaturalFormula c, (mem_formulaSet_iff _ _ _ _).mp hvalid, rfl⟩))

theorem naturalSentenceTrue_vopenka_some {U c φ : V}
    (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes) (hc : c ∈ (ω : V)) (hφ : φ ∈ (ω : V))
    (he : (templateOptionProgram vopenkaTemplate).evalSet (naturalSquarePair 0 c) = succ φ) : NaturalSentenceTrue U φ := by
  apply naturalSentenceTrue_template_some vopenkaTemplate hU (by simp) hc hφ he
  intro hv
  rw [prefixSize_zero] at hv
  have hvalid := decodedNaturalFormula_valid false hc (n := (2 : V)) (by simp) hv
  rw [MembershipTemplate.compileTail_zero]
  exact Or.inr ⟨rfl, (mem_vopenkaAxiomCodes_iff _).mpr
    ⟨decodedNaturalFormula c, (mem_formulaSet_iff _ _ _ _).mp hvalid, rfl⟩⟩

set_option maxHeartbeats 800000 in
theorem generatedAxiomProgram_sound {U tag k c φ : V}
    (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes)
    (ht : tag ∈ (ω : V)) (hk : k ∈ (ω : V)) (hc : c ∈ (ω : V)) (hφ : φ ∈ (ω : V))
    (he : generatedAxiomProgram.evalSet (naturalSquarePair tag (naturalSquarePair k c)) = succ φ) :
    NaturalSentenceTrue U φ := by
  rw [evalSet_generatedAxiomProgram ht hk hc] at he
  unfold naturalGeneratedAxiomValue at he
  split_ifs at he with h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · exact naturalSentenceTrue_fixed_some hU hφ Axiom.empty (by simp [fixedZFTheory]) he
  · exact naturalSentenceTrue_fixed_some hU hφ Axiom.extentionality (by simp [fixedZFTheory]) he
  · exact naturalSentenceTrue_fixed_some hU hφ Axiom.pairing (by simp [fixedZFTheory]) he
  · exact naturalSentenceTrue_fixed_some hU hφ Axiom.union (by simp [fixedZFTheory]) he
  · exact naturalSentenceTrue_fixed_some hU hφ Axiom.power (by simp [fixedZFTheory]) he
  · exact naturalSentenceTrue_fixed_some hU hφ Axiom.infinity (by simp [fixedZFTheory]) he
  · exact naturalSentenceTrue_fixed_some hU hφ Axiom.foundation (by simp [fixedZFTheory]) he
  · exact naturalSentenceTrue_fixed_some hU hφ equalityBasisSentence (by simp [fixedZFTheory]) he
  · exact naturalSentenceTrue_separation_some hU hk hc hφ he
  · exact naturalSentenceTrue_replacement_some hU hk hc hφ he
  · exact naturalSentenceTrue_vopenka_some hU hc hφ he
  · have hz : φ ∈ (0 : V) := by rw [he]; exact mem_succ_self φ
    exact (not_mem_empty hz).elim

theorem generatedAxiomCheck_sound {U φ e : V} (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes)
    (hφ : φ ∈ (ω : V)) (he : e ∈ (ω : V))
    (hcheck : generatedAxiomCheck.evalSet (naturalSquarePair φ e) = 1) : NaturalSentenceTrue U φ := by
  have h := (evalSet_generatedAxiomCheck hφ he).mp hcheck
  obtain ⟨tag, ht, tail, htail, rfl⟩ := naturalSquarePair_surjective he
  obtain ⟨k, hk, c, hc, rfl⟩ := naturalSquarePair_surjective htail
  exact generatedAxiomProgram_sound hU ht hk hc hφ h

end ZFVP
