import ZFVP.ModelTheory.SchmerlInternalBooleanTransport
import ZFVP.ModelTheory.SchmerlInternalSubstitutionTransport

/-! Capture-avoiding simultaneous substitution as an internal proof rule.
The premise is interpreted under every assignment. Its code is physically
stored in the conclusion node, giving the strict internal rank decrease. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

def IsSubstitutionProofNode (L F D d : V) : Prop := ∃ H s φ p,
  IsFragment L H ∧ IsSubstitutionState L ∅ ∅ s ∧
  ⟨stateSource s, φ⟩ₖ ∈ H ∧ ⟨stateTarget s, substituteCode L H s φ⟩ₖ ∈ F ∧
  p ∈ D ∧ kpair.π₁ p = ⟨stateSource s, φ⟩ₖ ∧
  d = booleanProofNode (stateTarget s) (substituteCode L H s φ) 9 ⟨H, ⟨s, p⟩ₖ⟩ₖ

instance isSubstitutionProofNode_definable : ℒₛₑₜ-relation₄[V] IsSubstitutionProofNode := by
  unfold IsSubstitutionProofNode
  definability

theorem IsSubstitutionProofNode.label_mem {L F D d : V} (h : IsSubstitutionProofNode L F D d) :
    kpair.π₁ d ∈ F := by
  obtain ⟨H, s, φ, p, _, _, _, hlabel, _, _, rfl⟩ := h
  simpa only [booleanProofNode_label] using hlabel

theorem IsSubstitutionProofNode.sound {L F D M d : V} (h : IsSubstitutionProofNode L F D d)
    (hF : IsFragment L F) (hM : IsStructureCode L M)
    (hlabels : ∀ p ∈ D, kpair.π₁ p ∈ F)
    (ih : ∀ p ∈ D, rank p ∈ rank d →
      ∀ b ∈ structureDomain M ^ kpair.π₁ (kpair.π₁ p),
        Holds L F M (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ (kpair.π₁ p)) b) :
    ∀ b ∈ structureDomain M ^ kpair.π₁ (kpair.π₁ d),
      Holds L F M (kpair.π₁ (kpair.π₁ d)) (kpair.π₂ (kpair.π₁ d)) b := by
  obtain ⟨H, s, φ, p, hH, hs, hφ, hχ, hp, hl, rfl⟩ := h
  have hr : rank p ∈ rank ⟨H, ⟨s, p⟩ₖ⟩ₖ :=
    IsOrdinal.toIsTransitive.mem_trans (rank_kpair_right_lt s p) (rank_kpair_right_lt H ⟨s, p⟩ₖ)
  have hi := ih p hp (booleanProofNode_premise_rank hr)
  have hpF := hlabels p hp
  rw [hl] at hpF
  simp only [hl, kpair.π₁_kpair, kpair.π₂_kpair] at hi
  simp only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair]
  intro b hb
  have he : (∅ : V) ∈ structureDomain M ^ (∅ : V) := mem_function.intro (by simp) (by simp)
  have hB := compose_function hs.2.2.1 (termEvaluation_mem_function hM hs.2.1 ∅ hb he)
  apply (holds_fragment_iff hF (substitutionFragment_valid hH hs) _ _ hχ (substituteCode_mem hφ) b).mpr
  apply (holds_substituteCode hH hM hs hφ hb).mpr
  exact (holds_fragment_iff hH hF _ _ hφ hpF _).mpr (hi _ hB)

namespace EndExtension
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem substitutionProofNode_map {L F D d : V} (h : IsSubstitutionProofNode L F D d) :
    IsSubstitutionProofNode (j L) (j F) (j D) (j d) := by
  obtain ⟨H, s, φ, p, hH, hs, hφ, hχ, hp, hl, rfl⟩ := h
  refine ⟨j H, j s, j φ, j p, fragment_map j hH, ?_, ?_, ?_, (j.mem_iff _ _).mpr hp, ?_, ?_⟩
  · simpa only [j.map_empty] using j.substitutionState_map hH.1 hs
  · simpa only [j.map_kpair, j.map_stateSource] using (j.mem_iff _ _).mpr hφ
  · simpa only [j.map_kpair, j.map_stateTarget, map_substituteCode j hH hs] using (j.mem_iff _ _).mpr hχ
  · rw [← j.map_first, hl, j.map_kpair, j.map_stateSource]
  · simp only [map_booleanProofNode, j.map_stateTarget, map_substituteCode j hH hs,
      j.map_kpair, (show j (9 : V) = (9 : W) from j.map_numeral 9)]

end EndExtension
end ZFVP.Infinitary.Internal
