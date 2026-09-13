import ZFVP.ModelTheory.SchmerlInternalCoreProofs
import ZFVP.ModelTheory.SchmerlInternalQUnion
import ZFVP.ModelTheory.SchmerlInternalQTwoPoints
import ZFVP.ModelTheory.SchmerlInternalQInterchangeTransport
import ZFVP.ModelTheory.SchmerlInternalSubstitutionRule
import ZFVP.ModelTheory.SchmerlInternalFOCoherence
import ZFVP.ModelTheory.SchmerlInternalInstantiation
import ZFVP.ModelTheory.SchmerlInternalEqualityAxioms
import ZFVP.ModelTheory.SchmerlInternalOrdinaryQuantifierAxioms

/-! Internal derivations with Q countable union, two-points, interchange
and capture-avoiding simultaneous substitution, with finite first-order
constructor coherence, ordinary quantifier instantiation, logical equality
and an explicit nonempty-domain axiom, universal distribution and vacuous generalization.
Proof validity is syntactic. Soundness uses internal Choice and a valid
structure code. Completeness and proof transformations remain separate obligations. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsInternalProofNode (L Γ F D d : V) : Prop :=
  IsCoreProofNode Γ F D d ∨ (∃ n φ, ⟨n, φ⟩ₖ ∈ F ∧
    d = booleanProofNode n φ 6 ∅ ∧ IsQUnionAxiom φ) ∨
  (∃ n φ, ⟨n, φ⟩ₖ ∈ F ∧ d = booleanProofNode n φ 7 ∅ ∧ IsQTwoPointsAxiom n φ) ∨
  (∃ n φ, ⟨n, φ⟩ₖ ∈ F ∧ d = booleanProofNode n φ 8 ∅ ∧ IsQInterchangeAxiom L n φ) ∨
  IsSubstitutionProofNode L F D d ∨
  (∃ n φ, ⟨n, φ⟩ₖ ∈ F ∧ d = booleanProofNode n φ 10 ∅ ∧ IsFOCoherenceAxiom L n φ) ∨
  (∃ n φ, ⟨n, φ⟩ₖ ∈ F ∧ d = booleanProofNode n φ 11 ∅ ∧ IsQuantifierInstantiationAxiom L n φ) ∨
  (∃ n φ, ⟨n, φ⟩ₖ ∈ F ∧ d = booleanProofNode n φ 12 ∅ ∧ IsEqualityAxiom L n φ) ∨
  ∃ n φ, ⟨n, φ⟩ₖ ∈ F ∧ d = booleanProofNode n φ 13 ∅ ∧ IsOrdinaryQuantifierAxiom L n φ

instance isInternalProofNode_definable :
    Language.DefinableRel₅ ℒₛₑₜ (IsInternalProofNode : V → V → V → V → V → Prop) := by
  unfold IsInternalProofNode
  definability

def IsInternalProof (L Γ F D : V) : Prop :=
  IsFragment L F ∧ Γ ⊆ F ∧ ∀ d ∈ D, IsInternalProofNode L Γ F D d

instance isInternalProof_definable : ℒₛₑₜ-relation₄[V] IsInternalProof := by
  unfold IsInternalProof
  definability

theorem IsInternalProofNode.label_mem {L Γ F D d : V} (h : IsInternalProofNode L Γ F D d) :
    kpair.π₁ d ∈ F := by
  rcases h with h | ⟨n, φ, hφ, rfl, _⟩ | ⟨n, φ, hφ, rfl, _⟩ | ⟨n, φ, hφ, rfl, _⟩ |
    hs | ⟨n, φ, hφ, rfl, _⟩ | ⟨n, φ, hφ, rfl, _⟩ | ⟨n, φ, hφ, rfl, _⟩ | ⟨n, φ, hφ, rfl, _⟩
  · exact h.label_mem
  · simpa only [booleanProofNode_label] using hφ
  · simpa only [booleanProofNode_label] using hφ
  · simpa only [booleanProofNode_label] using hφ
  · exact hs.label_mem
  · simpa only [booleanProofNode_label] using hφ
  · simpa only [booleanProofNode_label] using hφ
  · simpa only [booleanProofNode_label] using hφ
  · simpa only [booleanProofNode_label] using hφ

theorem IsCoreProof.toInternal {L Γ F D : V} (h : IsCoreProof L Γ F D) :
    IsInternalProof L Γ F D := ⟨h.1, h.2.1, fun d hd ↦ Or.inl (h.2.2 d hd)⟩

theorem IsInternalProof.sound {L Γ F D M : V} (h : IsInternalProof L Γ F D)
    (hM : IsStructureCode L M) (hAC : InternalChoice V)
    (hΓ : ∀ n φ, ⟨n, φ⟩ₖ ∈ Γ → ∀ b ∈ structureDomain M ^ n, Holds L F M n φ b) :
    ∀ d ∈ D, ∀ b ∈ structureDomain M ^ kpair.π₁ (kpair.π₁ d),
      Holds L F M (kpair.π₁ (kpair.π₁ d)) (kpair.π₂ (kpair.π₁ d)) b := by
  apply projectedRank_induction D id (by definability)
    (fun d ↦ ∀ b ∈ structureDomain M ^ kpair.π₁ (kpair.π₁ d),
      Holds L F M (kpair.π₁ (kpair.π₁ d)) (kpair.π₂ (kpair.π₁ d)) b)
    (by unfold Holds; definability)
  intro d hd ih
  rcases h.2.2 d hd with hh | ⟨n, φ, hφ, rfl, hax⟩ | ⟨n, φ, hφ, rfl, hax⟩ |
    ⟨n, φ, hφ, rfl, hax⟩ | hs | ⟨n, φ, hφ, rfl, hax⟩ | ⟨n, φ, hφ, rfl, hax⟩ | ⟨n, φ, hφ, rfl, hax⟩ | ⟨n, φ, hφ, rfl, hax⟩
  · exact hh.sound h.1 (fun p hp ↦ (h.2.2 p hp).label_mem) hΓ ih
  · simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using
      (fun b hb ↦ hax.sound hAC h.1 hφ hb)
  · simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using
      (fun b hb ↦ hax.sound h.1 hφ hb)
  · simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using
      (fun b hb ↦ hax.sound h.1 hM hAC hφ hb)
  · exact hs.sound h.1 hM (fun p hp ↦ (h.2.2 p hp).label_mem) ih
  · simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using
      (fun b hb ↦ hax.sound h.1 hφ hb)
  · simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using
      (fun b hb ↦ hax.sound h.1 hM hφ hb)
  · simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using
      (fun b hb ↦ hax.sound h.1 hM hφ hb)
  · simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using
      (fun b hb ↦ hax.sound h.1 hM hφ hb)

def IsInternalDerivationCode (L Γ n φ c : V) : Prop := ∃ F D d,
  c = ⟨F, ⟨D, d⟩ₖ⟩ₖ ∧ IsInternallyCountable F ∧ IsInternallyCountable D ∧
  IsInternalProof L Γ F D ∧ d ∈ D ∧ kpair.π₁ d = ⟨n, φ⟩ₖ

instance isInternalDerivationCode_definable :
    Language.DefinableRel₅ ℒₛₑₜ (IsInternalDerivationCode : V → V → V → V → V → Prop) := by
  unfold IsInternalDerivationCode
  definability

theorem IsInternalDerivationCode.sound {L Γ n φ c M : V} (h : IsInternalDerivationCode L Γ n φ c)
    (hM : IsStructureCode L M) (hAC : InternalChoice V)
    (hΓ : ∀ k ψ, ⟨k, ψ⟩ₖ ∈ Γ → ∀ b ∈ structureDomain M ^ k,
      Holds L (kpair.π₁ c) M k ψ b) :
    ∀ b ∈ structureDomain M ^ n, Holds L (kpair.π₁ c) M n φ b := by
  obtain ⟨F, D, d, rfl, _, _, hp, hd, hl⟩ := h
  simp only [kpair.π₁_kpair] at hΓ ⊢
  simpa only [hl, kpair.π₁_kpair, kpair.π₂_kpair] using hp.sound hM hAC hΓ d hd

namespace EndExtension
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem internalProofNode_map {L Γ F D d : V} (h : IsInternalProofNode L Γ F D d) :
    IsInternalProofNode (j L) (j Γ) (j F) (j D) (j d) := by
  rcases h with hh | ⟨n, φ, hφ, rfl, hax⟩ | ⟨n, φ, hφ, rfl, hax⟩ |
    ⟨n, φ, hφ, rfl, hax⟩ | hs | ⟨n, φ, hφ, rfl, hax⟩ | ⟨n, φ, hφ, rfl, hax⟩ | ⟨n, φ, hφ, rfl, hax⟩ | ⟨n, φ, hφ, rfl, hax⟩
  · exact Or.inl (coreProofNode_map j hh)
  · refine Or.inr (Or.inl ⟨j n, j φ, ?_, ?_, qUnionAxiom_map j hax⟩)
    · rw [← j.map_kpair, j.mem_iff]; exact hφ
    · simp only [map_booleanProofNode, (show j (6 : V) = (6 : W) from j.map_numeral 6), j.map_empty]
  · refine Or.inr (Or.inr (Or.inl ⟨j n, j φ, ?_, ?_, qTwoPointsAxiom_map j hax⟩))
    · rw [← j.map_kpair, j.mem_iff]; exact hφ
    · simp only [map_booleanProofNode, (show j (7 : V) = (7 : W) from j.map_numeral 7), j.map_empty]
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨j n, j φ, ?_, ?_, qInterchangeAxiom_map j hax⟩)))
    · rw [← j.map_kpair, j.mem_iff]; exact hφ
    · simp only [map_booleanProofNode, (show j (8 : V) = (8 : W) from j.map_numeral 8), j.map_empty]
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (substitutionProofNode_map j hs)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j n, j φ, ?_, ?_, foCoherenceAxiom_map j hax⟩)))))
    · rw [← j.map_kpair, j.mem_iff]; exact hφ
    · simp only [map_booleanProofNode, (show j (10 : V) = (10 : W) from j.map_numeral 10), j.map_empty]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j n, j φ, ?_, ?_, quantifierInstantiationAxiom_map j hax⟩))))))
    · rw [← j.map_kpair, j.mem_iff]; exact hφ
    · simp only [map_booleanProofNode, (show j (11 : V) = (11 : W) from j.map_numeral 11), j.map_empty]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j n, j φ, ?_, ?_, equalityAxiom_map j hax⟩)))))))
    · rw [← j.map_kpair, j.mem_iff]; exact hφ
    · simp only [map_booleanProofNode, (show j (12 : V) = (12 : W) from j.map_numeral 12), j.map_empty]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j n, j φ, ?_, ?_, ordinaryQuantifierAxiom_map j hax⟩)))))))
    · rw [← j.map_kpair, j.mem_iff]; exact hφ
    · simp only [map_booleanProofNode, (show j (13 : V) = (13 : W) from j.map_numeral 13), j.map_empty]

theorem internalProof_map {L Γ F D : V} (h : IsInternalProof L Γ F D) :
    IsInternalProof (j L) (j Γ) (j F) (j D) := by
  refine ⟨fragment_map j h.1, (j.subset_iff Γ F).mpr h.2.1, ?_⟩
  intro d hd
  obtain ⟨p, hp, rfl⟩ := j.endExtension D d hd
  exact internalProofNode_map j (h.2.2 p hp)

theorem internalDerivationCode_map {L Γ n φ c : V} (h : IsInternalDerivationCode L Γ n φ c) :
    IsInternalDerivationCode (j L) (j Γ) (j n) (j φ) (j c) := by
  obtain ⟨F, D, d, rfl, hF, hD, hp, hd, hl⟩ := h
  refine ⟨j F, j D, j d, ?_, ?_, ?_, internalProof_map j hp, (j.mem_iff d D).mpr hd, ?_⟩
  · simp only [j.map_kpair]
  · simpa only [IsInternallyCountable, j.map_omega] using j.map_cardLE hF
  · simpa only [IsInternallyCountable, j.map_omega] using j.map_cardLE hD
  · rw [← j.map_first, hl, j.map_kpair]

end EndExtension
end ZFVP.Infinitary.Internal
