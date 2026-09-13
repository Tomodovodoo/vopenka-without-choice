import ZFVP.ModelTheory.SchmerlInternalBooleanTransport
import ZFVP.ModelTheory.SchmerlInternalQuantifierAxioms

/-! The internal Boolean calculus extended by quantifier monotonicity and
universal generalization. Hypotheses are interpreted uniformly under all
assignments, so generalization has that same uniform interpretation.
Substitution, the remaining Q schemas, and completeness remain separate. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCoreProofNode (Γ F D d : V) : Prop :=
  IsBooleanProofNode Γ F D d ∨
  (∃ n φ, ⟨n, φ⟩ₖ ∈ F ∧ d = booleanProofNode n φ 4 ∅ ∧ IsQuantifierMonotonicityAxiom φ) ∨
  ∃ n φ p, ⟨n, allCode φ⟩ₖ ∈ F ∧ p ∈ D ∧
    d = booleanProofNode n (allCode φ) 5 p ∧ kpair.π₁ p = ⟨succ n, φ⟩ₖ

instance isCoreProofNode_definable : ℒₛₑₜ-relation₄[V] IsCoreProofNode := by
  unfold IsCoreProofNode
  definability

def IsCoreProof (L Γ F D : V) : Prop :=
  IsFragment L F ∧ Γ ⊆ F ∧ ∀ d ∈ D, IsCoreProofNode Γ F D d

instance isCoreProof_definable : ℒₛₑₜ-relation₄[V] IsCoreProof := by
  unfold IsCoreProof
  definability

theorem IsCoreProofNode.label_mem {Γ F D d : V} (h : IsCoreProofNode Γ F D d) :
    kpair.π₁ d ∈ F := by
  rcases h with h | ⟨n, φ, hφ, rfl, _⟩ | ⟨n, φ, p, hφ, _, rfl, _⟩
  · exact h.label_mem
  all_goals simpa only [booleanProofNode_label] using hφ

theorem IsBooleanProof.toCore {L Γ F D : V} (h : IsBooleanProof L Γ F D) :
    IsCoreProof L Γ F D := ⟨h.1, h.2.1, fun d hd ↦ Or.inl (h.2.2 d hd)⟩

theorem IsCoreProofNode.sound {L Γ F D M d : V} (h : IsCoreProofNode Γ F D d)
    (hF : IsFragment L F) (hlabels : ∀ p ∈ D, kpair.π₁ p ∈ F)
    (hΓ : ∀ n φ, ⟨n, φ⟩ₖ ∈ Γ → ∀ b ∈ structureDomain M ^ n, Holds L F M n φ b)
    (ih : ∀ p ∈ D, rank p ∈ rank d →
      ∀ b ∈ structureDomain M ^ kpair.π₁ (kpair.π₁ p),
        Holds L F M (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ (kpair.π₁ p)) b) :
    ∀ b ∈ structureDomain M ^ kpair.π₁ (kpair.π₁ d),
      Holds L F M (kpair.π₁ (kpair.π₁ d)) (kpair.π₂ (kpair.π₁ d)) b := by
  rcases h with hh | ⟨n, φ, hφ, rfl, hax⟩ | ⟨n, φ, p, hφ, hp, rfl, hl⟩
  · exact hh.sound hF hlabels hΓ ih
  · simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using
      (fun b hb ↦ hax.sound hF hφ hb)
  · have hr : rank p ∈ rank (booleanProofNode n (allCode φ) 5 p) :=
      IsOrdinal.toIsTransitive.mem_trans (rank_kpair_right_lt (5 : V) p)
        (rank_kpair_right_lt ⟨n, allCode φ⟩ₖ ⟨(5 : V), p⟩ₖ)
    have hi := ih p hp hr
    simp only [hl, kpair.π₁_kpair, kpair.π₂_kpair] at hi
    simp only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair]
    intro b hb
    apply (holds_all hF hφ hb).mpr
    intro x hx
    exact hi _ (assignmentPrepend_mem_function (hF.node hφ).1 hb hx)

theorem IsCoreProof.sound {L Γ F D M : V} (h : IsCoreProof L Γ F D)
    (hΓ : ∀ n φ, ⟨n, φ⟩ₖ ∈ Γ → ∀ b ∈ structureDomain M ^ n, Holds L F M n φ b) :
    ∀ d ∈ D, ∀ b ∈ structureDomain M ^ kpair.π₁ (kpair.π₁ d),
      Holds L F M (kpair.π₁ (kpair.π₁ d)) (kpair.π₂ (kpair.π₁ d)) b := by
  apply projectedRank_induction D id (by definability)
    (fun d ↦ ∀ b ∈ structureDomain M ^ kpair.π₁ (kpair.π₁ d),
      Holds L F M (kpair.π₁ (kpair.π₁ d)) (kpair.π₂ (kpair.π₁ d)) b)
    (by unfold Holds; definability)
  intro d hd ih
  exact (h.2.2 d hd).sound h.1 (fun p hp ↦ (h.2.2 p hp).label_mem) hΓ ih

def IsCoreDerivationCode (L Γ n φ c : V) : Prop := ∃ F D d,
  c = ⟨F, ⟨D, d⟩ₖ⟩ₖ ∧ IsInternallyCountable F ∧ IsInternallyCountable D ∧
  IsCoreProof L Γ F D ∧ d ∈ D ∧ kpair.π₁ d = ⟨n, φ⟩ₖ

instance isCoreDerivationCode_definable :
    Language.DefinableRel₅ ℒₛₑₜ (IsCoreDerivationCode : V → V → V → V → V → Prop) := by
  unfold IsCoreDerivationCode
  definability

theorem IsCoreDerivationCode.sound {L Γ n φ c M : V} (h : IsCoreDerivationCode L Γ n φ c)
    (hΓ : ∀ k ψ, ⟨k, ψ⟩ₖ ∈ Γ → ∀ b ∈ structureDomain M ^ k,
      Holds L (kpair.π₁ c) M k ψ b) :
    ∀ b ∈ structureDomain M ^ n, Holds L (kpair.π₁ c) M n φ b := by
  obtain ⟨F, D, d, rfl, _, _, hp, hd, hl⟩ := h
  simp only [kpair.π₁_kpair] at hΓ ⊢
  simpa only [hl, kpair.π₁_kpair, kpair.π₂_kpair] using hp.sound hΓ d hd

namespace EndExtension
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem coreProofNode_map {Γ F D d : V} (h : IsCoreProofNode Γ F D d) :
    IsCoreProofNode (j Γ) (j F) (j D) (j d) := by
  rcases h with hh | ⟨n, φ, hφ, rfl, hax⟩ | ⟨n, φ, p, hφ, hp, rfl, hl⟩
  · exact Or.inl (booleanProofNode_map j hh)
  · refine Or.inr (Or.inl ⟨j n, j φ, ?_, ?_, quantifierMonotonicityAxiom_map j hax⟩)
    · rw [← j.map_kpair, j.mem_iff]; exact hφ
    · simp only [map_booleanProofNode, (show j (4 : V) = (4 : W) from j.map_numeral 4), j.map_empty]
  · refine Or.inr (Or.inr ⟨j n, j φ, j p, ?_, (j.mem_iff p D).mpr hp, ?_, ?_⟩)
    · rw [← map_allCode, ← j.map_kpair, j.mem_iff]; exact hφ
    · simp only [map_booleanProofNode, map_allCode,
        (show j (5 : V) = (5 : W) from j.map_numeral 5)]
    · rw [← j.map_first, hl, j.map_kpair, j.map_succ]

theorem coreProof_map {L Γ F D : V} (h : IsCoreProof L Γ F D) :
    IsCoreProof (j L) (j Γ) (j F) (j D) := by
  refine ⟨fragment_map j h.1, (j.subset_iff Γ F).mpr h.2.1, ?_⟩
  intro d hd
  obtain ⟨p, hp, rfl⟩ := j.endExtension D d hd
  exact coreProofNode_map j (h.2.2 p hp)

theorem coreDerivationCode_map {L Γ n φ c : V} (h : IsCoreDerivationCode L Γ n φ c) :
    IsCoreDerivationCode (j L) (j Γ) (j n) (j φ) (j c) := by
  obtain ⟨F, D, d, rfl, hF, hD, hp, hd, hl⟩ := h
  refine ⟨j F, j D, j d, ?_, ?_, ?_, coreProof_map j hp, (j.mem_iff d D).mpr hd, ?_⟩
  · simp only [j.map_kpair]
  · simpa only [IsInternallyCountable, j.map_omega] using j.map_cardLE hF
  · simpa only [IsInternallyCountable, j.map_omega] using j.map_cardLE hD
  · rw [← j.map_first, hl, j.map_kpair]

end EndExtension
end ZFVP.Infinitary.Internal
