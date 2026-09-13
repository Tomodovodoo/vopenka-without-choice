import ZFVP.ModelTheory.SchmerlInternalBooleanAxioms

/-! Internally coded Boolean derivations. Each node contains its label, rule
tag, and premise codes. Conjunction premises form an internal omega-function.
Premise ranks decrease inside the model, so soundness uses internal rank
induction even when membership is externally ill founded.

This is the propositional/countable-conjunction subcalculus. It does not yet
include Keisler's Q schemas, first-order schemas, or completeness. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def booleanProofNode (n φ tag data : V) : V := ⟨⟨n, φ⟩ₖ, ⟨tag, data⟩ₖ⟩ₖ

instance booleanProofNode_definable : ℒₛₑₜ-function₄[V] booleanProofNode := by
  unfold booleanProofNode
  definability

@[simp] theorem booleanProofNode_label (n φ tag data : V) :
    kpair.π₁ (booleanProofNode n φ tag data) = ⟨n, φ⟩ₖ := by simp [booleanProofNode]

def IsBooleanProofNode (Γ F D d : V) : Prop := ∃ n φ, ⟨n, φ⟩ₖ ∈ F ∧
  ((d = booleanProofNode n φ 0 ∅ ∧ ⟨n, φ⟩ₖ ∈ Γ) ∨
   (d = booleanProofNode n φ 1 ∅ ∧ IsBooleanAxiom φ) ∨
   (∃ p ∈ D, ∃ q ∈ D, ∃ ψ, d = booleanProofNode n φ 2 ⟨p, q⟩ₖ ∧
      kpair.π₁ p = ⟨n, impCode ψ φ⟩ₖ ∧ kpair.π₁ q = ⟨n, ψ⟩ₖ) ∨
   ∃ f g, IsFunction f ∧ domain f = (ω : V) ∧ IsFunction g ∧ domain g = (ω : V) ∧
      d = booleanProofNode n φ 3 g ∧ φ = conjCode f ∧
      ∀ i ∈ (ω : V), g ‘ i ∈ D ∧ kpair.π₁ (g ‘ i) = ⟨n, f ‘ i⟩ₖ)

instance isBooleanProofNode_definable : ℒₛₑₜ-relation₄[V] IsBooleanProofNode := by
  unfold IsBooleanProofNode
  definability

def IsBooleanProof (L Γ F D : V) : Prop :=
  IsFragment L F ∧ Γ ⊆ F ∧ ∀ d ∈ D, IsBooleanProofNode Γ F D d

instance isBooleanProof_definable : ℒₛₑₜ-relation₄[V] IsBooleanProof := by
  unfold IsBooleanProof
  definability

theorem IsBooleanProofNode.label_mem {Γ F D d : V} (hd : IsBooleanProofNode Γ F D d) :
    kpair.π₁ d ∈ F := by
  obtain ⟨n, φ, hφ, hd⟩ := hd
  rcases hd with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨p, _, q, _, ψ, rfl, _, _⟩ |
    ⟨f, g, _, _, _, _, rfl, _, _⟩ <;> simpa only [booleanProofNode_label] using hφ

theorem booleanProofNode_premise_rank {p n φ tag data : V} (h : rank p ∈ rank data) :
    rank p ∈ rank (booleanProofNode n φ tag data) := by
  exact IsOrdinal.toIsTransitive.mem_trans h
    (IsOrdinal.toIsTransitive.mem_trans (rank_kpair_right_lt tag data)
      (rank_kpair_right_lt ⟨n, φ⟩ₖ ⟨tag, data⟩ₖ))

set_option maxHeartbeats 800000 in
theorem IsBooleanProofNode.sound {L Γ F D M d : V} (h : IsBooleanProofNode Γ F D d)
    (hF : IsFragment L F) (hlabels : ∀ p ∈ D, kpair.π₁ p ∈ F)
    (hΓ : ∀ n φ, ⟨n, φ⟩ₖ ∈ Γ → ∀ b ∈ structureDomain M ^ n, Holds L F M n φ b)
    (ih : ∀ p ∈ D, rank p ∈ rank d →
      ∀ b ∈ structureDomain M ^ kpair.π₁ (kpair.π₁ p),
        Holds L F M (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ (kpair.π₁ p)) b) :
    ∀ b ∈ structureDomain M ^ kpair.π₁ (kpair.π₁ d),
      Holds L F M (kpair.π₁ (kpair.π₁ d)) (kpair.π₂ (kpair.π₁ d)) b := by
  obtain ⟨n, φ, hφ, hn⟩ := h
  rcases hn with ⟨rfl, hφΓ⟩ | ⟨rfl, hax⟩ | ⟨p, hp, q, hq, ψ, rfl, hlp, hlq⟩ |
    ⟨f, g, hf, hfd, hg, hgd, rfl, rfl, hchildren⟩
  · simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using hΓ n φ hφΓ
  · simpa only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair] using
      (fun b hb ↦ hax.sound hF hφ hb)
  · have hip := ih p hp (booleanProofNode_premise_rank (rank_kpair_left_lt p q))
    have hiq := ih q hq (booleanProofNode_premise_rank (rank_kpair_right_lt p q))
    have hpF := hlabels p hp
    rw [hlp] at hpF
    simp only [hlp, hlq, kpair.π₁_kpair, kpair.π₂_kpair] at hip hiq
    simp only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair]
    intro b hb
    exact (holds_imp hF hpF hb).mp (hip b hb) (hiq b hb)
  · let := hg
    simp only [booleanProofNode_label, kpair.π₁_kpair, kpair.π₂_kpair]
    intro b hb
    apply (holds_conj hF hφ hb).mpr
    intro i hi
    have hic := hchildren i hi
    have hr : rank (g ‘ i) ∈ rank g := rank_lt_of_mem_range
      (mem_range_of_kpair_mem (kpair_value_mem (hgd.symm ▸ hi)))
    have hii := ih (g ‘ i) hic.1 (booleanProofNode_premise_rank hr)
    simp only [hic.2, kpair.π₁_kpair, kpair.π₂_kpair] at hii
    exact hii b hb

theorem IsBooleanProof.sound {L Γ F D M : V} (h : IsBooleanProof L Γ F D)
    (hΓ : ∀ n φ, ⟨n, φ⟩ₖ ∈ Γ → ∀ b ∈ structureDomain M ^ n, Holds L F M n φ b) :
    ∀ d ∈ D, ∀ b ∈ structureDomain M ^ kpair.π₁ (kpair.π₁ d),
      Holds L F M (kpair.π₁ (kpair.π₁ d)) (kpair.π₂ (kpair.π₁ d)) b := by
  apply projectedRank_induction D id (by definability)
    (fun d ↦ ∀ b ∈ structureDomain M ^ kpair.π₁ (kpair.π₁ d),
      Holds L F M (kpair.π₁ (kpair.π₁ d)) (kpair.π₂ (kpair.π₁ d)) b)
    (by unfold Holds; definability)
  intro d hd ih
  exact (h.2.2 d hd).sound h.1 (fun p hp ↦ (h.2.2 p hp).label_mem) hΓ ih

/-- The proof code stores its entire fragment, node set, and root. Both sets
are internally countable; proof validity itself is wholly syntactic. -/
def IsBooleanDerivationCode (L Γ n φ c : V) : Prop := ∃ F D d,
  c = ⟨F, ⟨D, d⟩ₖ⟩ₖ ∧ IsInternallyCountable F ∧ IsInternallyCountable D ∧
  IsBooleanProof L Γ F D ∧ d ∈ D ∧ kpair.π₁ d = ⟨n, φ⟩ₖ

instance isBooleanDerivationCode_definable :
    Language.DefinableRel₅ ℒₛₑₜ (IsBooleanDerivationCode : V → V → V → V → V → Prop) := by
  unfold IsBooleanDerivationCode
  definability

theorem IsBooleanDerivationCode.sound {L Γ n φ c M : V} (h : IsBooleanDerivationCode L Γ n φ c)
    (hΓ : ∀ k ψ, ⟨k, ψ⟩ₖ ∈ Γ → ∀ b ∈ structureDomain M ^ k,
      Holds L (kpair.π₁ c) M k ψ b) :
    ∀ b ∈ structureDomain M ^ n, Holds L (kpair.π₁ c) M n φ b := by
  obtain ⟨F, D, d, rfl, _, _, hproof, hd, hlabel⟩ := h
  simp only [kpair.π₁_kpair] at hΓ ⊢
  simpa only [hlabel, kpair.π₁_kpair, kpair.π₂_kpair] using hproof.sound hΓ d hd

end ZFVP.Infinitary.Internal
