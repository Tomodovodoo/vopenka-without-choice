import ZFVP.ModelTheory.SchmerlInternalClassicalDerivation
import ZFVP.ModelTheory.SchmerlInternalConsistency

/-! Syntactic sentence consistency and the one-sentence decision step.
The proof operates on actual internal derivation codes, including countable rules. -/
namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- No sentence and its negation both have internal derivation codes. -/
def IsInternallyConsistentTheory (L Γ : V) : Prop :=
  ∀ φ c e, IsInternalDerivationCode L Γ 0 φ c →
    ¬IsInternalDerivationCode L Γ 0 (negCode φ) e

instance isInternallyConsistentTheory_definable : ℒₛₑₜ-relation[V] IsInternallyConsistentTheory := by
  unfold IsInternallyConsistentTheory
  definability

theorem not_internallyConsistentTheory_iff {L Γ : V} :
    ¬IsInternallyConsistentTheory L Γ ↔
      ∃ φ c e, IsInternalDerivationCode L Γ 0 φ c ∧ IsInternalDerivationCode L Γ 0 (negCode φ) e := by
  classical
  simp only [IsInternallyConsistentTheory, not_forall, not_not, exists_prop]

/-- Adjoining a sentence already proved preserves internal consistency. -/
theorem IsInternallyConsistentTheory.insert_of_derivable {L Γ F χ c : V}
    (h : IsInternallyConsistentTheory L Γ) (hF : IsFragment L F)
    (hFc : IsInternallyCountable F) (hΓF : Γ ⊆ F) (hAC : InternalChoice V)
    (hχ : IsInternalDerivationCode L Γ 0 χ c) :
    IsInternallyConsistentTheory L (insert ⟨(0 : V), χ⟩ₖ Γ) := by
  have hcut : ∀ n ψ, ⟨n, ψ⟩ₖ ∈ insert ⟨(0 : V), χ⟩ₖ Γ →
      ∃ e, IsInternalDerivationCode L Γ n ψ e := by
    intro n ψ ht
    rcases mem_insert.mp ht with he | ht
    · obtain ⟨rfl, rfl⟩ := kpair_inj he
      exact ⟨c, hχ⟩
    · exact internalDerivation_hypothesis hF hFc hΓF ht
  intro ψ d e hd he
  obtain ⟨a, ha⟩ := hd.cut hF hFc hΓF hAC hcut
  obtain ⟨b, hb⟩ := he.cut hF hFc hΓF hAC hcut
  exact h ψ a b ha hb

/-- One of a sentence and its negation can be adjoined consistently. -/
theorem IsInternallyConsistentTheory.decide {L Γ F χ : V}
    (h : IsInternallyConsistentTheory L Γ) (hF : IsFragment L F)
    (hFc : IsInternallyCountable F) (hΓF : Γ ⊆ F)
    (hχ : ⟨(0 : V), χ⟩ₖ ∈ F) (hAC : InternalChoice V) :
    IsInternallyConsistentTheory L (insert ⟨(0 : V), χ⟩ₖ Γ) ∨
      IsInternallyConsistentTheory L (insert ⟨(0 : V), negCode χ⟩ₖ Γ) := by
  classical
  by_cases hn : IsInternallyConsistentTheory L (insert ⟨(0 : V), negCode χ⟩ₖ Γ)
  · exact Or.inr hn
  · obtain ⟨ψ, c, e, hp, hq⟩ := not_internallyConsistentTheory_iff.mp hn
    obtain ⟨d, hd⟩ := internalDerivation_reductio hF hFc hΓF hχ hAC hp hq
    exact Or.inl (h.insert_of_derivable hF hFc hΓF hAC hd)

/-- Both decision branches share an explicit valid, countable ambient fragment. -/
theorem IsInternallyConsistentTheory.exists_decision {L Γ F χ : V}
    (h : IsInternallyConsistentTheory L Γ) (hF : IsFragment L F)
    (hFc : IsInternallyCountable F) (hΓF : Γ ⊆ F)
    (hχ : ⟨(0 : V), χ⟩ₖ ∈ F) (hAC : InternalChoice V) :
    ∃ Δ, Γ ⊆ Δ ∧ Δ ⊆ insert ⟨(0 : V), negCode χ⟩ₖ F ∧
      IsFragment L (insert ⟨(0 : V), negCode χ⟩ₖ F) ∧
      IsInternallyCountable (insert ⟨(0 : V), negCode χ⟩ₖ F) ∧
      IsInternallyConsistentTheory L Δ ∧
      (Δ = insert ⟨(0 : V), χ⟩ₖ Γ ∨ Δ = insert ⟨(0 : V), negCode χ⟩ₖ Γ) := by
  have hsub : Γ ⊆ insert ⟨(0 : V), negCode χ⟩ₖ F := fun t ht ↦ mem_insert.mpr (Or.inr (hΓF t ht))
  have extend {ψ : V} (hp : ⟨(0 : V), ψ⟩ₖ ∈ insert ⟨(0 : V), negCode χ⟩ₖ F) :
      insert ⟨(0 : V), ψ⟩ₖ Γ ⊆ insert ⟨(0 : V), negCode χ⟩ₖ F := by
    intro t ht
    rcases mem_insert.mp ht with rfl | ht
    · exact hp
    · exact hsub t ht
  rcases h.decide hF hFc hΓF hχ hAC with hp | hn
  · exact ⟨_, fun t ht ↦ mem_insert.mpr (Or.inr ht), extend (mem_insert.mpr (Or.inr hχ)),
      hF.insert_neg hχ, internallyCountable_insert hFc _, hp, Or.inl rfl⟩
  · exact ⟨_, fun t ht ↦ mem_insert.mpr (Or.inr ht), extend (mem_insert.mpr (Or.inl rfl)),
      hF.insert_neg hχ, internallyCountable_insert hFc _, hn, Or.inr rfl⟩

/-- The existing no-refutation statement entails the contradiction-pair definition. -/
theorem internallyConsistentTheory_singleton_of_not_refutable {L F χ : V}
    (hF : IsFragment L F) (hFc : IsInternallyCountable F) (hχ : ⟨(0 : V), χ⟩ₖ ∈ F)
    (h : ∀ c, ¬IsInternalDerivationCode L {⟨(0 : V), χ⟩ₖ} 0 (negCode χ) c) :
    IsInternallyConsistentTheory L {⟨(0 : V), χ⟩ₖ} := by
  intro ψ c e hp hn
  obtain ⟨z, hz⟩ := hp.explode (ψ := negCode χ) hn (hF.insert_neg hχ)
    (internallyCountable_insert hFc _) (by simp)
  exact h z hz

/-- For a singleton sentence theory this is exactly the existing refutation criterion. -/
theorem internallyConsistentTheory_singleton_iff {L F χ : V}
    (hF : IsFragment L F) (hFc : IsInternallyCountable F) (hχ : ⟨(0 : V), χ⟩ₖ ∈ F) :
    IsInternallyConsistentTheory L {⟨(0 : V), χ⟩ₖ} ↔
      ∀ c, ¬IsInternalDerivationCode L {⟨(0 : V), χ⟩ₖ} 0 (negCode χ) c := by
  constructor
  · intro h c hc
    have hΓ : ({⟨(0 : V), χ⟩ₖ} : V) ⊆ F := by
      intro t ht
      simpa only [mem_singleton_iff.mp ht] using hχ
    obtain ⟨d, hd⟩ := internalDerivation_hypothesis (n := (0 : V)) (φ := χ) hF hFc hΓ (by simp)
    exact h χ d c hd hc
  · exact internallyConsistentTheory_singleton_of_not_refutable hF hFc hχ

theorem CodedSatisfiable.internallyConsistentTheory {L F χ : V}
    (h : CodedSatisfiable L F χ) (hFc : IsInternallyCountable F) (hAC : InternalChoice V) :
    IsInternallyConsistentTheory L {⟨(0 : V), χ⟩ₖ} :=
  internallyConsistentTheory_singleton_of_not_refutable h.fragment hFc h.sentence
    (h.not_internalDerivation_neg hAC)

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem CodedSatisfiable.ground_internallyConsistentTheory {L F χ : V}
    (j : MembershipEndExtension V W) (h : CodedSatisfiable (j L) (j F) (j χ))
    (hF : IsFragment L F) (hFc : IsInternallyCountable F) (hχ : ⟨(0 : V), χ⟩ₖ ∈ F)
    (hAC : InternalChoice W) : IsInternallyConsistentTheory L {⟨(0 : V), χ⟩ₖ} :=
  internallyConsistentTheory_singleton_of_not_refutable hF hFc hχ
    (h.not_ground_internalDerivation_neg j hAC)

end ZFVP.Infinitary.Internal
