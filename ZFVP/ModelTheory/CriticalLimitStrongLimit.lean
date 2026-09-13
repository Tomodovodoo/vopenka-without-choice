import ZFVP.ModelTheory.CriticalLimitCardinal
import ZFVP.ModelTheory.CriticalSequenceZF
import ZFVP.SetTheory.ChoicelessInaccessibleRank
import ZFVP.SetTheory.WellOrderingChoice
import ZFVP.SetTheory.InverseFunction

/-! Under choice every rank stage below a choiceless inaccessible injects into it, so the
critical limit of a coded rank self-embedding is a strong limit. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The rank-map inaccessibility of `κ` is the same condition as the rank criterion at `κ`. -/
theorem isChoicelessInaccessible_iff_rankCriterionHeight {κ : V} :
    IsChoicelessInaccessible κ ↔ IsRankCriterionHeight κ := by
  constructor
  · exact fun h ↦ h.rankCriterion
  · rintro ⟨ho, hω, _, hn⟩
    let := ho
    exact ⟨ho, hω, fun α hα g ↦ hn (hierarchy α) (hierarchy_mem hα) g⟩

theorem IsChoicelessInaccessible.hierarchy_cardLE (hAC : InternalChoice V) {κ α : V}
    (hκ : IsChoicelessInaccessible κ) (hα : α ∈ κ) : hierarchy α ≤# κ := by
  classical
  let := hκ.1
  let := IsOrdinal.of_mem hα
  have hwo : IsWellOrderable (hierarchy α) := wellOrderable_of_internalChoice hAC (hierarchy α)
  have hini : IsInitialOrdinal (wellOrderedCardinal (hierarchy α)) := wellOrderedCardinal_initial hwo
  let := hini.1
  have heq : wellOrderedCardinal (hierarchy α) ≋ hierarchy α := wellOrderedCardinal_cardEQ hwo
  rcases IsOrdinal.mem_trichotomy (wellOrderedCardinal (hierarchy α)) κ with hlt | he | hgt
  · exact heq.2.trans (cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ hlt))
  · exact heq.2.trans (cardLE_of_subset (he ▸ subset_refl _))
  · exfalso
    obtain ⟨g, hg, hginj⟩ :=
      (cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ hgt)).trans heq.1
    let := IsFunction.of_mem hg
    have hz : (∅ : V) ∈ κ := IsOrdinal.toIsTransitive.mem_trans (by simp) hκ.2.1
    have hdom : domain g = κ := domain_eq_of_mem_function hg
    have hval : ∀ ξ ∈ κ, g ‘ ξ ∈ range g := by
      intro ξ hξ
      exact mem_range_of_kpair_mem (kpair_value_mem (by rw [hdom]; exact hξ))
    have hcof : IsCofinalMap κ (range g) (converseGraph g) := by
      refine ⟨converseGraph_mem_function hg hginj, ?_⟩
      intro ξ hξ
      exact ⟨g ‘ ξ, hval ξ hξ, by rw [converseGraph_value_value hg hginj hξ]⟩
    obtain ⟨f, hf⟩ :=
      hcof.extend_domain (range_subset_of_mem_function hg) (hval ∅ hz)
    exact hκ.no_rank_cofinalMap (hierarchy_mem hα) hf

theorem IsChoicelessInaccessible.power_cardLE (hAC : InternalChoice V) {κ α : V}
    (hκ : IsChoicelessInaccessible κ) (hα : α ∈ κ) : ℘ α ≤# κ := by
  let := hκ.1
  let := IsOrdinal.of_mem hα
  have hsucc : succ α ∈ κ := hκ.rankCriterion.2.2.1 α hα
  have hsub : ℘ α ⊆ hierarchy (succ α) := by
    intro x hx
    rw [hierarchy_succ, mem_power_iff]
    intro y hy
    exact ordinal_subset_hierarchy α y (mem_power_iff.mp hx y hy)
  exact (cardLE_of_subset hsub).trans (hκ.hierarchy_cardLE hAC hsucc)

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem iterate_inaccessible {n : V} (hn : n ∈ (ω : V)) :
    IsChoicelessInaccessible (criticalIterate f κ n) :=
  isChoicelessInaccessible_iff_rankCriterionHeight.mpr (iterate_rankCriterion hδ h hκ hn)

theorem limit_power_cardLE (hAC : InternalChoice V) {α : V} (hα : α ∈ criticalLimit f κ) :
    ℘ α ≤# criticalLimit f κ := by
  obtain ⟨n, hn, hαn⟩ := (mem_criticalLimit_iff f κ α).mp hα
  let := limit_ordinal hδ h hκ
  have hsub : criticalIterate f κ n ⊆ criticalLimit f κ :=
    IsOrdinal.toIsTransitive.transitive _ (iterate_mem_limit hδ h hκ hn)
  exact ((iterate_inaccessible hδ h hκ hn).power_cardLE hAC hαn).trans (cardLE_of_subset hsub)

end CriticalSequence

end ZFVP
