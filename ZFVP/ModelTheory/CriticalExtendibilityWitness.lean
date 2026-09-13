import ZFVP.ModelTheory.CriticalChainEmbedding
import ZFVP.ModelTheory.CriticalSequenceIndexBounds

/-! Every internal critical stage has all positive-level extendibility witnesses in the limit. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem extendibility_witness (hlim : criticalLimit f κ ∈ hierarchy δ)
    {i : V} (hi : i ∈ (ω : V)) (m : ℕ)
    (μ : SetDomain (hierarchy (criticalLimit f κ)))
    (hμ : IsOrdinal μ.val) (hiμ : criticalIterate f κ i ∈ μ.val)
    (hc : (cnFormula (m + 1)).Evalb ![μ]) :
    ∃ (ν : SetDomain (hierarchy (criticalLimit f κ))) (e : V),
      IsOrdinal ν.val ∧ μ.val ∈ ν.val ∧ (cnFormula (m + 1)).Evalb ![ν] ∧
      e ∈ hierarchy (criticalLimit f κ) ∧
      IsCodedMembershipEmbedding (hierarchy μ.val) (hierarchy ν.val) e ∧
      IsCriticalPoint (hierarchy μ.val) e (criticalIterate f κ i) ∧
      μ.val ∈ e ‘ (criticalIterate f κ i) := by
  obtain ⟨q, hq, hμq⟩ := (mem_criticalLimit_iff f κ μ.val).mp
    (ordinal_mem_limit hδ h hκ μ hμ)
  let s := succ q
  let t := succ (succ q)
  have hs : s ∈ (ω : V) := ω_succ_closed hq
  have ht : t ∈ (ω : V) := ω_succ_closed hs
  have hs0 : s ≠ 0 := by
    intro hz
    have hm : q ∈ s := by simp [s]
    simp only [hz, zero_def, not_mem_empty] at hm
  have ht0 : t ≠ 0 := by
    intro hz
    have hm : succ q ∈ t := by simp [t]
    simp only [hz, zero_def, not_mem_empty] at hm
  let r := ordinalAdd q i
  let a := ordinalAdd s i
  let b := ordinalAdd (ordinalAdd s t) i
  let u := ordinalAdd (ordinalAdd q t) i
  have hr : r ∈ (ω : V) := ordinalAdd_natural hq hi
  have ha : a ∈ (ω : V) := ordinalAdd_natural hs hi
  have hb : b ∈ (ω : V) := ordinalAdd_natural (ordinalAdd_natural hs ht) hi
  have hu : u ∈ (ω : V) := ordinalAdd_natural (ordinalAdd_natural hq ht) hi
  let e := shiftedCriticalEmbedding δ f κ s t i
  have he : IsCodedMembershipEmbedding (hierarchy (criticalIterate f κ a))
      (hierarchy (criticalIterate f κ b)) e := shifted_elementary hδ h hκ hlim hs ht hi
  have heκ := shifted_criticalPoint hδ h hκ hlim hs ht hi hs0 ht0
  have her : e ‘ (criticalIterate f κ r) = criticalIterate f κ u :=
    shifted_value_criticalIterate hδ h hκ hlim hs ht hi hq (iterate_increasing hδ h hκ hq)
  have hra : criticalIterate f κ r ∈ criticalIterate f κ a := iterate_add_increasing hδ h hκ hq hi
  have hμr : μ.val ∈ criticalIterate f κ r := (iterate_subset_add hδ h hκ hq hi) _ hμq
  let := (iterate_spec hδ h hκ ha).1
  let := (iterate_spec hδ h hκ hb).1
  let := hierarchy_transitive (criticalIterate f κ a)
  let := hierarchy_transitive (criticalIterate f κ b)
  let := hμ
  let := hierarchy_transitive μ.val
  have hμa := IsOrdinal.toIsTransitive.mem_trans hμr hra
  let ν : SetDomain (hierarchy (criticalLimit f κ)) :=
    ⟨e ‘ μ.val, stageEmbedding_value_mem_limit hδ h hκ ha hb he hμa⟩
  have hνc := (stageEmbedding_cn hδ h hκ ha hb hr hu he hra her m μ ν hμ hμr rfl).mp hc
  have hiVμ := ordinal_subset_hierarchy μ.val _ hiμ
  obtain ⟨hν, _, hres, hresmem⟩ := stageEmbedding_restrict hδ h hκ ha hb he hμ hμa ⟨_, hiVμ⟩
  let := hν
  have hcrit : IsCriticalPoint (hierarchy μ.val) (e ↾ (hierarchy μ.val)) (criticalIterate f κ i) :=
    heκ.restrict he.function ((hierarchy_transitive (criticalIterate f κ a)).transitive _ (hierarchy_mem hμa)) hiVμ
  have hval : (e ↾ (hierarchy μ.val)) ‘ (criticalIterate f κ i) = criticalIterate f κ (ordinalAdd t i) := by
    let := IsFunction.of_mem he.function
    rw [value_restrict (by rw [domain_eq_of_mem_function he.function]; exact heκ.mem_domain) hiVμ]
    exact shifted_value_criticalPoint hδ h hκ hlim hs ht hi hs0
  have hmove : μ.val ∈ (e ↾ (hierarchy μ.val)) ‘ (criticalIterate f κ i) := by
    rw [hval]
    let := (iterate_spec hδ h hκ (ordinalAdd_natural ht hi)).1
    exact IsOrdinal.toIsTransitive.mem_trans hμa (iterate_add_increasing hδ h hκ hs hi)
  have himage : (e ↾ (hierarchy μ.val)) ‘ (criticalIterate f κ i) ∈ e ‘ μ.val := by
    rw [← shifted_value_criticalPoint hδ h hκ hlim hs ht hi hs0] at hval
    rw [hval]
    exact (he.value_mem_iff heκ.mem_domain (ordinal_subset_hierarchy _ _ hμa)).mpr hiμ
  exact ⟨ν, e ↾ (hierarchy μ.val), hν, IsOrdinal.toIsTransitive.mem_trans hmove himage,
    hνc, hresmem, hres, hcrit, hmove⟩

end CriticalSequence

end ZFVP
