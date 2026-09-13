import ZFVP.SetTheory.GoodClosureTransfer
import ZFVP.SetTheory.GoodLimitPointClass
import ZFVP.ModelTheory.CriticalSequence
import ZFVP.ModelTheory.KunenUnconditional

/-! The critical point of a Vopenka embedding is a good closure point.

This is the step in the converse of Bagaria's Theorem 4.12 that calls on Kunen's theorem.
Suppose `f` embeds the rank stage `hierarchy lam` into `hierarchy lam'`, that `lam` is a limit
point of the good closure point class, and that `κ` is the critical point of `f`. If `κ` were not
a good closure point, the good closure points below `κ` would stop at some `γ ∈ κ`. The least
good closure point `d1` above `γ` then lies above `κ`, and the least one `d2` above `d1` lies
above that. Both are least ordinals for a condition transferred by `f`, so `f` fixes them, and
the critical sequence of `κ` stays below `d1`, hence below `d2`. Kunen's theorem applied at the
fixed stage `d2` gives a contradiction. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The critical sequence below a fixed ordinal

`CriticalSequence.iterate_below_fixed` says the same for an embedding of a rank stage into
itself. The embedding here has a different target, so the induction is redone. -/

/-- If `f` fixes `β`, the whole critical sequence of `κ ∈ β` stays inside `β`. -/
theorem criticalIterate_mem_of_fixed {A B f κ β : V} [IsTransitive A]
    (h : IsCodedMembershipEmbedding A B f) (hβA : β ∈ A) (hβsub : β ⊆ A)
    (hfix : f ‘ β = β) (hκβ : κ ∈ β) {n : V} (hn : n ∈ (ω : V)) :
    criticalIterate f κ n ∈ β := by
  have hi : ∀ m ∈ (ω : V), criticalIterate f κ m ∈ β := by
    apply naturalNumber_induction (fun m ↦ criticalIterate f κ m ∈ β) (by definability)
    · simpa using hκβ
    · intro m hm ih
      rw [criticalIterate_succ f κ hm, ← hfix]
      exact (h.value_mem_iff (hβsub _ ih) hβA).mpr ih
  exact hi n hn

/-- The critical limit is an ordinal as soon as every member of the critical sequence is. -/
theorem criticalLimit_isOrdinal_of_iterates {f κ : V}
    (hi : ∀ n ∈ (ω : V), IsOrdinal (criticalIterate f κ n)) :
    IsOrdinal (criticalLimit f κ) := by
  apply IsOrdinal.sUnion
  intro y hy
  obtain ⟨n, hny⟩ := mem_range_iff.mp hy
  have hn : n ∈ (ω : V) := by simpa using mem_domain_of_kpair_mem hny
  have he : y = criticalIterate f κ n :=
    (value_eq_of_kpair_mem hny).symm.trans (criticalSequence_value f κ hn)
  exact he.symm ▸ hi n hn

/-! ### The critical point is a good closure point -/

/-- The critical point of an embedding of a limit point `lam` of the good closure point class is
itself a good closure point. -/
theorem criticalPoint_isGoodClosurePoint (hAC : InternalChoice V) {k : ℕ} {α lam lam' f κ : V}
    [IsOrdinal α]
    (hno : ∀ κ₀ : V, α ∈ κ₀ → ¬ IsCnExtendible (k + 1) κ₀)
    (hlam : IsGoodLimitPoint k α lam) (hlam' : Cn (k + 2) lam')
    (h : IsCodedMembershipEmbedding (hierarchy lam) (hierarchy lam') f)
    (hκ : IsCriticalPoint (hierarchy lam) f κ)
    (hαlam : α ∈ lam) (hfα : f ‘ α = α) (hακ : α ∈ κ) (hκlam : κ ∈ lam) :
    IsGoodClosurePoint k α κ := by
  by_contra hbad
  have hlamord : IsOrdinal lam := hlam.good.1
  have hκord : IsOrdinal κ := hκ.ordinal
  have hlamtrans : IsTransitive (hierarchy lam) := hierarchy_transitive lam
  -- the good closure points below `κ` are bounded by some `γ ∈ κ`
  have hex : ∃ γ : V, γ ∈ κ ∧ ∀ ν ∈ κ, ¬(γ ∈ ν ∧ IsGoodClosurePoint k α ν) := by
    by_contra hc
    refine hbad (goodClosurePoint_of_unbounded ⟨α, hακ⟩ ?_)
    intro ξ hξ
    by_contra hc2
    exact hc ⟨ξ, hξ, fun ν hν hcon ↦ hc2 ⟨ν, hν, hcon.1, hcon.2⟩⟩
  obtain ⟨γ, hγκ, hγ⟩ := hex
  have hγord : IsOrdinal γ := IsOrdinal.of_mem hγκ
  -- the two least good closure points above `γ`
  obtain ⟨d1, hd1spec⟩ : ∃ d : V, IsLeastOrdinal (fun x ↦ γ ∈ x ∧ IsGoodClosurePoint k α x) d :=
    ⟨_, leastGoodClosurePoint_spec hno γ⟩
  have hd1ord : IsOrdinal d1 := hd1spec.1
  have hγd1 : γ ∈ d1 := hd1spec.2.1.1
  have hd1good : IsGoodClosurePoint k α d1 := hd1spec.2.1.2
  obtain ⟨d2, hd2spec⟩ : ∃ d : V, IsLeastOrdinal (fun x ↦ d1 ∈ x ∧ IsGoodClosurePoint k α x) d :=
    ⟨_, leastGoodClosurePoint_spec hno d1⟩
  have hd2ord : IsOrdinal d2 := hd2spec.1
  have hd1d2 : d1 ∈ d2 := hd2spec.2.1.1
  have hd2good : IsGoodClosurePoint k α d2 := hd2spec.2.1.2
  -- `d1` lies above `κ`
  have hκd1 : κ ∈ d1 := by
    rcases IsOrdinal.mem_trichotomy d1 κ with hlt | heq | hgt
    · exact absurd ⟨hγd1, hd1good⟩ (hγ d1 hlt)
    · exact absurd (heq ▸ hd1good) hbad
    · exact hgt
  have hκd2 : κ ∈ d2 := IsOrdinal.toIsTransitive.mem_trans hκd1 hd1d2
  -- both stay below `lam`, because `lam` has good closure points cofinally below it
  have hd1lam : d1 ∈ lam := by
    obtain ⟨ν, hνlam, hκν, hνgood⟩ := hlam.exists_good_above hκlam
    have hνord : IsOrdinal ν := hνgood.1
    have hsub : d1 ⊆ ν :=
      hd1spec.2.2 ν hνord ⟨IsOrdinal.toIsTransitive.mem_trans hγκ hκν, hνgood⟩
    rcases IsOrdinal.subset_iff.mp hsub with he | hlt
    · exact he ▸ hνlam
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hνlam
  have hd2lam : d2 ∈ lam := by
    obtain ⟨ν, hνlam, hd1ν, hνgood⟩ := hlam.exists_good_above hd1lam
    have hνord : IsOrdinal ν := hνgood.1
    have hsub : d2 ⊆ ν := hd2spec.2.2 ν hνord ⟨hd1ν, hνgood⟩
    rcases IsOrdinal.subset_iff.mp hsub with he | hlt
    · exact he ▸ hνlam
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hνlam
  -- everything in sight lives in the source stage
  have hαH : α ∈ hierarchy lam := ordinal_subset_hierarchy lam _ hαlam
  have hγH : γ ∈ hierarchy lam :=
    ordinal_subset_hierarchy lam _ (IsOrdinal.toIsTransitive.mem_trans hγκ hκlam)
  have hd1H : d1 ∈ hierarchy lam := ordinal_subset_hierarchy lam _ hd1lam
  have hd2H : d2 ∈ hierarchy lam := ordinal_subset_hierarchy lam _ hd2lam
  -- `f` fixes `γ`, hence `d1` and `d2`
  have hfγ : f ‘ γ = γ := hκ.fixed_below hγκ
  have hfd1 : f ‘ d1 = d1 :=
    leastGoodClosurePoint_transfer_fixed hlam.cn hlam' h hαH hfα hγH hfγ hd1H hd1spec
  have hfd2 : f ‘ d2 = d2 :=
    leastGoodClosurePoint_transfer_fixed hlam.cn hlam' h hαH hfα hd1H hfd1 hd2H hd2spec
  -- the critical sequence stays below `d1`, so the critical limit is below `d2`
  have hd1sub : d1 ⊆ hierarchy lam := fun x hx ↦
    ordinal_subset_hierarchy lam _ (IsOrdinal.toIsTransitive.mem_trans hx hd1lam)
  have hiter : ∀ n ∈ (ω : V), criticalIterate f κ n ∈ d1 :=
    fun n hn ↦ criticalIterate_mem_of_fixed h hd1H hd1sub hfd1 hκd1 hn
  have hlimord : IsOrdinal (criticalLimit f κ) :=
    criticalLimit_isOrdinal_of_iterates (fun n hn ↦ IsOrdinal.of_mem (hiter n hn))
  have hlimsub : criticalLimit f κ ⊆ d1 := by
    intro x hx
    obtain ⟨n, hn, hxn⟩ := (mem_criticalLimit_iff f κ x).mp hx
    exact IsOrdinal.toIsTransitive.mem_trans hxn (hiter n hn)
  have hlimd2 : criticalLimit f κ ∈ d2 := by
    rcases IsOrdinal.subset_iff.mp hlimsub with he | hlt
    · exact he ▸ hd1d2
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hd1d2
  exact false_of_fixed_stage_embedding_choice (k := k + 1) (l := k + 1) hAC hlam.cn hlam'
    (Cn.of_le hd2good.cn (by omega)) h hκ hd2ord hd2H hfd2 hκd2 hlimd2

end ZFVP
