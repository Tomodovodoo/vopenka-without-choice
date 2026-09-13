import ZFVP.ModelTheory.NormalizedTwoStepComparison
import ZFVP.ModelTheory.TransitiveZFTwoStepForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingName_mem_rankHierarchy {P τ : V} (hτ : IsForcingName P τ) :
    τ ∈ forcingNameHierarchy P (succ (rank τ)) := by
  apply forcingName_induction P (fun τ ↦ τ ∈ forcingNameHierarchy P (succ (rank τ)))
    (by definability) ?_ τ hτ
  intro ν hν ih
  rw [forcingNameHierarchy_succ, mem_power_iff]
  intro z hz
  obtain ⟨σ, p, hp, rfl, _⟩ := (forcingName_iff P ν).mp hν z hz
  have hlt := rank_subname_lt hz
  have hs : succ (rank σ) ⊆ rank ν := by
    intro β hβ
    rcases mem_succ_iff.mp hβ with rfl | hβ
    · exact hlt
    · exact (inferInstance : IsTransitive (rank ν)).mem_trans hβ hlt
  exact kpair_mem_iff.mpr ⟨forcingNameHierarchy_mono P hs σ (ih σ p hz), hp⟩

theorem forcingName_mem_hierarchy_pool {P τ δ : V} [IsOrdinal δ]
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hτ : IsForcingName P τ) (hτδ : τ ∈ hierarchy δ) :
    τ ∈ forcingNameHierarchy P δ :=
  forcingNameHierarchy_mono P (IsOrdinal.toIsTransitive.transitive _
    (hδ _ ((mem_hierarchy_iff_rank_mem _ _).mp hτδ))) τ (forcingName_mem_rankHierarchy hτ)

theorem forcingSaturatedName_member_imp {P R U Q p τ : V}
    (hR : IsForcingPreorder P R)
    (hm : p ∈ atomicMembership P R τ (forcingSaturatedName P R U Q)) :
    p ∈ atomicMembership P R τ Q := by
  have hp := atomicMembership_subset _ _ _ _ p hm
  apply atomicMembership_dense hR hp
  intro q hq hqp
  obtain ⟨r, hr, hrq, ν, s, hνs, hrs, he⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hm |>.2 q hq hqp
  have hν := ((pair_mem_forcingSaturatedName _ _ _ _ _ _).mp hνs).2.2.2
  exact ⟨r, ((atomicEquality_membership_iff hR he Q).1).mpr (atomicMembership_mono hR hν hr hrs), hrq⟩

/-- The existing saturated-name carrier is exactly the bounded-name carrier,
including its explicit empty-name top. -/
theorem saturatedTwoStep_eq_boundedNameTwoStep {P R δ Q : V}
    (hR : IsForcingPreorder P R) (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) :
    twoStepConditions P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q) ∅ =
      boundedNameTwoStep P R δ (forcingSaturatedName P R (forcingNameHierarchy P δ) Q) := by
  let := hδ.1
  have h0 : (∅ : V) ∈ hierarchy δ := by
    apply (mem_hierarchy_iff_rank_mem _ _).mpr
    rw [rank_empty]
    exact ordinal_mem_of_subset_mem (empty_subset (rank P)) ((mem_hierarchy_iff_rank_mem _ _).mp hP)
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨p, hp, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp hz
    have hn := forcingName_of_twoStepNames (forcingSaturatedName_isName P R (forcingNameHierarchy P δ) Q)
      (empty_forcingName P) hτ
    have hb : τ ∈ hierarchy δ := by
      rcases mem_union_iff.mp hτ with hd | he
      · exact hδ.forcingNameHierarchy_subset hP τ (forcingSaturatedName_domain_subset _ _ _ _ τ hd)
      · exact (mem_singleton_iff.mp he).symm ▸ h0
    exact (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mpr ⟨hp, hb, hn, hm⟩
  · intro hz
    obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    obtain ⟨hp, hb, hn, hm⟩ := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hz
    have hpool := forcingName_mem_hierarchy_pool hδ.rankCriterion.2.2.1 hn hb
    have hd := forcingSaturatedName_mem_domain hpool hp hn (forcingSaturatedName_member_imp hR hm)
    exact (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hp, mem_union_iff.mpr (.inl hd), hm⟩

theorem saturatedTwoStepOrder_eq_nameTwoStepOrderOn {P R δ Q S : V}
    (hR : IsForcingPreorder P R) (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) :
    twoStepOrder P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q) S ∅ =
      nameTwoStepOrderOn P R S
        (boundedNameTwoStep P R δ (forcingSaturatedName P R (forcingNameHierarchy P δ) Q)) := by
  unfold twoStepOrder nameTwoStepOrderOn
  rw [saturatedTwoStep_eq_boundedNameTwoStep hR hδ hP]

end ZFVP
