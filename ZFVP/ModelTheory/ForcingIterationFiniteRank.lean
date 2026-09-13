import ZFVP.SetTheory.ForcingIterationCode
import ZFVP.SetTheory.CodingUniverse

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsIterationTable.mem_hierarchy_of_range {κ A B f : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hf : IsIterationTable A f)
    (hA : A ∈ hierarchy κ) (hB : B ∈ hierarchy κ)
    (hv : ∀ x ∈ A, f ‘ x ∈ B) : f ∈ hierarchy κ := by
  have : IsFunction f := hf.function
  apply subset_mem_hierarchy_limit hκ (prod_mem_hierarchy_limit hκ hA hB)
  intro z hz
  obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
  have hx : x ∈ A := hf.domain_eq ▸ mem_domain_of_kpair_mem hz
  exact kpair_mem_iff.mpr ⟨hx, (value_eq_of_kpair_mem hz) ▸ hv x hx⟩

/-- Structural bounds on all graph entries, including the unconstrained triangle
and values of lifts on pairs that do not satisfy the stronger-prefix premise. -/
theorem IsForcingIterationCode.finiteRank {η c γ : V} [IsOrdinal γ]
    (hc : IsForcingIterationCode η c)
    (hη : η ∈ hierarchy (ordinalAdd γ (ω : V)))
    (hP : ∀ i ∈ η, (forcingCodeP c) ‘ i ⊆ hierarchy γ)
    (hπ : ∀ i ∈ η, ∀ j ∈ η, (forcingCodeπ c) ‘ ⟨i, j⟩ₖ ⊆
      ((forcingCodeP c) ‘ j ×ˢ (forcingCodeP c) ‘ i))
    (hE : ∀ i ∈ η, ∀ j ∈ η, (forcingCodeE c) ‘ ⟨i, j⟩ₖ ⊆
      ((forcingCodeP c) ‘ i ×ˢ (forcingCodeP c) ‘ j))
    (hL : ∀ i ∈ η, ∀ j ∈ η, (forcingCodeL c) ‘ ⟨i, j⟩ₖ ⊆
      (((forcingCodeP c) ‘ j ×ˢ (forcingCodeP c) ‘ i) ×ˢ
        ((forcingCodeP c) ‘ j ∪ {∅}))) :
    forcingIterationCode (forcingCodeP c) (forcingCodeR c) (forcingCodeπ c)
      (forcingCodeE c) (forcingCodeL c) (forcingCodet c) ∈
        hierarchy (ordinalAdd γ (ω : V)) := by
  classical
  let κ := ordinalAdd γ (ω : V)
  have hκ : ∀ β ∈ κ, succ β ∈ κ := fun _ h ↦ ordinalAdd_omega_succ_closed γ h
  have hV : hierarchy γ ∈ hierarchy κ := by
    rw [mem_hierarchy_iff_rank_mem, rank_hierarchy]
    exact ordinalAdd_omega_gt γ
  have hU : ℘ (hierarchy γ) ∈ hierarchy κ := power_mem_hierarchy_limit hκ hV
  have hrows : ∀ i ∈ η, (forcingCodeP c) ‘ i ⊆ ℘ (hierarchy γ) := by
    intro i hi a ha
    apply mem_power_iff.mpr
    exact (hierarchy_transitive γ).transitive a (hP i hi a ha)
  have hprod : ℘ (hierarchy γ) ×ˢ ℘ (hierarchy γ) ∈ hierarchy κ :=
    prod_mem_hierarchy_limit hκ hU hU
  have hmat := prod_mem_hierarchy_limit hκ hη hη
  have hp := hc.tableP.mem_hierarchy_of_range hκ hη hU
    (fun i hi ↦ mem_power_iff.mpr (hP i hi))
  have hbin {i j f : V} (hi : i ∈ η) (hj : j ∈ η)
      (hf : f ⊆ (forcingCodeP c) ‘ i ×ˢ (forcingCodeP c) ‘ j) :
      f ∈ ℘ (℘ (hierarchy γ) ×ˢ ℘ (hierarchy γ)) := by
    apply mem_power_iff.mpr
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp (hf z hz)
    exact kpair_mem_iff.mpr ⟨hrows i hi a ha, hrows j hj b hb⟩
  have hr := hc.tableR.mem_hierarchy_of_range hκ hη
    (power_mem_hierarchy_limit hκ hprod)
    (fun i hi ↦ hbin hi hi (hc.system.order.preorder i hi).1)
  have hpr := hc.tableπ.mem_hierarchy_of_range hκ hmat
    (power_mem_hierarchy_limit hκ hprod) (by
      intro z hz
      obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hz
      exact hbin hj hi (hπ i hi j hj))
  have he := hc.tableE.mem_hierarchy_of_range hκ hmat
    (power_mem_hierarchy_limit hκ hprod) (by
      intro z hz
      obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hz
      exact hbin hi hj (hE i hi j hj))
  have hl := hc.tableL.mem_hierarchy_of_range hκ hmat
    (power_mem_hierarchy_limit hκ (prod_mem_hierarchy_limit hκ hprod hU)) (by
      intro z hz
      obtain ⟨i, hi, j, hj, rfl⟩ := mem_prod_iff.mp hz
      apply mem_power_iff.mpr
      intro w hw
      obtain ⟨ab, hab, v, hv, rfl⟩ := mem_prod_iff.mp (hL i hi j hj w hw)
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hab
      refine kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨hrows j hj a ha, hrows i hi b hb⟩, ?_⟩
      rcases mem_union_iff.mp hv with hv | hv
      · exact hrows j hj v hv
      · have hv0 : v = ∅ := by simpa using hv
        rw [hv0]; exact mem_power_iff.mpr (empty_subset _))
  have ht := hc.tablet.mem_hierarchy_of_range hκ hη hV
    (fun i hi ↦ hP i hi _ (hc.system.tops.top i hi).1)
  exact kpair_mem_hierarchy_limit hκ hp (kpair_mem_hierarchy_limit hκ hr
    (kpair_mem_hierarchy_limit hκ hpr (kpair_mem_hierarchy_limit hκ he
      (kpair_mem_hierarchy_limit hκ hl ht))))

theorem IsIterationTable.cutoff_finiteRank {η K γ : V} [IsOrdinal γ]
    (hK : IsIterationTable η K) (hη : η ∈ hierarchy (ordinalAdd γ (ω : V)))
    (hbound : ∀ i ∈ η, K ‘ i ⊆ γ) :
    K ∈ hierarchy (ordinalAdd γ (ω : V)) := by
  have hκ : ∀ β ∈ ordinalAdd γ (ω : V), succ β ∈ ordinalAdd γ (ω : V) :=
    fun _ h ↦ ordinalAdd_omega_succ_closed γ h
  have hγ : γ ∈ hierarchy (ordinalAdd γ (ω : V)) := by
    rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]
    exact ordinalAdd_omega_gt γ
  exact hK.mem_hierarchy_of_range hκ hη (power_mem_hierarchy_limit hκ hγ)
    (fun i hi ↦ mem_power_iff.mpr (hbound i hi))

theorem IsForcingIterationCode.finiteRank_pair {η c γ K : V} [IsOrdinal γ]
    (hc : IsForcingIterationCode η c)
    (hη : η ∈ hierarchy (ordinalAdd γ (ω : V)))
    (hP : ∀ i ∈ η, (forcingCodeP c) ‘ i ⊆ hierarchy γ)
    (hπ : ∀ i ∈ η, ∀ j ∈ η, (forcingCodeπ c) ‘ ⟨i, j⟩ₖ ⊆
      ((forcingCodeP c) ‘ j ×ˢ (forcingCodeP c) ‘ i))
    (hE : ∀ i ∈ η, ∀ j ∈ η, (forcingCodeE c) ‘ ⟨i, j⟩ₖ ⊆
      ((forcingCodeP c) ‘ i ×ˢ (forcingCodeP c) ‘ j))
    (hL : ∀ i ∈ η, ∀ j ∈ η, (forcingCodeL c) ‘ ⟨i, j⟩ₖ ⊆
      (((forcingCodeP c) ‘ j ×ˢ (forcingCodeP c) ‘ i) ×ˢ
        ((forcingCodeP c) ‘ j ∪ {∅})))
    (hK : IsIterationTable η K) (hbound : ∀ i ∈ η, K ‘ i ⊆ γ) :
    ⟨forcingIterationCode (forcingCodeP c) (forcingCodeR c) (forcingCodeπ c)
      (forcingCodeE c) (forcingCodeL c) (forcingCodet c), K⟩ₖ ∈
        hierarchy (ordinalAdd γ (ω : V)) := by
  exact kpair_mem_hierarchy_limit (fun _ h ↦ ordinalAdd_omega_succ_closed γ h)
    (hc.finiteRank hη hP hπ hE hL) (hK.cutoff_finiteRank hη hbound)

end ZFVP
