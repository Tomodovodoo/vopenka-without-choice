import ZFVP.ModelTheory.WoodinStageSections

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ θ j d : V} [IsOrdinal θ]
  (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
    (kpair.π₂ (woodinIterationRec k)))
  (hj : j ∈ θ) (h0 : j ≠ ∅) (hlim : j ≠ succ (⋃ˢ j))
  (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
  (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
include hs hj h0 hlim hinac hd

theorem woodinThread_direct_coordinate :
    d ‘ j ∈ forcingDirectLimit j (forcingCodeP (woodinIterationPrefix j))
      (forcingCodeπ (woodinIterationPrefix j)) (forcingCodeE (woodinIterationPrefix j))
      (forcingCodeUniverse (woodinIterationPrefix j)) ∧
    ∀ k ∈ j, d ‘ k = (d ‘ j) ‘ k := by
  let := IsOrdinal.of_mem hj
  have hd' := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hd
  have hdj := hd'.2.1 j hj
  have hrec := woodinIterationRec_direct h0 hlim hinac
  rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair] at hdj
  simp only [forcingDirectCode, forcingThreadCode_poset] at hdj
  refine ⟨hdj, ?_⟩
  intro k hk
  rw [← hd'.2.2 j hj k hk (IsOrdinal.toIsTransitive.mem_trans hk hj),
    woodinIterationPrefix_projection_value hs hj (mem_succ_iff.mpr (Or.inr hk)) (mem_succ_self j),
    hrec, kpair.π₁_kpair]
  simp only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeπ_code,
    forcingMatrixNext_column hk, forcingLimitProjectionColumn_value hk, forcingThreadCoordinate_value hdj]

theorem woodinThread_successor_tail_empty_of_support {b k : V}
    (hb : IsThreadSupport j (forcingCodeE (woodinIterationPrefix j)) (d ‘ j) b)
    (hk : succ k ∈ j) (hbk : b ⊆ k) : kpair.π₂ (d ‘ (succ k)) = ∅ := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hk
  let := IsOrdinal.of_mem (mem_succ_self k)
  let := IsOrdinal.of_mem hb.1
  have hh := woodinThread_direct_coordinate hs hj h0 hlim hinac hd
  have hqb := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp
    (forcingDirectLimit_subset _ _ _ _ _ _ hh.1)).2.1 b hb.1
  have hsj := fun l hl ↦ hs l (IsOrdinal.toIsTransitive.mem_trans hl hj)
  have hbs : b ∈ succ k := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hbk)
  rw [hh.2 (succ k) hk, hb.2 (succ k) hk (IsOrdinal.toIsTransitive.transitive _ hbs),
    woodinIterationPrefix_section_successor hsj hk hbs hqb, kpair.π₂_kpair]

theorem woodinThread_inverse_tail_empty_of_support {b k : V}
    (hb : IsThreadSupport j (forcingCodeE (woodinIterationPrefix j)) (d ‘ j) b)
    (hk : k ∈ j) (hbk : b ∈ k) (hklim : k ≠ succ (⋃ˢ k))
    (hkinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix k))) :
    kpair.π₂ (d ‘ k) = ∅ := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hk
  have hh := woodinThread_direct_coordinate hs hj h0 hlim hinac hd
  have hqb := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp
    (forcingDirectLimit_subset _ _ _ _ _ _ hh.1)).2.1 b hb.1
  have hsj := fun l hl ↦ hs l (IsOrdinal.toIsTransitive.mem_trans hl hj)
  rw [hh.2 k hk, hb.2 k hk (IsOrdinal.toIsTransitive.transitive _ hbk),
    woodinIterationPrefix_section_inverse hsj hk hbk hklim hkinac hqb, kpair.π₂_kpair]

end ZFVP
