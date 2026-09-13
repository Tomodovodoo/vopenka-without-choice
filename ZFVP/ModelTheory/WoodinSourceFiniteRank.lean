import ZFVP.ModelTheory.WoodinSourceCode
import ZFVP.ModelTheory.ForcingIterationFiniteRank
import ZFVP.SetTheory.FiniteCodingClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem value_mem_stage {β f : V} [IsOrdinal β] [IsFunction f]
    (h0 : (∅ : V) ∈ hierarchy β) (hf : f ∈ hierarchy β) (x : V) :
    f ‘ x ∈ hierarchy β := by
  have : IsTransitive (hierarchy β) := hierarchy_transitive β
  classical
  by_cases hx : x ∈ domain f
  · exact (kpair_components_mem_transitive
      ((hierarchy_transitive β).mem_trans (kpair_value_mem hx) hf)).2
  · rwa [value_eq_empty_of_not_mem_domain hx]

private theorem graph_mem {κ A B : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hA : A ∈ hierarchy κ) (hB : B ∈ hierarchy κ)
    (F : V → V) (dF : ℒₛₑₜ-function₁ F) (hv : ∀ x ∈ A, F x ∈ B) :
    definableGraph A F dF ∈ hierarchy κ := by
  apply subset_mem_hierarchy_limit hκ (prod_mem_hierarchy_limit hκ hA hB)
  intro z hz
  obtain ⟨x, hx, rfl⟩ := (mem_definableGraph_iff _ _ _ _).mp hz
  exact kpair_mem_iff.mpr ⟨hx, hv x hx⟩

private theorem stage_mem {κ β : V} [IsOrdinal κ] [IsOrdinal β] (hβ : β ∈ κ) :
    hierarchy β ∈ hierarchy κ := by
  rwa [mem_hierarchy_iff_rank_mem, rank_hierarchy]

variable {κ θ : V} [IsOrdinal κ]
variable (hκ : ∀ β ∈ κ, succ β ∈ κ)
variable (h0 : (∅ : V) ∈ hierarchy κ) (hθ : woodinSourceIndex θ ∈ hierarchy κ)

include hκ h0 hθ in
theorem woodinInsertSeed_mem_hierarchy {f a : V} [IsFunction f]
    (hf : f ∈ hierarchy κ) (ha : a ∈ hierarchy κ) :
    woodinInsertSeed θ f a ∈ hierarchy κ := by
  obtain ⟨β, hβ, hz, hfa⟩ := common_hierarchy_stage hκ h0 (kpair_mem_hierarchy_limit hκ hf ha)
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  have : IsTransitive (hierarchy β) := hierarchy_transitive β
  obtain ⟨hfb, hab⟩ := kpair_components_mem_transitive hfa
  unfold woodinInsertSeed
  apply graph_mem hκ hθ (stage_mem hβ)
  intro i _
  classical
  by_cases hi : i = ∅
  · simpa [woodinInsertSeedValue, hi] using hab
  · simpa [woodinInsertSeedValue, hi] using value_mem_stage hz hfb (woodinRecursiveIndex i)

include hκ h0 hθ in
theorem woodinSeedMatrix_mem_hierarchy {M C : V} [IsFunction M] [IsFunction C]
    (hM : M ∈ hierarchy κ) (hC : C ∈ hierarchy κ) :
    woodinSeedMatrix θ M C ∈ hierarchy κ := by
  obtain ⟨β, hβ, hz, hMC⟩ := common_hierarchy_stage hκ h0 (kpair_mem_hierarchy_limit hκ hM hC)
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  have : IsTransitive (hierarchy β) := hierarchy_transitive β
  obtain ⟨hMb, hCb⟩ := kpair_components_mem_transitive hMC
  unfold woodinSeedMatrix
  apply graph_mem hκ (prod_mem_hierarchy_limit hκ hθ hθ) (stage_mem hβ)
  intro z _
  classical
  by_cases hz0 : kpair.π₁ z = ∅
  · simpa [woodinSeedMatrixValue, hz0] using value_mem_stage hz hCb (kpair.π₂ z)
  · simpa [woodinSeedMatrixValue, hz0] using
      value_mem_stage hz hMb ⟨woodinRecursiveIndex (kpair.π₁ z), woodinRecursiveIndex (kpair.π₂ z)⟩ₖ

include hκ h0 hθ in
private theorem seed_columns_mem {Q : V} [IsFunction Q] (hQ : Q ∈ hierarchy κ) :
    woodinSeedProjectionColumn θ Q ∈ hierarchy κ ∧
    woodinSeedSectionColumn θ Q ∈ hierarchy κ ∧
    woodinSeedLiftColumn θ Q ∈ hierarchy κ := by
  obtain ⟨β, hβ, hz, hQb⟩ := common_hierarchy_stage hκ h0 hQ
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  have : IsTransitive (hierarchy β) := hierarchy_transitive β
  have hv := value_mem_stage hz hQb
  have hV := stage_mem hβ
  have hp := prod_mem_hierarchy_limit hκ hV hV
  have hsub (j : V) : Q ‘ j ⊆ hierarchy β := (hierarchy_transitive β).transitive _ (hv j)
  refine ⟨?_, ?_, ?_⟩
  · unfold woodinSeedProjectionColumn
    apply graph_mem hκ hθ (power_mem_hierarchy_limit hκ hp)
    intro j _
    apply mem_power_iff.mpr
    intro z hz'
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz'
    have hb0 : b = ∅ := by simpa using hb
    exact kpair_mem_iff.mpr ⟨hsub j a ha, hb0 ▸ hz⟩
  · unfold woodinSeedSectionColumn
    apply graph_mem hκ hθ (power_mem_hierarchy_limit hκ hp)
    intro j _
    apply mem_power_iff.mpr
    intro z hz'
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz'
    have ha0 : a = ∅ := by simpa using ha
    have hbq : b = Q ‘ j := by simpa using hb
    exact kpair_mem_iff.mpr ⟨ha0 ▸ hz, hbq ▸ hv j⟩
  · unfold woodinSeedLiftColumn
    apply graph_mem hκ hθ (power_mem_hierarchy_limit hκ (prod_mem_hierarchy_limit hκ hp hV))
    intro j _
    apply mem_power_iff.mpr
    intro z hz'
    obtain ⟨w, hw, rfl⟩ := (mem_definableGraph_iff _ _ _ _).mp hz'
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hw
    have hb0 : b = ∅ := by simpa using hb
    exact kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨hsub j a ha, hb0 ▸ hz⟩,
      by simpa only [kpair.π₁_kpair] using hsub j a ha⟩

include hκ hθ in
/-- Seed insertion preserves finite coding rank, including entries in the unused
matrix triangle. Only table functionhood and the rank of the original code are needed. -/
theorem woodinSourceCode_mem_hierarchy {c : V} [IsOrdinal θ]
    (hc : IsForcingIterationCode θ c)
    (hr : forcingIterationCode (forcingCodeP c) (forcingCodeR c) (forcingCodeπ c)
      (forcingCodeE c) (forcingCodeL c) (forcingCodet c) ∈ hierarchy κ) :
    woodinSourceCode θ c ∈ hierarchy κ := by
  have : IsTransitive (hierarchy κ) := hierarchy_transitive κ
  have h0 : (∅ : V) ∈ hierarchy κ := (hierarchy_transitive κ).mem_trans
    (subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)) hθ
  have : IsFunction (forcingCodeP c) := hc.tableP.function
  have : IsFunction (forcingCodeR c) := hc.tableR.function
  have : IsFunction (forcingCodeπ c) := hc.tableπ.function
  have : IsFunction (forcingCodeE c) := hc.tableE.function
  have : IsFunction (forcingCodeL c) := hc.tableL.function
  have : IsFunction (forcingCodet c) := hc.tablet.function
  obtain ⟨hP, hr⟩ := kpair_components_mem_transitive hr
  obtain ⟨hR, hr⟩ := kpair_components_mem_transitive hr
  obtain ⟨hπ, hr⟩ := kpair_components_mem_transitive hr
  obtain ⟨hE, hr⟩ := kpair_components_mem_transitive hr
  obtain ⟨hL, ht⟩ := kpair_components_mem_transitive hr
  have hsingle : ({∅} : V) ∈ hierarchy κ := by simpa using pair_mem_hierarchy_limit hκ h0 h0
  have hp := woodinInsertSeed_mem_hierarchy hκ h0 hθ hP hsingle
  have hr := woodinInsertSeed_mem_hierarchy hκ h0 hθ hR (prod_mem_hierarchy_limit hκ hsingle hsingle)
  have ht' := woodinInsertSeed_mem_hierarchy hκ h0 hθ ht h0
  have hpc := (seed_columns_mem hκ h0 hθ hp).1
  have hec := (seed_columns_mem hκ h0 hθ ht').2.1
  have hlc := (seed_columns_mem hκ h0 hθ hp).2.2
  have : IsFunction (woodinSeedProjectionColumn θ (woodinInsertSeed θ (forcingCodeP c) {∅})) := by
    unfold woodinSeedProjectionColumn; infer_instance
  have : IsFunction (woodinSeedSectionColumn θ (woodinInsertSeed θ (forcingCodet c) ∅)) := by
    unfold woodinSeedSectionColumn; infer_instance
  have : IsFunction (woodinSeedLiftColumn θ (woodinInsertSeed θ (forcingCodeP c) {∅})) := by
    unfold woodinSeedLiftColumn; infer_instance
  exact kpair_mem_hierarchy_limit hκ hp (kpair_mem_hierarchy_limit hκ hr
    (kpair_mem_hierarchy_limit hκ (woodinSeedMatrix_mem_hierarchy hκ h0 hθ hπ hpc)
      (kpair_mem_hierarchy_limit hκ (woodinSeedMatrix_mem_hierarchy hκ h0 hθ hE hec)
        (kpair_mem_hierarchy_limit hκ (woodinSeedMatrix_mem_hierarchy hκ h0 hθ hL hlc) ht'))))


include hκ hθ in
theorem woodinSourceCardinals_mem_hierarchy {K : V} [IsOrdinal θ] [IsFunction K]
    (hK : K ∈ hierarchy κ) (hseed : woodinSeedCardinal ∈ hierarchy κ) :
    woodinSourceCardinals θ K ∈ hierarchy κ := by
  have hz : (∅ : V) ∈ hierarchy κ := (hierarchy_transitive κ).mem_trans
    (subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)) hθ
  exact woodinInsertSeed_mem_hierarchy hκ hz hθ hK hseed

include hκ hθ in
theorem woodinSourceCode_pair_mem_hierarchy {c K : V} [IsOrdinal θ]
    (hc : IsForcingIterationCode θ c) (hK : IsIterationTable θ K)
    (hr : ⟨forcingIterationCode (forcingCodeP c) (forcingCodeR c) (forcingCodeπ c)
      (forcingCodeE c) (forcingCodeL c) (forcingCodet c), K⟩ₖ ∈ hierarchy κ)
    (hseed : woodinSeedCardinal ∈ hierarchy κ) :
    ⟨woodinSourceCode θ c, woodinSourceCardinals θ K⟩ₖ ∈ hierarchy κ := by
  have : IsTransitive (hierarchy κ) := hierarchy_transitive κ
  have : IsFunction K := hK.function
  obtain ⟨hcr, hKr⟩ := kpair_components_mem_transitive hr
  exact kpair_mem_hierarchy_limit hκ (woodinSourceCode_mem_hierarchy hκ hθ hc hcr)
    (woodinSourceCardinals_mem_hierarchy hκ hθ hKr hseed)

theorem woodinSourceCode_finiteRank {γ c : V} [IsOrdinal θ] [IsOrdinal γ]
    (hθ : woodinSourceIndex θ ∈ hierarchy (ordinalAdd γ (ω : V)))
    (hc : IsForcingIterationCode θ c)
    (hr : forcingIterationCode (forcingCodeP c) (forcingCodeR c) (forcingCodeπ c)
      (forcingCodeE c) (forcingCodeL c) (forcingCodet c) ∈ hierarchy (ordinalAdd γ (ω : V))) :
    woodinSourceCode θ c ∈ hierarchy (ordinalAdd γ (ω : V)) :=
  woodinSourceCode_mem_hierarchy (fun _ h ↦ ordinalAdd_omega_succ_closed γ h) hθ hc hr

end ZFVP
