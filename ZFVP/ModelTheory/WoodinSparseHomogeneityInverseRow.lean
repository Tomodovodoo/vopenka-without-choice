import ZFVP.ModelTheory.WoodinSparseHomogeneityDirectRow

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ a b δ H W : V} [IsOrdinal θ]
local notation "c" => woodinSparsePrefixCode θ
local notation "s" => woodinSparseStageCode θ
local notation "B" i => succ (woodinSourceIndex i)

theorem woodinSparseHomogeneityInverseRow_spec
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hnot : ¬θ ⊆ δ)
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W)
    (hp : a ‘ θ ∈ (forcingCodeP s) ‘ θ) (hq : b ‘ θ ∈ (forcingCodeP s) ‘ θ)
    (ha : ∀ i ∈ θ, a ‘ i = (a ‘ θ) ↾ (B i))
    (hb : ∀ i ∈ θ, b ‘ i = (b ‘ θ) ↾ (B i)) :
    IsCoherentAutomorphismWitnessRow θ s a b δ H W
      (woodinSparseHomogeneityInverseRow θ H W (a ‘ θ) (b ‘ θ)) := by
  let := hΩ.inaccessible.1
  have hsub : θ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hθ
  have hc := woodinSparsePrefixCode_valid hΩ hAC hsub
  have hs := woodinSparseStageCode_valid hΩ hAC hsub
  have he := woodinSparseStageCode_extends hΩ hAC hsub
  have hP (i : V) (hi : i ∈ θ) : (forcingCodeP c) ‘ i = (forcingCodeP s) ‘ i :=
    hc.tableP.value_of_subset hs.tableP he.subP hi
  have h00 : ∅ ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hll : ∀ i ∈ θ, succ i ∈ θ := ordinal_limit_of_not_successor hlim
  have hB (i : V) (hi : i ∈ θ) : (B i) ⊆ θ := by
    simpa only [woodinSparseBounds_value hi] using woodinSparseBounds_limit_subset h00 hll hi
  have hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (B i) p :=
    fun _ hi _ hp ↦ woodinSparsePrefixCode_sparse hΩ hAC hsub hi hp
  have hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (B i) := by
    intro i hi j hj hij p hp
    let := IsOrdinal.of_mem hj
    exact woodinSparsePrefixCode_projection hΩ hAC hsub hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hp
  have hraw {p : V} (hp : p ∈ (forcingCodeP s) ‘ θ) : p ↾ θ ∈ woodinSparseInverseBase θ c := by
    rw [(woodinSparseStageCode_inverse h0 hlim hn).1] at hp
    exact (mem_sparsePairCarrier_iff.mp hp).2.1
  let u := sparseThreadDecodeValue θ (woodinSparseBounds θ) ((a ‘ θ) ↾ θ)
  let v := sparseThreadDecodeValue θ (woodinSparseBounds θ) ((b ‘ θ) ↾ θ)
  have hu : u ∈ forcingInverseCodePoset θ c := by
    rw [woodinSparseInverse_threads hsp hπ]
    exact sparseThreadDecodeValue_mem (hraw hp) hc.subset_universe
  have hv : v ∈ forcingInverseCodePoset θ c := by
    rw [woodinSparseInverse_threads hsp hπ]
    exact sparseThreadDecodeValue_mem (hraw hq) hc.subset_universe
  have hua (i : V) (hi : i ∈ θ) : u ‘ i = a ‘ i := by
    dsimp only [u]
    rw [sparseThreadDecodeValue_apply hi, woodinSparseBounds_value hi,
      restrict_restrict_of_subset (hB i hi), ← ha i hi]
  have hvb (i : V) (hi : i ∈ θ) : v ‘ i = b ‘ i := by
    dsimp only [v]
    rw [sparseThreadDecodeValue_apply hi, woodinSparseBounds_value hi,
      restrict_restrict_of_subset (hB i hi), ← hb i hi]
  have hue : (woodinSparseInverseFlatten θ c) ‘ u = (a ‘ θ) ↾ θ := by
    rw [woodinSparseInverseFlatten_value hsp hπ hu]
    exact sparseThread_union_decodeValue ((mem_woodinSparseInverseBase_iff hc).mp (hraw hp)).1
      (fun _ hx ↦ woodinSparseBounds_cover hx)
  have hve : (woodinSparseInverseFlatten θ c) ‘ v = (b ‘ θ) ↾ θ := by
    rw [woodinSparseInverseFlatten_value hsp hπ hv]
    exact sparseThread_union_decodeValue ((mem_woodinSparseInverseBase_iff hc).mp (hraw hq)).1
      (fun _ hx ↦ woodinSparseBounds_cover hx)
  have hh := h.of_endpoint_values hua hvb
  have hcommon := hh.union_common hc h00 hll hsp hπ hu hv
  rw [hue, hve] at hcommon
  have hw := h.union_mem hc h00 hll hsp hπ
  let f := woodinSparseInverseAutomorphism θ c H
  have hf : IsForcingAutomorphism (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) f :=
    woodinSparseActualInverseAutomorphism hΩ hAC hsub h.automorphism h00 hll
  have htop : (H ‘ ∅) ‘ ∅ = ∅ := by
    simpa only [woodinSparsePrefixCode_top hΩ hAC hsub h00] using h.fixesTop ∅ h00
  have hft : f ‘ ∅ = ∅ :=
    (woodinSparseActualInverseAutomorphism_top hΩ hAC hsub h.automorphism h00 hll htop).2
  have hfdom : ∀ p ∈ woodinSparseInverseBase θ c, domain (f ‘ p) = domain p :=
    fun _ hp ↦ woodinSparseActualInverseAutomorphism_domain hΩ hAC hsub h.automorphism h00 hll h.preservesDomain hp
  have hfull := woodinSparseCompletedHomogenizingMap_automorphism hΩ hAC hθ h0 hlim hn hf hft hp hq
  have hwfull := woodinSparseCompletedCommonWitness_spec hΩ hAC hθ h0 hlim hn hf hft hp hq
    hw hcommon.1 hcommon.2 hfdom
  let := (woodinSparseStageCode_sparse hΩ hAC hsub hp).1
  let := (woodinSparseStageCode_sparse hΩ hAC hsub hq).1
  have hsupport : domain (⋃ˢ range W) ⊆ domain (a ‘ θ) ∪ domain (b ‘ θ) := by
    apply h.union_support
    intro i hi x hx
    rw [ha i hi, hb i hi, domain_restrict_eq, domain_restrict_eq] at hx
    exact (mem_union_iff.mp hx).elim
      (fun hx ↦ mem_union_iff.mpr (Or.inl (mem_inter_iff.mp hx).1))
      (fun hx ↦ mem_union_iff.mpr (Or.inr (mem_inter_iff.mp hx).1))
  have hcol (i : V) (hi : i ∈ θ) (p : V) (hp : p ∈ (forcingCodeP s) ‘ θ) :
      ((woodinSparseCompletedHomogenizingMap θ f (a ‘ θ) (b ‘ θ)) ‘ p) ↾ (B i) =
        (H ‘ i) ‘ (p ↾ (B i)) := by
    rw [← restrict_restrict_of_subset (hB i hi),
      woodinSparseCompletedHomogenizingMap_restrict hΩ hAC hθ h0 hlim hn hf hft ‹a ‘ θ ∈ _› hq hp,
      woodinSparseActualInverseAutomorphism_restrict hΩ hAC hsub h.automorphism h00 hll (hraw hp) hi,
      restrict_restrict_of_subset (hB i hi)]
  constructor <;> simp only [woodinSparseHomogeneityInverseRow, kpair.π₁_kpair, kpair.π₂_kpair]
  · constructor
    · exact hfull
    · rw [woodinSparseStageCode_top hΩ hAC hsub]
      exact woodinSparseCompletedHomogenizingMap_top hΩ hAC hθ h0 hlim hn hf hft hp hq
    · intro i hi p hp
      rw [woodinSparseStageCode_projection hΩ hAC hsub hi (function_value_mem hfull.1 hp),
        woodinSparseStageCode_projection hΩ hAC hsub hi hp]
      exact hcol i hi p hp
    · intro i hi p hp
      have hpc : p ∈ (forcingCodeP c) ‘ i := (hP i hi).symm ▸ hp
      have hmp : (H ‘ i) ‘ p ∈ (forcingCodeP s) ‘ i :=
        hP i hi ▸ function_value_mem (h.automorphism.iso i hi).1 hpc
      have hpcurr := hs.system.split.secMaps i (mem_succ_iff.mpr (Or.inr hi)) θ (mem_succ_self θ)
        (IsOrdinal.toIsTransitive.transitive _ hi) p hp
      rw [woodinSparseStageCode_section hΩ hAC hsub hi hp] at hpcurr
      have hps := hsp i hi p hpc
      let := hps.1
      have hdom : domain p ⊆ θ := subset_trans hps.2.1 (hB i hi)
      have hz : p ‘ θ = ∅ := value_eq_empty_of_not_mem_domain (fun hx ↦ mem_irrefl θ (hdom θ hx))
      rw [woodinSparseStageCode_section hΩ hAC hsub hi hp,
        woodinSparseStageCode_section hΩ hAC hsub hi hmp,
        woodinSparseCompletedHomogenizingMap_empty_tail hΩ hAC hθ h0 hlim hn hf hft ‹a ‘ θ ∈ _› hq hpcurr hz,
        IsFunction.restrict_eq_self p θ hdom]
      exact (woodinSparseActualInverseAutomorphism_section hΩ hAC hsub h.automorphism h00 hll hi hpc).2
  · intro p hp
    exact woodinSparseCompletedHomogenizingMap_domain hΩ hAC hθ h0 hlim hn hf hft ‹a ‘ θ ∈ _› hq hfdom hp
  · exact fun hθδ ↦ (hnot hθδ).elim
  · exact hwfull.1
  · exact hwfull.2.1
  · exact hwfull.2.2.1
  · intro i hi
    rw [woodinSparseStageCode_projection hΩ hAC hsub hi hwfull.1,
      ← restrict_restrict_of_subset (hB i hi), hwfull.2.2.2.1]
    exact h.union_restrict hc hsp hπ hi
  · intro x hx
    have hh := hwfull.2.2.2.2 x hx
    rcases mem_union_iff.mp hh with hh | hh
    · rcases mem_union_iff.mp hh with hh | hh
      · exact hsupport x hh
      · exact mem_union_iff.mpr (Or.inl hh)
    · exact mem_union_iff.mpr (Or.inr hh)
  · exact fun hθδ ↦ (hnot hθδ).elim

end ZFVP
