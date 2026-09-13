import ZFVP.ModelTheory.WoodinSparseWitnessPrefix
import ZFVP.ModelTheory.WoodinSparseHomogeneityBuilder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseDirect_pair_support {θ c p q : V} [IsOrdinal θ]
    (hp : p ∈ woodinSparseDirectBase θ c) (hq : q ∈ woodinSparseDirectBase θ c) :
    ∃ k ∈ θ, domain p ∪ domain q ⊆ succ (woodinSourceIndex k) := by
  obtain ⟨_, i, hi, hpi⟩ := mem_woodinSparseDirectBase_iff.mp hp
  obtain ⟨_, j, hj, hqj⟩ := mem_woodinSparseDirectBase_iff.mp hq
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  have hb {i j : V} (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ∈ j) :
      succ (woodinSourceIndex i) ⊆ succ (woodinSourceIndex j) := by
    simpa only [woodinSparseBounds_value hi, woodinSparseBounds_value hj] using woodinSparseBounds_mono hij hj
  rcases IsOrdinal.mem_trichotomy i j with hij | rfl | hji
  · refine ⟨j, hj, ?_⟩
    intro x hx
    exact (mem_union_iff.mp hx).elim (fun hx ↦ hb hi hj hij x (hpi x hx)) (hqj x)
  · refine ⟨i, hi, ?_⟩
    intro x hx
    exact (mem_union_iff.mp hx).elim (hpi x) (hqj x)
  · refine ⟨i, hi, ?_⟩
    intro x hx
    exact (mem_union_iff.mp hx).elim (hpi x) (fun hx ↦ hb hj hi hji x (hqj x hx))

variable {Ω θ a b δ H W : V} [IsOrdinal θ]
local notation "c" => woodinSparsePrefixCode θ
local notation "s" => woodinSparseStageCode θ
local notation "B" i => succ (woodinSourceIndex i)

theorem woodinSparseHomogeneityDirectRow_spec
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hnot : ¬θ ⊆ δ)
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W)
    (hp : a ‘ θ ∈ (forcingCodeP s) ‘ θ) (hq : b ‘ θ ∈ (forcingCodeP s) ‘ θ)
    (ha : ∀ i ∈ θ, a ‘ i = (a ‘ θ) ↾ (B i))
    (hb : ∀ i ∈ θ, b ‘ i = (b ‘ θ) ↾ (B i)) :
    IsCoherentAutomorphismWitnessRow θ s a b δ H W (woodinSparseHomogeneityDirectRow θ H W) := by
  have hc := woodinSparsePrefixCode_valid hΩ hAC hθ
  have hs := woodinSparseStageCode_valid hΩ hAC hθ
  have he := woodinSparseStageCode_extends hΩ hAC hθ
  have hP (i : V) (hi : i ∈ θ) : (forcingCodeP c) ‘ i = (forcingCodeP s) ‘ i :=
    hc.tableP.value_of_subset hs.tableP he.subP hi
  have h00 : ∅ ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hll : ∀ i ∈ θ, succ i ∈ θ := ordinal_limit_of_not_successor hlim
  have hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (B i) p :=
    fun _ hi _ hp ↦ woodinSparsePrefixCode_sparse hΩ hAC hθ hi hp
  have hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (B i) := by
    intro i hi j hj hij p hp
    let := IsOrdinal.of_mem hj
    exact woodinSparsePrefixCode_projection hΩ hAC hθ hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hp
  have hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
      ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p = p :=
    fun _ hi _ hj hij _ hp ↦ woodinSparsePrefixCode_section hΩ hAC hθ hi hj hij hp
  have hp' : a ‘ θ ∈ woodinSparseDirectBase θ c := (woodinSparseStageCode_direct h0 hlim hn).1 ▸ hp
  have hq' : b ‘ θ ∈ woodinSparseDirectBase θ c := (woodinSparseStageCode_direct h0 hlim hn).1 ▸ hq
  let := ((mem_woodinSparseInverseBase_iff hc).mp (mem_woodinSparseDirectBase_iff.mp hp').1).1.1
  let := ((mem_woodinSparseInverseBase_iff hc).mp (mem_woodinSparseDirectBase_iff.mp hq').1).1.1
  have hsupport : ∀ i ∈ θ, domain (a ‘ i) ∪ domain (b ‘ i) ⊆ domain (a ‘ θ) ∪ domain (b ‘ θ) := by
    intro i hi x hx
    rw [ha i hi, hb i hi, domain_restrict_eq, domain_restrict_eq] at hx
    exact (mem_union_iff.mp hx).elim
      (fun hx ↦ mem_union_iff.mpr (Or.inl (mem_inter_iff.mp hx).1))
      (fun hx ↦ mem_union_iff.mpr (Or.inr (mem_inter_iff.mp hx).1))
  obtain ⟨k, hk, hkdom⟩ := woodinSparseDirect_pair_support hp' hq'
  have hA : ∀ i ∈ θ, domain (a ‘ i) ∪ domain (b ‘ i) ⊆ (B k) :=
    fun i hi ↦ subset_trans (hsupport i hi) hkdom
  let u := sparseThreadDecodeValue θ (woodinSparseBounds θ) (a ‘ θ)
  let v := sparseThreadDecodeValue θ (woodinSparseBounds θ) (b ‘ θ)
  have hu := woodinSparseDirectDecodeValue_mem hc hsp hπ hE hp'
  have hv := woodinSparseDirectDecodeValue_mem hc hsp hπ hE hq'
  have hua (i : V) (hi : i ∈ θ) : u ‘ i = a ‘ i := by
    dsimp only [u]
    rw [sparseThreadDecodeValue_apply hi, woodinSparseBounds_value hi, ← ha i hi]
  have hvb (i : V) (hi : i ∈ θ) : v ‘ i = b ‘ i := by
    dsimp only [v]
    rw [sparseThreadDecodeValue_apply hi, woodinSparseBounds_value hi, ← hb i hi]
  have hh := h.of_endpoint_values hua hvb
  have hA' : ∀ i ∈ θ, domain (u ‘ i) ∪ domain (v ‘ i) ⊆ (B k) := by
    intro i hi
    rw [hua i hi, hvb i hi]
    exact hA i hi
  have hue : (woodinSparseDirectFlatten θ c) ‘ u = a ‘ θ := by
    simpa only [woodinSparseDirectDecode_value hp', u] using woodinSparseDirectFlatten_decode hc hsp hπ hE hp'
  have hve : (woodinSparseDirectFlatten θ c) ‘ v = b ‘ θ := by
    simpa only [woodinSparseDirectDecode_value hq', v] using woodinSparseDirectFlatten_decode hc hsp hπ hE hq'
  have hw := h.union_mem_direct hc h00 hll hsp hπ hk hA
  have hcommon := hh.union_common_direct hc h00 hll hsp hπ hE hu hv hk hA'
  rw [hue, hve] at hcommon
  have hf := woodinSparseActualDirectAutomorphism hΩ hAC hθ h.automorphism h00 hll
  have htop : (H ‘ ∅) ‘ ∅ = ∅ := by
    simpa only [woodinSparsePrefixCode_top hΩ hAC hθ h00] using h.fixesTop ∅ h00
  have hfs : IsForcingIsomorphism ((forcingCodeP s) ‘ θ) ((forcingCodeR s) ‘ θ)
      ((forcingCodeP s) ‘ θ) ((forcingCodeR s) ‘ θ) (woodinSparseDirectAutomorphism θ c H) := by
    rw [(woodinSparseStageCode_direct h0 hlim hn).1, (woodinSparseStageCode_direct h0 hlim hn).2]
    exact hf
  constructor <;> simp only [woodinSparseHomogeneityDirectRow, kpair.π₁_kpair, kpair.π₂_kpair]
  · constructor
    · exact hfs
    · rw [woodinSparseStageCode_top hΩ hAC hθ]
      exact (woodinSparseActualDirectAutomorphism_top hΩ hAC hθ h.automorphism h00 hll htop).2
    · intro i hi p hp
      rw [woodinSparseStageCode_projection hΩ hAC hθ hi (function_value_mem hfs.1 hp),
        woodinSparseStageCode_projection hΩ hAC hθ hi hp]
      exact woodinSparseActualDirectAutomorphism_restrict hΩ hAC hθ h.automorphism h00 hll
        ((woodinSparseStageCode_direct h0 hlim hn).1 ▸ hp) hi
    · intro i hi p hp
      have hpc : p ∈ (forcingCodeP c) ‘ i := (hP i hi).symm ▸ hp
      have hmp : (H ‘ i) ‘ p ∈ (forcingCodeP s) ‘ i :=
        hP i hi ▸ function_value_mem (h.automorphism.iso i hi).1 hpc
      rw [woodinSparseStageCode_section hΩ hAC hθ hi hp,
        woodinSparseStageCode_section hΩ hAC hθ hi hmp]
      exact (woodinSparseActualDirectAutomorphism_section hΩ hAC hθ h.automorphism h00 hll hi hpc).2
  · intro p hp
    exact woodinSparseActualDirectAutomorphism_domain hΩ hAC hθ h.automorphism h00 hll h.preservesDomain
      ((woodinSparseStageCode_direct h0 hlim hn).1 ▸ hp)
  · exact fun hθδ ↦ (hnot hθδ).elim
  · exact (woodinSparseStageCode_direct h0 hlim hn).1.symm ▸ hw
  · exact (woodinSparseStageCode_direct h0 hlim hn).2.symm ▸ hcommon.1
  · exact (woodinSparseStageCode_direct h0 hlim hn).2.symm ▸ hcommon.2
  · intro i hi
    rw [woodinSparseStageCode_projection hΩ hAC hθ hi ((woodinSparseStageCode_direct h0 hlim hn).1.symm ▸ hw)]
    exact h.union_restrict hc hsp hπ hi
  · exact h.union_support hsupport
  · exact fun hθδ ↦ (hnot hθδ).elim

end ZFVP
