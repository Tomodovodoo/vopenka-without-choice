import ZFVP.ModelTheory.WoodinSparseHomogeneityBuilder
import ZFVP.ModelTheory.CoherentAutomorphismSuccessorRow
import ZFVP.ModelTheory.WoodinSparseWitnessPrefix

set_option maxHeartbeats 1000000

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω k a b δ H W : V} [IsOrdinal k]
local notation "c" => woodinSparsePrefixCode (succ k)
local notation "s" => woodinSparseStageCode (succ k)
local notation "P" => (forcingCodeP c) ‘ k
local notation "R" => (forcingCodeR c) ‘ k
local notation "o" => (forcingCodet c) ‘ k
local notation "C" => (forcingCodeP s) ‘ (succ k)
local notation "T" => (forcingCodeR s) ‘ (succ k)
local notation "A" => woodinSourceIndex (succ k)
local notation "g" => woodinSparseSuccessorHomogenizingMap k (H ‘ k) (a ‘ (succ k)) (b ‘ (succ k))
local notation "w" => woodinSparseSuccessorCommonWitness k (H ‘ k) (a ‘ (succ k)) (b ‘ (succ k)) (W ‘ k)

theorem woodinSparseHomogeneitySuccessorRow_spec
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω)
    (hh : IsCoherentAutomorphismWitnessHistory (succ k) c a b δ H W)
    (hδ : ¬succ k ⊆ δ)
    (ha : a ‘ (succ k) ∈ C) (hb : b ‘ (succ k) ∈ C)
    (hap : a ‘ k = (a ‘ (succ k)) ↾ A) (hbp : b ‘ k = (b ‘ (succ k)) ↾ A) :
    IsCoherentAutomorphismWitnessRow (succ k) s a b δ H W
      (woodinSparseHomogeneitySuccessorRow k H W (a ‘ (succ k)) (b ‘ (succ k))) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hk
  have hc := woodinSparsePrefixCode_valid hΩ hAC hsub
  have hs := woodinSparseStageCode_valid hΩ hAC hsub
  have hex := woodinSparseStageCode_extends hΩ hAC hsub
  have hPval : ∀ i ∈ succ k, (forcingCodeP c) ‘ i = (forcingCodeP s) ‘ i :=
    fun _ hi ↦ hc.tableP.value_of_subset hs.tableP hex.subP hi
  have hRval : ∀ i ∈ succ k, (forcingCodeR c) ‘ i = (forcingCodeR s) ‘ i :=
    fun _ hi ↦ hc.tableR.value_of_subset hs.tableR hex.subR hi
  have htval : ∀ i ∈ succ k, (forcingCodet c) ‘ i = (forcingCodet s) ‘ i :=
    fun _ hi ↦ hc.tablet.value_of_subset hs.tablet hex.subt hi
  have hhs : IsCoherentAutomorphismWitnessHistory (succ k) s a b δ H W :=
    hh.of_code_values (fun _ hi ↦ (hPval _ hi).symm) (fun _ hi ↦ (hRval _ hi).symm)
      (fun _ hi ↦ (htval _ hi).symm)
      (fun _ hi _ hj ↦ (hc.tableπ.value_of_subset hs.tableπ hex.subπ (kpair_mem_iff.mpr ⟨hi,hj⟩)).symm)
      (fun _ hi _ hj ↦ (hc.tableE.value_of_subset hs.tableE hex.subE (kpair_mem_iff.mpr ⟨hi,hj⟩)).symm)
  have hf : IsForcingAutomorphism P R (H ‘ k) := hh.automorphism.iso k (mem_succ_self k)
  have hft : (H ‘ k) ‘ o = o := hh.fixesTop k (mem_succ_self k)
  have hdom : ∀ z ∈ P, domain ((H ‘ k) ‘ z) = domain z := hh.preservesDomain k (mem_succ_self k)
  have hg := woodinSparseSuccessorHomogenizingMap_automorphism hΩ hAC hk hf hft ha hb
  have hπ : ∀ z ∈ C, ((forcingCodeπ s) ‘ ⟨k,succ k⟩ₖ) ‘ z = z ↾ A := by
    intro z hz
    simpa only [woodinSourceIndex_successor] using woodinSparseStageCode_projection hΩ hAC hsub (mem_succ_self k) hz
  have hrow : IsCoherentAutomorphismRow (succ k) s H g := by
    apply coherentAutomorphismRow_of_successor hs (mem_succ_self _) hhs.automorphism hg
    · rw [woodinSparseStageCode_top hΩ hAC hsub]
      exact woodinSparseSuccessorHomogenizingMap_top hΩ hAC hk hf hft ha hb
    · intro z hz
      rw [hπ _ (function_value_mem hg.1 hz), hπ z hz]
      exact woodinSparseSuccessorHomogenizingMap_restrict hΩ hAC hk hf hft ha hb hz
    · intro z hz
      rw [woodinSparseStageCode_section hΩ hAC hsub (mem_succ_self k) hz,
        woodinSparseStageCode_section hΩ hAC hsub (mem_succ_self k)
          (function_value_mem (hhs.automorphism.iso k (mem_succ_self k)).1 hz)]
      have hz' : z ∈ P := by rwa [hPval k (mem_succ_self k)]
      exact woodinSparseSuccessorHomogenizingMap_base hΩ hAC hk hf hft ha hb hz'
  have hrp : ⟨W ‘ k, (H ‘ k) ‘ ((a ‘ (succ k)) ↾ A)⟩ₖ ∈ R := by
    rw [← hap]
    exact hh.left k (mem_succ_self k)
  have hrq : ⟨W ‘ k, (b ‘ (succ k)) ↾ A⟩ₖ ∈ R := by
    rw [← hbp]
    exact hh.right k (mem_succ_self k)
  have hw := woodinSparseSuccessorCommonWitness_spec hΩ hAC hk hf hft ha hb
    (hh.mem k (mem_succ_self k)) hrp hrq hdom
  have hWdom : domain (W ‘ k) ⊆ domain (a ‘ (succ k)) ∪ domain (b ‘ (succ k)) := by
    intro x hx
    have hx' := hh.support k (mem_succ_self k) x hx
    rw [hap, hbp, domain_restrict_eq, domain_restrict_eq] at hx'
    rcases mem_union_iff.mp hx' with hx' | hx'
    · exact mem_union_iff.mpr (Or.inl (mem_inter_iff.mp hx').1)
    · exact mem_union_iff.mpr (Or.inr (mem_inter_iff.mp hx').1)
  have hpw : ((forcingCodeπ s) ‘ ⟨k,succ k⟩ₖ) ‘ w = W ‘ k := by rw [hπ w hw.1]; exact hw.2.2.2.1
  unfold woodinSparseHomogeneitySuccessorRow
  constructor <;> simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  · exact hrow
  · intro p hp
    exact woodinSparseSuccessorHomogenizingMap_domain hΩ hAC hk hf hft ha hb hdom hp
  · exact fun h ↦ (hδ h).elim
  · exact hw.1
  · exact hw.2.1
  · exact hw.2.2.1
  · exact coherentWitnessProjection_of_successor hs (mem_succ_self _) hw.1 hhs.proj hpw
  · intro x hx
    rcases mem_union_iff.mp (hw.2.2.2.2 x hx) with hx | hx
    · rcases mem_union_iff.mp hx with hx | hx
      · exact hWdom x hx
      · exact mem_union_iff.mpr (Or.inl hx)
    · exact mem_union_iff.mpr (Or.inr hx)
  · exact fun h ↦ (hδ h).elim

end ZFVP
