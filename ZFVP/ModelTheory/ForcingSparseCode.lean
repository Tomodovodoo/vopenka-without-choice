import ZFVP.SetTheory.ForcingMinimalSupportCodes
import ZFVP.ModelTheory.ForcingCodeConstructionUniform
import ZFVP.ModelTheory.ForcingIsomorphismComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingSparseCodes (θ s U : V) : V :=
  forcingMinimalSupportCodes θ (forcingCodeP s) (forcingCodeE s) U

instance forcingSparseCodes_definable : ℒₛₑₜ-function₃[V] forcingSparseCodes := by
  have h : ℒₛₑₜ-relation₄[V] (fun C θ s U ↦ ∀ a, a ∈ C ↔ ∃ k ∈ θ, ∃ p ∈ U,
    a = ⟨k, p⟩ₖ ∧ IsMinimalSectionPoint (forcingCodeP s) (forcingCodeE s) k p) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingSparseCodes (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingSparseCodes, mem_forcingMinimalSupportCodes_iff]

noncomputable def forcingSparseDecode (θ s U : V) : V :=
  forcingMinimalSupportMap θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) U

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₅.comp

instance forcingSparseDecode_definable : ℒₛₑₜ-function₃[V] forcingSparseDecode := by
  have h : ℒₛₑₜ-relation₄[V] (fun g θ s U ↦ ∀ z, z ∈ g ↔ ∃ a ∈ forcingSparseCodes θ s U,
    z = ⟨a, forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) (kpair.π₁ a) (kpair.π₂ a)⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingSparseDecode (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingSparseDecode, forcingMinimalSupportMap, mem_definableGraph_iff,
    forcingMinimalSupportDecode, forcingSparseCodes]

noncomputable def forcingSparseOrder (θ s U : V) : V :=
  forcingPullbackOrder (forcingSparseCodes θ s U)
    (forcingThreadOrder θ (forcingCodeR s)
      (forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) U))
    (forcingSparseDecode θ s U)

instance forcingSparseOrder_definable : ℒₛₑₜ-function₃[V] forcingSparseOrder := by
  have h : ℒₛₑₜ-relation₄[V] (fun R θ s U ↦ ∀ z, z ∈ R ↔
    z ∈ (forcingSparseCodes θ s U) ×ˢ (forcingSparseCodes θ s U) ∧
      ⟨(forcingSparseDecode θ s U) ‘ (kpair.π₁ z), (forcingSparseDecode θ s U) ‘ (kpair.π₂ z)⟩ₖ ∈
        forcingThreadOrder θ (forcingCodeR s)
          (forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) U)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingSparseOrder (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingSparseOrder, forcingPullbackOrder, mem_sep_iff]

noncomputable def forcingSparseEncode (θ s U : V) : V := converseGraph (forcingSparseDecode θ s U)

instance forcingSparseEncode_definable : ℒₛₑₜ-function₃[V] forcingSparseEncode := by
  unfold forcingSparseEncode
  definability

variable {θ s U : V} [IsOrdinal θ]
variable (hs : IsForcingIterationCode θ s) (hU : ∀ i ∈ θ, (forcingCodeP s) ‘ i ⊆ U)
local notation "D" => forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) U
local notation "R" => forcingThreadOrder θ (forcingCodeR s) D

include hs hU in
theorem forcingSparseDecode_isomorphism :
    IsForcingIsomorphism (forcingSparseCodes θ s U) (forcingSparseOrder θ s U) D R
      (forcingSparseDecode θ s U) :=
  forcingMinimalSupportMap_isomorphism hs.system.split hU

include hs hU in
theorem forcingSparseEncode_isomorphism :
    IsForcingIsomorphism D R (forcingSparseCodes θ s U) (forcingSparseOrder θ s U)
      (forcingSparseEncode θ s U) := (forcingSparseDecode_isomorphism hs hU).inverse

include hs hU in
theorem forcingSparseOrder_preorder :
    IsForcingPreorder (forcingSparseCodes θ s U) (forcingSparseOrder θ s U) :=
  forcingPullbackOrder_preorder (forcingDirectLimit_preorder hs.system.order.preorder)
    (forcingSparseDecode_isomorphism hs hU).1

theorem forcingSparseCodes_subset_hierarchy (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hP : ∀ i ∈ θ, (forcingCodeP s) ‘ i ∈ hierarchy θ) :
    forcingSparseCodes θ s U ⊆ hierarchy θ :=
  forcingMinimalSupportCodes_subset_hierarchy hlim hP

theorem forcingSparseOrder_subset_hierarchy (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hP : ∀ i ∈ θ, (forcingCodeP s) ‘ i ∈ hierarchy θ) :
    forcingSparseOrder θ s U ⊆ hierarchy θ := by
  intro z hz
  unfold forcingSparseOrder forcingPullbackOrder at hz
  have hz' : z ∈ (forcingSparseCodes θ s U) ×ˢ (forcingSparseCodes θ s U) := (mem_sep_iff.mp hz).1
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz'
  exact kpair_mem_hierarchy_limit hlim (forcingSparseCodes_subset_hierarchy hlim hP a ha)
    (forcingSparseCodes_subset_hierarchy hlim hP b hb)

include hs hU in
theorem forcingSparseEncode_decode {f : V} (hf : f ∈ D) :
    (forcingSparseDecode θ s U) ‘ ((forcingSparseEncode θ s U) ‘ f) = f :=
  (forcingSparseDecode_isomorphism hs hU).value_inverse hf

include hs hU in
theorem forcingSparseEncode_least_support {f k : V} (hf : f ∈ D)
    (hk : IsLeastOrdinal (IsThreadSupport θ (forcingCodeE s) f) k) :
    (forcingSparseEncode θ s U) ‘ f = ⟨k, f ‘ k⟩ₖ := by
  have hfi := forcingDirectLimit_subset _ _ _ _ _ _ hf
  have hp := minimalSectionPoint_of_least_support hs.system.split hU hfi hk
  have ha : ⟨k, f ‘ k⟩ₖ ∈ forcingSparseCodes θ s U :=
    (mem_forcingMinimalSupportCodes_iff _ _ _ _ _).mpr
      ⟨k, hk.2.1.1, f ‘ k, hU k hk.2.1.1 _ hp.1, rfl, hp⟩
  have he : (forcingSparseDecode θ s U) ‘ ⟨k, f ‘ k⟩ₖ = f := by
    rw [forcingSparseDecode, forcingMinimalSupportMap_value ha, forcingMinimalSupportDecode_pair]
    exact (forcingThread_eq_section_of_support hs.system.split hfi hk.2.1 hU).symm
  simpa only [he, forcingSparseEncode] using (forcingSparseDecode_isomorphism hs hU).inverse_value ha

end ZFVP
