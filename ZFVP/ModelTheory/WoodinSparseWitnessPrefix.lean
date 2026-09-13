import ZFVP.ModelTheory.CoherentAutomorphismWitnessLimits
import ZFVP.ModelTheory.WoodinSparseStageCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCoherentAutomorphismWitnessHistory.of_endpoint_values {θ c a b a' b' δ H W : V}
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W)
    (ha : ∀ i ∈ θ, a' ‘ i = a ‘ i) (hb : ∀ i ∈ θ, b' ‘ i = b ‘ i) :
    IsCoherentAutomorphismWitnessHistory θ c a' b' δ H W := by
  refine ⟨h.mapsTable, h.boundsTable, h.automorphism, h.fixesTop, h.preservesDomain,
    h.fixesInitial, h.mem, ?_, ?_, h.proj, ?_, ?_⟩
  · intro i hi
    rw [ha i hi]
    exact h.left i hi
  · intro i hi
    rw [hb i hi]
    exact h.right i hi
  · intro i hi
    rw [ha i hi, hb i hi]
    exact h.support i hi
  · intro i hi
    rw [ha i hi]
    exact h.initialWitness i hi

theorem IsCoherentAutomorphismWitnessRow.of_code_values {θ c d a b δ H W z : V}
    (h : IsCoherentAutomorphismWitnessRow θ c a b δ H W z)
    (hP : ∀ i ∈ succ θ, (forcingCodeP c) ‘ i = (forcingCodeP d) ‘ i)
    (hR : (forcingCodeR c) ‘ θ = (forcingCodeR d) ‘ θ)
    (ht : (forcingCodet c) ‘ θ = (forcingCodet d) ‘ θ)
    (hπ : ∀ i ∈ θ, (forcingCodeπ c) ‘ ⟨i, θ⟩ₖ = (forcingCodeπ d) ‘ ⟨i, θ⟩ₖ)
    (hE : ∀ i ∈ θ, (forcingCodeE c) ‘ ⟨i, θ⟩ₖ = (forcingCodeE d) ‘ ⟨i, θ⟩ₖ) :
    IsCoherentAutomorphismWitnessRow θ d a b δ H W z := by
  constructor
  · constructor
    · rw [← hP θ (mem_succ_self θ), ← hR]
      exact h.automorphism.iso
    · rw [← ht]
      exact h.automorphism.fixesTop
    · intro i hi p hp
      rw [← hP θ (mem_succ_self θ)] at hp
      rw [← hπ i hi]
      exact h.automorphism.proj i hi p hp
    · intro i hi p hp
      rw [← hP i (mem_succ_iff.mpr (Or.inr hi))] at hp
      rw [← hE i hi]
      exact h.automorphism.sec i hi p hp
  · rw [← hP θ (mem_succ_self θ)]
    exact h.preservesDomain
  · rw [← hP θ (mem_succ_self θ)]
    exact h.fixesInitial
  · rw [← hP θ (mem_succ_self θ)]
    exact h.mem
  · rw [← hR]
    exact h.left
  · rw [← hR]
    exact h.right
  · intro i hi
    rw [← hπ i hi]
    exact h.proj i hi
  · exact h.support
  · exact h.initialWitness

theorem IsCoherentAutomorphismWitnessRow.of_code_extension {θ η c d a b δ H W z : V}
    (h : IsCoherentAutomorphismWitnessRow θ c a b δ H W z)
    (hc : IsForcingIterationCode (succ θ) c) (hd : IsForcingIterationCode η d)
    (he : ForcingCodeExtends c d) : IsCoherentAutomorphismWitnessRow θ d a b δ H W z :=
  h.of_code_values (fun _ hi ↦ hc.tableP.value_of_subset hd.tableP he.subP hi)
    (hc.tableR.value_of_subset hd.tableR he.subR (mem_succ_self θ))
    (hc.tablet.value_of_subset hd.tablet he.subt (mem_succ_self θ))
    (fun _ hi ↦ hc.tableπ.value_of_subset hd.tableπ he.subπ
      (kpair_mem_iff.mpr ⟨mem_succ_iff.mpr (Or.inr hi), mem_succ_self θ⟩))
    (fun _ hi ↦ hc.tableE.value_of_subset hd.tableE he.subE
      (kpair_mem_iff.mpr ⟨mem_succ_iff.mpr (Or.inr hi), mem_succ_self θ⟩))

theorem IsCoherentAutomorphismWitnessHistory.of_code_values {θ c d a b δ H W : V}
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W)
    (hP : ∀ i ∈ θ, (forcingCodeP d) ‘ i = (forcingCodeP c) ‘ i)
    (hR : ∀ i ∈ θ, (forcingCodeR d) ‘ i = (forcingCodeR c) ‘ i)
    (ht : ∀ i ∈ θ, (forcingCodet d) ‘ i = (forcingCodet c) ‘ i)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, (forcingCodeπ d) ‘ ⟨i, j⟩ₖ = (forcingCodeπ c) ‘ ⟨i, j⟩ₖ)
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, (forcingCodeE d) ‘ ⟨i, j⟩ₖ = (forcingCodeE c) ‘ ⟨i, j⟩ₖ) :
    IsCoherentAutomorphismWitnessHistory θ d a b δ H W := by
  constructor
  · exact h.mapsTable
  · exact h.boundsTable
  · constructor
    · intro i hi
      rw [hP i hi, hR i hi]
      exact h.automorphism.iso i hi
    · intro i hi j hj hij p hp
      rw [hP j hj] at hp
      rw [hπ i hi j hj]
      exact h.automorphism.proj i hi j hj hij p hp
    · intro i hi j hj hij p hp
      rw [hP i hi] at hp
      rw [hE i hi j hj]
      exact h.automorphism.sec i hi j hj hij p hp
  · intro i hi
    rw [ht i hi]
    exact h.fixesTop i hi
  · intro i hi
    rw [hP i hi]
    exact h.preservesDomain i hi
  · intro i hi
    rw [hP i hi]
    exact h.fixesInitial i hi
  · intro i hi
    rw [hP i hi]
    exact h.mem i hi
  · intro i hi
    rw [hR i hi]
    exact h.left i hi
  · intro i hi
    rw [hR i hi]
    exact h.right i hi
  · intro i hi j hj hij
    rw [hπ i hi j hj]
    exact h.proj i hi j hj hij
  · exact h.support
  · exact h.initialWitness

theorem IsCoherentAutomorphismWitnessHistory.of_code_extension {θ η c d a b δ H W : V}
    (h : IsCoherentAutomorphismWitnessHistory θ c a b δ H W)
    (hc : IsForcingIterationCode η c) (hd : IsForcingIterationCode θ d)
    (he : ForcingCodeExtends d c) : IsCoherentAutomorphismWitnessHistory θ d a b δ H W :=
  h.of_code_values (fun _ hi ↦ hd.tableP.value_of_subset hc.tableP he.subP hi)
    (fun _ hi ↦ hd.tableR.value_of_subset hc.tableR he.subR hi)
    (fun _ hi ↦ hd.tablet.value_of_subset hc.tablet he.subt hi)
    (fun _ hi _ hj ↦ hd.tableπ.value_of_subset hc.tableπ he.subπ (kpair_mem_iff.mpr ⟨hi, hj⟩))
    (fun _ hi _ hj ↦ hd.tableE.value_of_subset hc.tableE he.subE (kpair_mem_iff.mpr ⟨hi, hj⟩))

theorem woodinSparsePrefixCode_extends_endpoint {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    ForcingCodeExtends (woodinSparsePrefixCode θ) (woodinSparseStageCode Ω) := by
  let := hΩ.inaccessible.1
  exact (woodinSparsePrefixCode_extends hΩ hAC (subset_refl Ω) hθ).trans
    (woodinSparseStageCode_endpoint_extends hΩ hAC)

theorem woodinSparseStageCode_extends_endpoint {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    ForcingCodeExtends (woodinSparseStageCode θ) (woodinSparseStageCode Ω) := by
  let := hΩ.inaccessible.1
  rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
  · exact ForcingCodeExtends.refl _
  · rw [woodinSparseStageCode_eq_prefix hΩ hAC hθ]
    apply woodinSparsePrefixCode_extends_endpoint hΩ hAC
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hθ
    · exact IsOrdinal.toIsTransitive.mem_trans hi hθ

theorem woodinSparseStageCode_endpoint_row_values {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    (forcingCodeP (woodinSparseStageCode θ)) ‘ θ = (forcingCodeP (woodinSparseStageCode Ω)) ‘ θ ∧
    (forcingCodeR (woodinSparseStageCode θ)) ‘ θ = (forcingCodeR (woodinSparseStageCode Ω)) ‘ θ ∧
    (forcingCodet (woodinSparseStageCode θ)) ‘ θ = (forcingCodet (woodinSparseStageCode Ω)) ‘ θ := by
  have hs := woodinSparseStageCode_valid hΩ hAC hθ
  have hz := woodinSparseStageCode_endpoint_valid hΩ hAC
  have he := woodinSparseStageCode_extends_endpoint hΩ hAC hθ
  exact ⟨hs.tableP.value_of_subset hz.tableP he.subP (mem_succ_self θ),
    hs.tableR.value_of_subset hz.tableR he.subR (mem_succ_self θ),
    hs.tablet.value_of_subset hz.tablet he.subt (mem_succ_self θ)⟩

theorem IsCoherentAutomorphismWitnessHistory.woodin_prefix {Ω θ a b δ H W : V} [IsOrdinal θ]
    (h : IsCoherentAutomorphismWitnessHistory θ (woodinSparseStageCode Ω) a b δ H W)
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsCoherentAutomorphismWitnessHistory θ (woodinSparsePrefixCode θ) a b δ H W :=
  h.of_code_extension (woodinSparseStageCode_endpoint_valid hΩ hAC)
    (woodinSparsePrefixCode_valid hΩ hAC hθ) (woodinSparsePrefixCode_extends_endpoint hΩ hAC hθ)

theorem IsCoherentAutomorphismWitnessRow.woodin_endpoint {Ω θ a b δ H W z : V} [IsOrdinal θ]
    (h : IsCoherentAutomorphismWitnessRow θ (woodinSparseStageCode θ) a b δ H W z)
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsCoherentAutomorphismWitnessRow θ (woodinSparseStageCode Ω) a b δ H W z :=
  h.of_code_extension (woodinSparseStageCode_valid hΩ hAC hθ)
    (woodinSparseStageCode_endpoint_valid hΩ hAC) (woodinSparseStageCode_extends_endpoint hΩ hAC hθ)

end ZFVP
