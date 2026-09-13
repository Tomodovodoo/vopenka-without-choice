import ZFVP.ModelTheory.WoodinSparseWitnessPrefix
import ZFVP.ModelTheory.WoodinSparseStageLaws

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseEndpointThread (Ω p : V) : V :=
  definableGraph (succ Ω) (fun i ↦ ((forcingCodeπ (woodinSparseStageCode Ω)) ‘ ⟨i,Ω⟩ₖ) ‘ p) (by definability)

instance woodinSparseEndpointThread_definable : ℒₛₑₜ-function₂[V] woodinSparseEndpointThread := by
  have h : ℒₛₑₜ-relation₃[V] (fun t Ω p ↦ ∀ z, z ∈ t ↔ ∃ i ∈ succ Ω,
    z = ⟨i, ((forcingCodeπ (woodinSparseStageCode Ω)) ‘ ⟨i,Ω⟩ₖ) ‘ p⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinSparseEndpointThread (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [woodinSparseEndpointThread, mem_definableGraph_iff]

theorem woodinSparseEndpointThread_table (Ω p : V) :
    IsIterationTable (succ Ω) (woodinSparseEndpointThread Ω p) :=
  ⟨inferInstanceAs (IsFunction (definableGraph _ _ _)), domain_definableGraph _ _ _⟩

theorem woodinSparseEndpointThread_value {Ω p i : V} (hi : i ∈ succ Ω) :
    (woodinSparseEndpointThread Ω p) ‘ i = ((forcingCodeπ (woodinSparseStageCode Ω)) ‘ ⟨i,Ω⟩ₖ) ‘ p :=
  value_definableGraph _ _ _ hi

variable {Ω p : V}
local notation "c" => woodinSparseStageCode Ω
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
include hΩ hAC

theorem woodinSparseEndpointThread_self (hp : p ∈ (forcingCodeP c) ‘ Ω) :
    (woodinSparseEndpointThread Ω p) ‘ Ω = p := by
  rw [woodinSparseEndpointThread_value (mem_succ_self Ω)]
  exact (woodinSparseStageCode_endpoint_valid hΩ hAC).system.split.projId (mem_succ_self Ω) hp

theorem woodinSparseEndpointThread_mem (hp : p ∈ (forcingCodeP c) ‘ Ω) {i : V} (hi : i ∈ succ Ω) :
    (woodinSparseEndpointThread Ω p) ‘ i ∈ (forcingCodeP c) ‘ i := by
  let := hΩ.inaccessible.1
  have hiΩ : i ⊆ Ω := by
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hi
  rw [woodinSparseEndpointThread_value hi]
  exact (woodinSparseStageCode_endpoint_valid hΩ hAC).system.split.projMaps
    i hi Ω (mem_succ_self Ω) hiΩ p hp

theorem woodinSparseEndpointThread_coherent (hp : p ∈ (forcingCodeP c) ‘ Ω)
    {i j : V} (hi : i ∈ succ Ω) (hj : j ∈ succ Ω) (hij : i ⊆ j) :
    ((forcingCodeπ c) ‘ ⟨i,j⟩ₖ) ‘ ((woodinSparseEndpointThread Ω p) ‘ j) =
      (woodinSparseEndpointThread Ω p) ‘ i := by
  let := hΩ.inaccessible.1
  have hjΩ : j ⊆ Ω := by
    rcases mem_succ_iff.mp hj with rfl | hj
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hj
  rw [woodinSparseEndpointThread_value hi, woodinSparseEndpointThread_value hj]
  exact (woodinSparseStageCode_endpoint_valid hΩ hAC).system.split.projComp
    i hi j hj Ω (mem_succ_self Ω) hij hjΩ p hp

theorem woodinSparseEndpointThread_local_mem (hp : p ∈ (forcingCodeP c) ‘ Ω)
    {θ : V} [IsOrdinal θ] (hθ : θ ⊆ Ω) :
    (woodinSparseEndpointThread Ω p) ‘ θ ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ := by
  let := hΩ.inaccessible.1
  have hθ' : θ ∈ succ Ω := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hθ)
  rw [(woodinSparseStageCode_endpoint_row_values hΩ hAC hθ).1]
  exact woodinSparseEndpointThread_mem hΩ hAC hp hθ'

theorem woodinSparseEndpointThread_local_restrict (hp : p ∈ (forcingCodeP c) ‘ Ω)
    {θ i : V} [IsOrdinal θ] (hθ : θ ⊆ Ω) (hi : i ∈ θ) :
    (woodinSparseEndpointThread Ω p) ‘ i =
      ((woodinSparseEndpointThread Ω p) ‘ θ) ↾ (succ (woodinSourceIndex i)) := by
  let := hΩ.inaccessible.1
  have hθ' : θ ∈ succ Ω := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hθ)
  have hi' : i ∈ succ Ω := IsOrdinal.toIsTransitive.mem_trans hi hθ'
  have hh := woodinSparseEndpointThread_coherent hΩ hAC hp hi' hθ' (IsOrdinal.toIsTransitive.transitive _ hi)
  have hs := woodinSparseStageCode_valid hΩ hAC hθ
  have hc := woodinSparseStageCode_endpoint_valid hΩ hAC
  have he := woodinSparseStageCode_extends_endpoint hΩ hAC hθ
  rw [← hs.tableπ.value_of_subset hc.tableπ he.subπ
    (kpair_mem_iff.mpr ⟨mem_succ_iff.mpr (Or.inr hi),mem_succ_self θ⟩),
    woodinSparseStageCode_projection hΩ hAC hθ hi (woodinSparseEndpointThread_local_mem hΩ hAC hp hθ)] at hh
  exact hh.symm

theorem woodinSparseEndpointThread_order_below {q i j : V}
    (hp : p ∈ (forcingCodeP c) ‘ Ω) (hq : q ∈ (forcingCodeP c) ‘ Ω)
    (hi : i ∈ succ Ω) (hj : j ∈ succ Ω) (hij : i ⊆ j)
    (hpq : ⟨(woodinSparseEndpointThread Ω p) ‘ j,(woodinSparseEndpointThread Ω q) ‘ j⟩ₖ
      ∈ (forcingCodeR c) ‘ j) :
    ⟨(woodinSparseEndpointThread Ω p) ‘ i,(woodinSparseEndpointThread Ω q) ‘ i⟩ₖ
      ∈ (forcingCodeR c) ‘ i := by
  have hh := (woodinSparseStageCode_endpoint_valid hΩ hAC).system.order.projMono i hi j hj hij
    _ (woodinSparseEndpointThread_mem hΩ hAC hp hj) _ (woodinSparseEndpointThread_mem hΩ hAC hq hj) hpq
  rwa [woodinSparseEndpointThread_coherent hΩ hAC hp hi hj hij,
    woodinSparseEndpointThread_coherent hΩ hAC hq hi hj hij] at hh

end ZFVP
