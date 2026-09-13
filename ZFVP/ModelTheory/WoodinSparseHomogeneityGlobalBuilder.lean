import ZFVP.ModelTheory.WoodinSparseHomogeneityInitialRow
import ZFVP.ModelTheory.WoodinSparseHomogeneitySuccessorRow
import ZFVP.ModelTheory.WoodinSparseHomogeneityDirectRow
import ZFVP.ModelTheory.WoodinSparseHomogeneityInverseRow
import ZFVP.ModelTheory.WoodinSparseEndpointThread

set_option maxHeartbeats 1000000

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω δ p q : V} [IsOrdinal δ]
local notation "c" => woodinSparseStageCode Ω
local notation "a" => woodinSparseEndpointThread Ω p
local notation "b" => woodinSparseEndpointThread Ω q

theorem woodinSparseHomogeneityRow_spec
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hδ : δ ⊆ Ω)
    (hp : p ∈ (forcingCodeP c) ‘ Ω) (hq : q ∈ (forcingCodeP c) ‘ Ω)
    (hle : ⟨a ‘ δ,b ‘ δ⟩ₖ ∈ (forcingCodeR c) ‘ δ) :
    ∀ θ ∈ succ Ω, ∀ H W, IsCoherentAutomorphismWitnessHistory θ c a b δ H W →
      IsCoherentAutomorphismWitnessRow θ c a b δ H W (woodinSparseHomogeneityRow δ a b θ H W) := by
  classical
  let := hΩ.inaccessible.1
  have hδ' : δ ∈ succ Ω := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hδ)
  intro θ hθ' H W hh
  let := IsOrdinal.of_mem hθ'
  have hθ : θ ⊆ Ω := by
    rcases mem_succ_iff.mp hθ' with rfl | hθ'
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hθ'
  have hpa := woodinSparseEndpointThread_local_mem hΩ hAC hp hθ
  have hqb := woodinSparseEndpointThread_local_mem hΩ hAC hq hθ
  have hprefix := hh.woodin_prefix hΩ hAC hθ
  by_cases hinit : θ ⊆ δ
  · rw [woodinSparseHomogeneityRow, ite_eq_left hinit]
    exact woodinSparseHomogeneityInitialRow_spec (woodinSparseStageCode_endpoint_valid hΩ hAC) hθ'
      hh hinit (woodinSparseStageCode_endpoint_row_values hΩ hAC hθ).1.symm
      (woodinSparseEndpointThread_mem hΩ hAC hp hθ')
      (woodinSparseEndpointThread_order_below hΩ hAC hp hq hθ' hδ' hinit hle)
      (fun i hi ↦ woodinSparseEndpointThread_coherent hΩ hAC hp
        (IsOrdinal.toIsTransitive.mem_trans hi hθ') hθ' (IsOrdinal.toIsTransitive.transitive _ hi))
  rw [woodinSparseHomogeneityRow, ite_eq_right hinit]
  by_cases hsucc : θ = succ (⋃ˢ θ)
  · rw [ite_eq_left hsucc]
    generalize hkdef : ⋃ˢ θ = k at hsucc ⊢
    subst θ
    let := IsOrdinal.of_mem (mem_succ_self k)
    have hkΩ : succ k ∈ Ω := by
      rcases IsOrdinal.subset_iff.mp hθ with he | he
      · exact ((woodinEndpoint_branch hΩ hAC).2.1 (by rw [← he, hkdef])).elim
      · exact he
    have hap : a ‘ k = (a ‘ (succ k)) ↾ (woodinSourceIndex (succ k)) := by
      simpa only [woodinSourceIndex_successor] using woodinSparseEndpointThread_local_restrict hΩ hAC hp hθ (mem_succ_self k)
    have hbp : b ‘ k = (b ‘ (succ k)) ↾ (woodinSourceIndex (succ k)) := by
      simpa only [woodinSourceIndex_successor] using woodinSparseEndpointThread_local_restrict hΩ hAC hq hθ (mem_succ_self k)
    exact (woodinSparseHomogeneitySuccessorRow_spec hΩ hAC hkΩ hprefix hinit hpa hqb hap hbp).woodin_endpoint hΩ hAC hθ
  rw [ite_eq_right hsucc]
  have h0 : θ ≠ ∅ := by
    intro he
    subst θ
    exact hinit (empty_subset δ)
  by_cases hn : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))
  · rw [ite_eq_left hn]
    exact (woodinSparseHomogeneityDirectRow_spec hΩ hAC hθ h0 hsucc hn hinit hprefix hpa hqb
      (fun i hi ↦ woodinSparseEndpointThread_local_restrict hΩ hAC hp hθ hi)
      (fun i hi ↦ woodinSparseEndpointThread_local_restrict hΩ hAC hq hθ hi)).woodin_endpoint hΩ hAC hθ
  · rw [ite_eq_right hn]
    have hθΩ : θ ∈ Ω := by
      rcases IsOrdinal.subset_iff.mp hθ with he | he
      · subst θ
        exact (hn (woodinEndpoint_branch hΩ hAC).2.2).elim
      · exact he
    exact (woodinSparseHomogeneityInverseRow_spec hΩ hAC hθΩ h0 hsucc hn hinit hprefix hpa hqb
      (fun i hi ↦ woodinSparseEndpointThread_local_restrict hΩ hAC hp hθ hi)
      (fun i hi ↦ woodinSparseEndpointThread_local_restrict hΩ hAC hq hθ hi)).woodin_endpoint hΩ hAC hθ

end ZFVP


