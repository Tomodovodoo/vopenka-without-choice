import ZFVP.SetTheory.ForcingSectionThread
import ZFVP.SetTheory.ForcingThreadMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingSectionThread_parameter_definable (θ π E k : V) :
    ℒₛₑₜ-function₁[V] (fun p ↦ forcingSectionThread θ π E k p) := by
  classical
  have h : ℒₛₑₜ-relation (fun f p : V ↦ ∀ z, z ∈ f ↔ ∃ i ∈ θ,
    (i ∈ k ∧ z = ⟨i, (π ‘ ⟨i, k⟩ₖ) ‘ p⟩ₖ) ∨
    (i ∉ k ∧ z = ⟨i, (E ‘ ⟨k, i⟩ₖ) ‘ p⟩ₖ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingSectionThread θ π E k (v 1) ↔ _
  rw [mem_ext_iff]
  apply forall_congr'
  intro z
  rw [forcingSectionThread, mem_definableGraph_iff]
  apply iff_congr Iff.rfl
  apply exists_congr
  intro i
  by_cases hi : i ∈ k <;> simp [forcingSectionValue, hi]

noncomputable def forcingThreadSection (θ P π E k : V) : V :=
  definableGraph (P ‘ k) (fun p ↦ forcingSectionThread θ π E k p)
    (forcingSectionThread_parameter_definable θ π E k)

theorem forcingThreadSection_value {θ P π E k p : V} (hp : p ∈ P ‘ k) :
    (forcingThreadSection θ P π E k) ‘ p = forcingSectionThread θ π E k p :=
  value_definableGraph _ _ _ hp

theorem forcingThreadSection_maps {θ P π E U k : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hU : ∀ i ∈ θ, P ‘ i ⊆ U) :
    forcingThreadSection θ P π E k ∈ forcingDirectLimit θ P π E U ^ (P ‘ k) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hp ↦ forcingSectionThread_mem h hk hp hU)

theorem forcingThreadSection_retraction {θ P π E U k p : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hp : p ∈ P ‘ k)
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U) :
    (forcingThreadCoordinate (forcingDirectLimit θ P π E U) k) ‘
      ((forcingThreadSection θ P π E k) ‘ p) = p := by
  rw [forcingThreadSection_value hp,
    forcingThreadCoordinate_value (forcingSectionThread_mem h hk hp hU),
    forcingSectionThread_value hk, forcingSectionValue_self h hk hp]

theorem forcingThread_eq_of_support {θ P π E U f g k : V} [IsOrdinal θ]
    (hf : f ∈ forcingInverseLimit θ P π U) (hg : g ∈ forcingInverseLimit θ P π U)
    (hfk : IsThreadSupport θ E f k) (hgk : IsThreadSupport θ E g k)
    (he : f ‘ k = g ‘ k) : f = g := by
  have hf' := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hf
  have hg' := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hg
  let := IsFunction.of_mem hf'.1
  let := IsFunction.of_mem hg'.1
  let := IsOrdinal.of_mem hfk.1
  have hv : ∀ i ∈ θ, f ‘ i = g ‘ i := by
    intro i hi
    let := IsOrdinal.of_mem hi
    rcases IsOrdinal.mem_trichotomy i k with hik | rfl | hki
    · rw [← hf'.2.2 k hfk.1 i hik hi, ← hg'.2.2 k hfk.1 i hik hi, he]
    · exact he
    · have hki' : k ⊆ i := IsOrdinal.toIsTransitive.transitive _ hki
      rw [hfk.2 i hi hki', hgk.2 i hi hki', he]
  apply function_ext hf'.1 hg'.1
  intro i hi y _hy hiy
  have hy : y = g ‘ i := (value_eq_of_kpair_mem hiy).symm.trans (hv i hi)
  rw [hy]
  exact kpair_value_mem ((domain_eq_of_mem_function hg'.1).symm ▸ hi)

theorem forcingSectionThread_comp {θ P π E U k l p : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hl : l ∈ θ) (hkl : k ⊆ l)
    (hp : p ∈ P ‘ k) (hU : ∀ i ∈ θ, P ‘ i ⊆ U) :
    forcingSectionThread θ π E l ((E ‘ ⟨k, l⟩ₖ) ‘ p) = forcingSectionThread θ π E k p := by
  have hq := h.secMaps k hk l hl hkl p hp
  have hf := forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem h hk hp hU)
  have hg := forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem h hl hq hU)
  have hs := forcingSectionThread_support h hk hp
  have hsl := hs.raise ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 hl hkl
    (fun j hj hlj q hq ↦ h.secComp k hk l hl j hj hkl hlj q hq)
  apply forcingThread_eq_of_support hg hf (forcingSectionThread_support h hl hq) hsl
  rw [hs.2 l hl hkl, forcingSectionThread_value hl, forcingSectionValue_self h hl hq,
    forcingSectionThread_value hk, forcingSectionValue_self h hk hp]

theorem forcingThreadSection_monotone {θ P R π E U k p q : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hp : p ∈ P ‘ k) (hq : q ∈ P ‘ k) (hpq : ⟨p, q⟩ₖ ∈ R ‘ k)
    (hπ : ∀ i ∈ k, ∀ a ∈ P ‘ k, ∀ b ∈ P ‘ k, ⟨a, b⟩ₖ ∈ R ‘ k →
      ⟨(π ‘ ⟨i, k⟩ₖ) ‘ a, (π ‘ ⟨i, k⟩ₖ) ‘ b⟩ₖ ∈ R ‘ i)
    (hE : ∀ i ∈ θ, k ⊆ i → ∀ a ∈ P ‘ k, ∀ b ∈ P ‘ k, ⟨a, b⟩ₖ ∈ R ‘ k →
      ⟨(E ‘ ⟨k, i⟩ₖ) ‘ a, (E ‘ ⟨k, i⟩ₖ) ‘ b⟩ₖ ∈ R ‘ i) :
    ⟨(forcingThreadSection θ P π E k) ‘ p, (forcingThreadSection θ P π E k) ‘ q⟩ₖ ∈
      forcingThreadOrder θ R (forcingDirectLimit θ P π E U) := by
  rw [forcingThreadSection_value hp, forcingThreadSection_value hq]
  apply forcingThreadOrder_of_support
    (forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem h hk hp hU))
    (forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem h hk hq hU))
    (forcingSectionThread_support h hk hp) (forcingSectionThread_support h hk hq) hπ hE
  rwa [forcingSectionThread_value hk, forcingSectionThread_value hk,
    forcingSectionValue_self h hk hp, forcingSectionValue_self h hk hq]

end ZFVP
