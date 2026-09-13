import ZFVP.ModelTheory.ForcingRecodedSystem
import ZFVP.ModelTheory.ForcingThreadIsomorphism

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s Q T m U W : V} [IsOrdinal θ]
variable (hs : IsForcingIterationCode θ s)
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
  (Q ‘ i) (T ‘ i) (m ‘ i))
local notation "P" => forcingCodeP s
local notation "R" => forcingCodeR s
local notation "π" => forcingCodeπ s
local notation "E" => forcingCodeE s
local notation "ρ" => forcingRecodedProjections θ s m
local notation "F" => forcingRecodedSections θ s m
local notation "back" => forcingInverseMapFamily θ m

include hs hm

theorem forcingRecodedThread_mem_inverse
    (hQ : ∀ i ∈ θ, Q ‘ i ⊆ W) {f : V} (hf : f ∈ forcingInverseLimit θ P π U) :
    forcingThreadAction θ m f ∈ forcingInverseLimit θ Q ρ W := by
  apply forcingThreadAction_mem_inverse (fun i hi ↦ (hm i hi).1) hQ ?_ hf
  intro j hj i hij hi p hp
  let := IsOrdinal.of_mem hj
  exact forcingRecodedProjections_image hs hm hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hp

theorem forcingRecodedThread_inverse_mem
    (hP : ∀ i ∈ θ, P ‘ i ⊆ U) {f : V} (hf : f ∈ forcingInverseLimit θ Q ρ W) :
    forcingThreadAction θ back f ∈ forcingInverseLimit θ P π U := by
  apply forcingThreadAction_mem_inverse ?_ hP ?_ hf
  · intro i hi
    rw [forcingInverseMapFamily_value hi]
    exact (hm i hi).inverse_maps
  · intro j hj i hij hi p hp
    let := IsOrdinal.of_mem hj
    rw [forcingInverseMapFamily_value hj, forcingInverseMapFamily_value hi]
    exact (forcingRecodedProjections_inverse hs hm hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hp).symm

theorem forcingRecodedThread_mem_direct
    (hQ : ∀ i ∈ θ, Q ‘ i ⊆ W) {f : V} (hf : f ∈ forcingDirectLimit θ P π E U) :
    forcingThreadAction θ m f ∈ forcingDirectLimit θ Q ρ F W := by
  obtain ⟨hf, k, hk⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hf
  refine (mem_forcingDirectLimit_iff _ _ _ _ _ _).mpr
    ⟨forcingRecodedThread_mem_inverse hs hm hQ hf, k, ?_⟩
  apply forcingThreadAction_support ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 ?_ hk
  intro i hi j hj hij p hp
  exact (forcingRecodedSections_image hs hm hi hj hij hp).symm

theorem forcingRecodedThread_direct_inverse_mem
    (hP : ∀ i ∈ θ, P ‘ i ⊆ U) {f : V} (hf : f ∈ forcingDirectLimit θ Q ρ F W) :
    forcingThreadAction θ back f ∈ forcingDirectLimit θ P π E U := by
  obtain ⟨hf, k, hk⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hf
  refine (mem_forcingDirectLimit_iff _ _ _ _ _ _).mpr
    ⟨forcingRecodedThread_inverse_mem hs hm hP hf, k, ?_⟩
  apply forcingThreadAction_support ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 ?_ hk
  intro i hi j hj hij p hp
  rw [forcingInverseMapFamily_value hi, forcingInverseMapFamily_value hj]
  exact forcingRecodedSections_inverse hs hm hi hj hij hp

omit [IsOrdinal θ] in
theorem forcingRecodedThread_support_iff {f k : V}
    (hf : f ∈ forcingInverseLimit θ P π U) :
    IsThreadSupport θ F (forcingThreadAction θ m f) k ↔ IsThreadSupport θ E f k := by
  obtain ⟨hfun, hv, _⟩ := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hf
  apply forcingThreadAction_support_iff (n := back) hfun hv (fun i hi ↦ (hm i hi).1)
  · intro i hi p hp
    rw [forcingInverseMapFamily_value hi, (hm i hi).inverse_value hp]
  · intro i hi j hj hij p hp
    exact (forcingRecodedSections_image hs hm hi hj hij hp).symm
  · intro i hi j hj hij p hp
    rw [forcingInverseMapFamily_value hi, forcingInverseMapFamily_value hj]
    exact forcingRecodedSections_inverse hs hm hi hj hij hp

theorem forcingRecoded_inverseLimit_isomorphism
    (hP : ∀ i ∈ θ, P ‘ i ⊆ U) (hQ : ∀ i ∈ θ, Q ‘ i ⊆ W) :
    IsForcingIsomorphism (forcingInverseLimit θ P π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ P π U))
      (forcingInverseLimit θ Q ρ W) (forcingThreadOrder θ T (forcingInverseLimit θ Q ρ W))
      (forcingThreadActionMap θ m (forcingInverseLimit θ P π U)) := by
  apply forcingThreadActionMap_isomorphism hm
  · intro f hf
    have hh := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hf
    exact ⟨hh.1, hh.2.1⟩
  · intro f hf
    have hh := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hf
    exact ⟨hh.1, hh.2.1⟩
  · exact fun _ hf ↦ forcingRecodedThread_mem_inverse hs hm hQ hf
  · exact fun _ hf ↦ forcingRecodedThread_inverse_mem hs hm hP hf

theorem forcingRecoded_directLimit_isomorphism
    (hP : ∀ i ∈ θ, P ‘ i ⊆ U) (hQ : ∀ i ∈ θ, Q ‘ i ⊆ W) :
    IsForcingIsomorphism (forcingDirectLimit θ P π E U)
      (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))
      (forcingDirectLimit θ Q ρ F W) (forcingThreadOrder θ T (forcingDirectLimit θ Q ρ F W))
      (forcingThreadActionMap θ m (forcingDirectLimit θ P π E U)) := by
  apply forcingThreadActionMap_isomorphism hm
  · intro f hf
    have hh := (mem_forcingInverseLimit_iff _ _ _ _ _).mp (forcingDirectLimit_subset _ _ _ _ _ _ hf)
    exact ⟨hh.1, hh.2.1⟩
  · intro f hf
    have hh := (mem_forcingInverseLimit_iff _ _ _ _ _).mp (forcingDirectLimit_subset _ _ _ _ _ _ hf)
    exact ⟨hh.1, hh.2.1⟩
  · exact fun _ hf ↦ forcingRecodedThread_mem_direct hs hm hQ hf
  · exact fun _ hf ↦ forcingRecodedThread_direct_inverse_mem hs hm hP hf

end ZFVP
