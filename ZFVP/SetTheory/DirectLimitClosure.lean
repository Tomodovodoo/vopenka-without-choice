import ZFVP.SetTheory.ForcingSectionThread
import ZFVP.SetTheory.ForcingClosure
import ZFVP.SetTheory.LeastOrdinalChoice
import ZFVP.SetTheory.Cofinality

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem function_bounded_below_cofinality {θ α f : V} [IsOrdinal θ]
    (hα : α ∈ internalCofinality θ) (hf : f ∈ θ ^ α) :
    ∃ k ∈ θ, ∀ i ∈ α, f ‘ i ∈ k := by
  classical
  have hn : ¬∀ k ∈ θ, ∃ i ∈ α, k ⊆ f ‘ i :=
    fun h ↦ no_cofinalMap_below_cofinality hα ⟨f, hf, h⟩
  push Not at hn
  obtain ⟨k, hk, hki⟩ := hn
  refine ⟨k, hk, fun i hi ↦ ?_⟩
  let := IsOrdinal.of_mem hk
  let := IsOrdinal.of_mem (function_value_mem hf hi)
  exact IsOrdinal.mem_iff_subset_and_not_subset.mpr
    ⟨(IsOrdinal.subset_or_supset (f ‘ i) k).resolve_right (hki i hi), hki i hi⟩

theorem forcingDirectLimit_common_support {θ P π E U α f : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hα : α ∈ internalCofinality θ)
    (hf : f ∈ (forcingDirectLimit θ P π E U) ^ α) :
    ∃ k ∈ θ, ∀ i ∈ α, IsThreadSupport θ E (f ‘ i) k := by
  let L : V → V := leastOrdinalOrZero (fun g k ↦ IsThreadSupport θ E g k) (by definability)
  have hL (i : V) (hi : i ∈ α) : IsThreadSupport θ E (f ‘ i) (L (f ‘ i)) := by
    obtain ⟨_, k, hk⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp (function_value_mem hf hi)
    exact (leastOrdinalOrZero_spec _ _ _ ⟨k, IsOrdinal.of_mem hk.1, hk⟩).2.1
  let b := definableGraph α (fun i ↦ L (f ‘ i)) (by definability)
  have hb : b ∈ θ ^ α := definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦ (hL i hi).1)
  obtain ⟨k, hk, hbound⟩ := function_bounded_below_cofinality hα hb
  refine ⟨k, hk, fun i hi ↦ ?_⟩
  have hLik : L (f ‘ i) ∈ k := by
    simpa only [b, value_definableGraph _ _ _ hi] using hbound i hi
  let := IsOrdinal.of_mem hk
  have hsub : L (f ‘ i) ⊆ k := IsOrdinal.toIsTransitive.transitive _ hLik
  have hfi := forcingDirectLimit_subset _ _ _ _ _ _ (function_value_mem hf hi)
  have hcoord := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hfi).2.1
  exact (hL i hi).raise hcoord hk hsub (fun j hj hkj p hp ↦
    h.secComp _ (hL i hi).1 k hk j hj hsub hkj p hp)

theorem forcingDirectLimit_closedAt {θ P R π E U α : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hα : α ∈ internalCofinality θ)
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hclosed : ∀ k ∈ θ, IsForcingClosedAt (P ‘ k) (R ‘ k) α)
    (hπ : ∀ i ∈ θ, ∀ k ∈ θ, i ∈ k → ∀ p ∈ P ‘ k, ∀ q ∈ P ‘ k,
      ⟨p, q⟩ₖ ∈ R ‘ k → ⟨(π ‘ ⟨i, k⟩ₖ) ‘ p, (π ‘ ⟨i, k⟩ₖ) ‘ q⟩ₖ ∈ R ‘ i)
    (hE : ∀ k ∈ θ, ∀ i ∈ θ, k ⊆ i → ∀ p ∈ P ‘ k, ∀ q ∈ P ‘ k,
      ⟨p, q⟩ₖ ∈ R ‘ k → ⟨(E ‘ ⟨k, i⟩ₖ) ‘ p, (E ‘ ⟨k, i⟩ₖ) ‘ q⟩ₖ ∈ R ‘ i) :
    IsForcingClosedAt (forcingDirectLimit θ P π E U)
      (forcingThreadOrder θ R (forcingDirectLimit θ P π E U)) α := by
  intro f hf
  obtain ⟨k, hk, hsupport⟩ := forcingDirectLimit_common_support h hα hf.1
  have hfi (i : V) (hi : i ∈ α) := forcingDirectLimit_subset _ _ _ _ _ _ (function_value_mem hf.1 hi)
  have hcoord (i : V) (hi : i ∈ α) : (f ‘ i) ‘ k ∈ P ‘ k :=
    ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hfi i hi)).2.1 k hk
  let b := definableGraph α (fun i ↦ (f ‘ i) ‘ k) (by definability)
  have hb (i : V) (hi : i ∈ α) : b ‘ i = (f ‘ i) ‘ k := value_definableGraph _ _ _ hi
  let := IsOrdinal.of_mem hα
  have hbdesc : IsForcingDescending (P ‘ k) (R ‘ k) α b := by
    refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ hcoord, ?_⟩
    intro i hi j hj
    rw [hb i hi, hb j (IsOrdinal.toIsTransitive.mem_trans hj hi)]
    exact ((mem_forcingThreadOrder_iff _ _ _ _ _).mp (hf.2 i hi j hj)).2.2 k hk
  obtain ⟨p, hp, hpbound⟩ := hclosed k hk b hbdesc
  have hpD := forcingSectionThread_mem h hk hp hU
  refine ⟨forcingSectionThread θ π E k p, hpD, fun i hi ↦ ?_⟩
  apply forcingThreadOrder_of_support (forcingDirectLimit_subset _ _ _ _ _ _ hpD) (hfi i hi)
    (forcingSectionThread_support h hk hp) (hsupport i hi)
    (fun j hj ↦ hπ j (IsOrdinal.toIsTransitive.mem_trans hj hk) k hk hj)
    (hE k hk)
  simpa only [forcingSectionThread_value hk, forcingSectionValue_self h hk hp, hb i hi] using hpbound i hi

end ZFVP
