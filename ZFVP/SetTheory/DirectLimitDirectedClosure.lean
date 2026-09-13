import ZFVP.SetTheory.DirectLimitClosure
import ZFVP.SetTheory.ForcingDirectedClosure

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingDirectLimit_directedClosedAt {θ P R π E U α : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hα : α ∈ internalCofinality θ)
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hclosed : ∀ k ∈ θ, IsForcingDirectedClosedAt (P ‘ k) (R ‘ k) α)
    (hπ : ∀ i ∈ θ, ∀ k ∈ θ, i ∈ k → ∀ p ∈ P ‘ k, ∀ q ∈ P ‘ k,
      ⟨p, q⟩ₖ ∈ R ‘ k → ⟨(π ‘ ⟨i, k⟩ₖ) ‘ p, (π ‘ ⟨i, k⟩ₖ) ‘ q⟩ₖ ∈ R ‘ i)
    (hE : ∀ k ∈ θ, ∀ i ∈ θ, k ⊆ i → ∀ p ∈ P ‘ k, ∀ q ∈ P ‘ k,
      ⟨p, q⟩ₖ ∈ R ‘ k → ⟨(E ‘ ⟨k, i⟩ₖ) ‘ p, (E ‘ ⟨k, i⟩ₖ) ‘ q⟩ₖ ∈ R ‘ i) :
    IsForcingDirectedClosedAt (forcingDirectLimit θ P π E U)
      (forcingThreadOrder θ R (forcingDirectLimit θ P π E U)) α := by
  intro f hf
  obtain ⟨k, hk, hsupport⟩ := forcingDirectLimit_common_support h hα hf.1
  have hfi (i : V) (hi : i ∈ α) := forcingDirectLimit_subset _ _ _ _ _ _ (function_value_mem hf.1 hi)
  have hcoord (i : V) (hi : i ∈ α) : (f ‘ i) ‘ k ∈ P ‘ k :=
    ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hfi i hi)).2.1 k hk
  let b := definableGraph α (fun i ↦ (f ‘ i) ‘ k) (by definability)
  have hb (i : V) (hi : i ∈ α) : b ‘ i = (f ‘ i) ‘ k := value_definableGraph _ _ _ hi
  have hbdir : IsForcingDirectedFamily (P ‘ k) (R ‘ k) α b := by
    refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ hcoord, ?_⟩
    intro i hi j hj
    obtain ⟨l, hl, hli, hlj⟩ := hf.2 i hi j hj
    refine ⟨l, hl, ?_, ?_⟩
    · rw [hb l hl, hb i hi]
      exact ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hli).2.2 k hk
    · rw [hb l hl, hb j hj]
      exact ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hlj).2.2 k hk
  obtain ⟨p, hp, hpbound⟩ := hclosed k hk b hbdir
  have hpD := forcingSectionThread_mem h hk hp hU
  refine ⟨forcingSectionThread θ π E k p, hpD, fun i hi ↦ ?_⟩
  apply forcingThreadOrder_of_support (forcingDirectLimit_subset _ _ _ _ _ _ hpD) (hfi i hi)
    (forcingSectionThread_support h hk hp) (hsupport i hi)
    (fun j hj ↦ hπ j (IsOrdinal.toIsTransitive.mem_trans hj hk) k hk hj)
    (hE k hk)
  simpa only [forcingSectionThread_value hk, forcingSectionValue_self h hk hp, hb i hi] using hpbound i hi

end ZFVP
