import ZFVP.ModelTheory.ProjectionQuotient
import ZFVP.SetTheory.DirectLimitClosure
import ZFVP.SetTheory.FunctionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- Even a new intermediate sequence of ground direct-limit conditions has a
common ground support, provided its length is below the intermediate cofinality
of the ground iteration length. -/
theorem check_directLimit_common_support (A : ForcingContext V)
    {θ P π E U : V} [IsOrdinal θ] {α f : A.Model}
    (h : IsSplitForcingSystem θ P π E)
    (hα : α ∈ internalCofinality (A.check θ))
    (hf : ∀ i ∈ α, f ‘ i ∈ A.check (forcingDirectLimit θ P π E U)) :
    ∃ k ∈ θ, ∀ i ∈ α, ∃ q ∈ forcingDirectLimit θ P π E U,
      f ‘ i = A.check q ∧ IsThreadSupport θ E q k := by
  let L : V → V := leastOrdinalOrZero (fun q k ↦ IsThreadSupport θ E q k) (by definability)
  have hL (q : V) (hq : q ∈ forcingDirectLimit θ P π E U) :
      IsThreadSupport θ E q (L q) := by
    obtain ⟨_, k, hk⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hq
    exact (leastOrdinalOrZero_spec _ _ _ ⟨k, IsOrdinal.of_mem hk.1, hk⟩).2.1
  let s := definableGraph (forcingDirectLimit θ P π E U) L (by definability)
  have hs : s ∈ θ ^ forcingDirectLimit θ P π E U :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun q hq ↦ (hL q hq).1)
  let := IsFunction.of_mem hs
  have hcs := (A.check_function_iff _ _ _).mpr hs
  let b := definableGraph α (fun i ↦ (A.check s) ‘ (f ‘ i)) (by definability)
  have hb : b ∈ (A.check θ) ^ α :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦ function_value_mem hcs (hf i hi))
  obtain ⟨k', hk', hbound⟩ := function_bounded_below_cofinality hα hb
  obtain ⟨k, hk, rfl⟩ := (A.mem_check_iff θ k').mp hk'
  refine ⟨k, hk, ?_⟩
  intro i hi
  obtain ⟨q, hq, he⟩ := (A.mem_check_iff _ (f ‘ i)).mp (hf i hi)
  have hLk : L q ∈ k := by
    have hh := hbound i hi
    rw [value_definableGraph _ _ _ hi, he,
      A.check_value ((domain_eq_of_mem_function hs).symm ▸ hq),
      value_definableGraph _ _ _ hq, A.check_mem_iff] at hh
    exact hh
  let := IsOrdinal.of_mem hk
  have hcoord := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp
    (forcingDirectLimit_subset _ _ _ _ _ _ hq)).2.1
  refine ⟨q, hq, he, (hL q hq).raise hcoord hk
    (IsOrdinal.toIsTransitive.transitive _ hLk) ?_⟩
  intro j hj hkj p hp
  exact h.secComp _ (hL q hq).1 k hk j hj
    (IsOrdinal.toIsTransitive.transitive _ hLk) hkj p hp

theorem check_directLimit_cofinal_common_support (A : ForcingContext V)
    {θ P π E U k₀ : V} [IsOrdinal θ] {α f : A.Model}
    (h : IsSplitForcingSystem θ P π E) (hk₀ : k₀ ∈ θ)
    (hα : α ∈ internalCofinality (A.check θ))
    (hf : ∀ i ∈ α, f ‘ i ∈ A.check (forcingDirectLimit θ P π E U)) :
    ∃ k ∈ θ, k₀ ⊆ k ∧ ∀ i ∈ α, ∃ q ∈ forcingDirectLimit θ P π E U,
      f ‘ i = A.check q ∧ IsThreadSupport θ E q k := by
  obtain ⟨k, hk, hs⟩ := A.check_directLimit_common_support h hα hf
  let := IsOrdinal.of_mem hk
  let := IsOrdinal.of_mem hk₀
  rcases IsOrdinal.subset_or_supset k₀ k with h₀k | hk₀'
  · exact ⟨k, hk, h₀k, hs⟩
  · refine ⟨k₀, hk₀, fun _ hx ↦ hx, ?_⟩
    intro i hi
    obtain ⟨q, hq, he, hqk⟩ := hs i hi
    refine ⟨q, hq, he, hqk.raise
      ((mem_forcingInverseLimit_iff _ _ _ _ _).mp
        (forcingDirectLimit_subset _ _ _ _ _ _ hq)).2.1 hk₀ hk₀' ?_⟩
    intro j hj h₀j p hp
    exact h.secComp k hk k₀ hk₀ j hj hk₀' h₀j p hp

end ForcingContext
end ZFVP
