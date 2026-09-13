import ZFVP.SetTheory.CohenAutomorphisms
import ZFVP.SetTheory.InternalTranspositions

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem cohen_transposition_compatible {I p i j : V} (hp : p ∈ cohenConditions I)
    (hi : i ∈ I) (hj : j ∈ I) (hfresh : j ∉ cohenSupport p) :
    ForcingCompatible (cohenConditions I) (cohenOrder I) p
      (cohenConditionAction I (internalTransposition I i j) p) := by
  have hπ := internalTransposition_permutation hi hj
  have hq := cohenConditionAction_condition hπ hp
  have : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp hp).2.1
  apply (finitePartialFunctions_compatible_iff hp hq).mpr
  intro x y z hxy hxz
  obtain ⟨k, hk, n, hn, rfl⟩ := mem_prod_iff.mp (finitePartialFunction_domain hp _ (mem_domain_of_kpair_mem hxy))
  obtain ⟨l, hlz, hkl⟩ := (cohenConditionAction_pair_iff hp).mp hxz
  have hl : l ∈ I := (kpair_mem_iff.mp (finitePartialFunction_domain hp _ (mem_domain_of_kpair_mem hlz))).1
  have hlj : l ≠ j := fun he ↦ hfresh (he ▸ (mem_cohenSupport p l).mpr ⟨n, z, hlz⟩)
  have hkj : k ≠ j := fun he ↦ hfresh (he ▸ (mem_cohenSupport p k).mpr ⟨n, y, hxy⟩)
  have hli : l ≠ i := by
    intro he
    rw [he, internalTransposition_left hi] at hkl
    exact hkj hkl
  rw [internalTransposition_fixed hl hli hlj] at hkl
  subst k
  exact IsFunction.unique hxy hlz

theorem cohen_transposition_fix {I p i j : V} (hp : p ∈ cohenConditions I)
    (hi : i ∉ cohenSupport p) (hj : j ∉ cohenSupport p) :
    (cohenPermutation I (internalTransposition I i j)) ‘ p = p := by
  rw [cohenPermutation_value hp]
  apply cohenConditionAction_fix hp
  intro k hk
  exact internalTransposition_fixed (cohenSupport_subset hp k hk)
    (fun he ↦ hi (he ▸ hk)) (fun he ↦ hj (he ▸ hk))

end ZFVP
