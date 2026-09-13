import ZFVP.SetTheory.ForcingIterationCongruence
import ZFVP.SetTheory.IterationTableUnion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Assemble internal stage tables from compatible successor prefixes. -/
theorem forcingIterationSystem_union {θ : V} [IsOrdinal θ]
    {P R π E L t : V → V}
    (dP : ℒₛₑₜ-function₁ P)
    (dR : ℒₛₑₜ-function₁ R)
    (dπ : ℒₛₑₜ-function₁ π)
    (dE : ℒₛₑₜ-function₁ E)
    (dL : ℒₛₑₜ-function₁ L)
    (dt : ℒₛₑₜ-function₁ t)
    (hP : ∀ i ∈ θ, IsIterationTable (succ i) (P i))
    (hR : ∀ i ∈ θ, IsIterationTable (succ i) (R i))
    (hπ : ∀ i ∈ θ, IsIterationTable (succ i ×ˢ succ i) (π i))
    (hE : ∀ i ∈ θ, IsIterationTable (succ i ×ˢ succ i) (E i))
    (hL : ∀ i ∈ θ, IsIterationTable (succ i ×ˢ succ i) (L i))
    (ht : ∀ i ∈ θ, IsIterationTable (succ i) (t i))
    (cP : ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ, P i ⊆ P k ∧ P j ⊆ P k)
    (cR : ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ, R i ⊆ R k ∧ R j ⊆ R k)
    (cπ : ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ, π i ⊆ π k ∧ π j ⊆ π k)
    (cE : ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ, E i ⊆ E k ∧ E j ⊆ E k)
    (cL : ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ, L i ⊆ L k ∧ L j ⊆ L k)
    (ct : ∀ i ∈ θ, ∀ j ∈ θ, ∃ k ∈ θ, t i ⊆ t k ∧ t j ⊆ t k)
    (hs : ∀ i ∈ θ, IsForcingIterationSystem (succ i) (P i) (R i) (π i) (E i) (L i) (t i)) :
    IsForcingIterationSystem θ
      (iterationTableUnion θ P dP) (iterationTableUnion θ R dR)
      (iterationTableUnion θ π dπ) (iterationTableUnion θ E dE)
      (iterationTableUnion θ L dL) (iterationTableUnion θ t dt) := by
  apply IsForcingIterationSystem.of_prefixes
  intro k hk
  apply (hs k hk).congr
  · intro i hi
    exact (iterationTableUnion_value dP (fun j hj ↦ (hP j hj).function) cP hk
      ((hP k hk).domain_eq.symm ▸ hi)).symm
  · intro i hi
    exact (iterationTableUnion_value dR (fun j hj ↦ (hR j hj).function) cR hk
      ((hR k hk).domain_eq.symm ▸ hi)).symm
  · intro i hi j hj
    exact (iterationTableUnion_value dπ (fun j hj ↦ (hπ j hj).function) cπ hk
      ((hπ k hk).domain_eq.symm ▸ (kpair_mem_iff.mpr ⟨hi, hj⟩))).symm
  · intro i hi j hj
    exact (iterationTableUnion_value dE (fun j hj ↦ (hE j hj).function) cE hk
      ((hE k hk).domain_eq.symm ▸ (kpair_mem_iff.mpr ⟨hi, hj⟩))).symm
  · intro i hi j hj
    exact (iterationTableUnion_value dL (fun j hj ↦ (hL j hj).function) cL hk
      ((hL k hk).domain_eq.symm ▸ (kpair_mem_iff.mpr ⟨hi, hj⟩))).symm
  · intro i hi
    exact (iterationTableUnion_value dt (fun j hj ↦ (ht j hj).function) ct hk
      ((ht k hk).domain_eq.symm ▸ hi)).symm

end ZFVP
