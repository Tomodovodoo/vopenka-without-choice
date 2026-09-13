import ZFVP.SetTheory.PartialFunctionAction
import ZFVP.SetTheory.CardinalSmallComplements

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem permutedGraph_function_of_injection {D E π p : V} [IsFunction p]
    (hπ : π ∈ E ^ D) (hinj : Injective π) (hdom : domain p ⊆ D) :
    IsFunction (permutedGraph π p) := by
  apply isFunction_iff.mpr
  apply mem_function.intro
  · intro z hz
    obtain ⟨u, _, rfl⟩ := (mem_permutedGraph π p z).mp hz
    exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hz, mem_range_of_kpair_mem hz⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
    refine ⟨y, hxy, ?_⟩
    intro z hxz
    obtain ⟨u, huy, hxu⟩ := (pair_mem_permutedGraph π p x y).mp hxy
    obtain ⟨v, hvz, hxv⟩ := (pair_mem_permutedGraph π p x z).mp hxz
    have huv := injective_value_eq hπ hinj (hdom _ (mem_domain_of_kpair_mem huy))
      (hdom _ (mem_domain_of_kpair_mem hvz)) (hxu.symm.trans hxv)
    subst v
    exact IsFunction.unique hvz huy

theorem permutedGraph_domain_cardLE {D E π p : V} [IsFunction p]
    (hπ : π ∈ E ^ D) (hinj : Injective π) (hdom : domain p ⊆ D) :
    domain (permutedGraph π p) ≤# domain p := by
  let g := definableGraph (domain p) (fun x ↦ π ‘ x) (by definability)
  have hg : g ∈ E ^ (domain p) := definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun x hx ↦ function_value_mem hπ (hdom x hx))
  have hgi : Injective g := by
    intro x y z hx hy
    obtain ⟨hxD, hzx⟩ := (pair_mem_definableGraph_iff _ _ (by definability) x z).mp hx
    obtain ⟨hyD, hzy⟩ := (pair_mem_definableGraph_iff _ _ (by definability) y z).mp hy
    exact injective_value_eq hπ hinj (hdom x hxD) (hdom y hyD) (hzx.symm.trans hzy)
  have he : domain (permutedGraph π p) = range g := by
    apply mem_ext
    intro x
    rw [mem_domain_iff, range_definableGraph, repl_spec]
    constructor
    · rintro ⟨y, hxy⟩
      obtain ⟨u, hu, he⟩ := (pair_mem_permutedGraph π p x y).mp hxy
      exact ⟨u, mem_domain_of_kpair_mem hu, he⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨y, huy⟩ := mem_domain_iff.mp hu
      exact ⟨y, (pair_mem_permutedGraph π p _ y).mpr ⟨u, huy, rfl⟩⟩
  let := IsFunction.of_mem hg
  rw [he]
  exact ⟨converseGraph g, converseGraph_mem_function hg hgi, converseGraph_injective g⟩

theorem permutedGraph_inverse_of_values {π ρ p : V} [IsFunction p]
    (hval : ∀ x ∈ domain p, ρ ‘ (π ‘ x) = x) :
    permutedGraph ρ (permutedGraph π p) = p := by
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨v, hv, rfl⟩ := (mem_permutedGraph ρ _ z).mp hz
    obtain ⟨u, hu, rfl⟩ := (mem_permutedGraph π p v).mp hv
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hu
    simpa only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair,
      hval x (mem_domain_of_kpair_mem hu)] using hu
  · intro hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    apply (mem_permutedGraph ρ _ _).mpr
    refine ⟨permutedGraphEntry π ⟨x, y⟩ₖ, (mem_permutedGraph π p _).mpr ⟨⟨x, y⟩ₖ, hz, rfl⟩, ?_⟩
    simp only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair,
      hval x (mem_domain_of_kpair_mem hz)]

theorem permutedGraph_domain_maps {π p : V} [IsFunction p] {x : V}
    (hx : x ∈ domain (permutedGraph π p)) : ∃ u ∈ domain p, x = π ‘ u := by
  obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
  obtain ⟨u, huy, he⟩ := (pair_mem_permutedGraph π p x y).mp hxy
  exact ⟨u, mem_domain_of_kpair_mem huy, he⟩

end ZFVP
