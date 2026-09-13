import ZFVP.ModelTheory.WoodinSparseAutomorphismLimit

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ m : V} [IsOrdinal θ]
local notation "c" => woodinSparsePrefixCode θ
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
variable (hm : IsCoherentForcingAutomorphismFamily θ (woodinSparsePrefixCode θ) m)
variable (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)

include hΩ hAC hθ in
private theorem actual_projection : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
    ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)) := by
  intro i hi j hj hij p hp
  let := IsOrdinal.of_mem hj
  exact woodinSparsePrefixCode_projection hΩ hAC hθ hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hp

include hΩ hAC hθ hm h0 hlim

theorem woodinSparseActualInverseAutomorphism :
    IsForcingIsomorphism (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c)
      (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) (woodinSparseInverseAutomorphism θ c m) :=
  woodinSparseInverseAutomorphism_isomorphism (woodinSparsePrefixCode_valid hΩ hAC hθ) hm h0 hlim
    (fun _ hi _ hp ↦ woodinSparsePrefixCode_sparse hΩ hAC hθ hi hp) (actual_projection hΩ hAC hθ)

theorem woodinSparseActualDirectAutomorphism :
    IsForcingIsomorphism (woodinSparseDirectBase θ c) (woodinSparseDirectOrder θ c)
      (woodinSparseDirectBase θ c) (woodinSparseDirectOrder θ c) (woodinSparseDirectAutomorphism θ c m) :=
  woodinSparseDirectAutomorphism_isomorphism (woodinSparsePrefixCode_valid hΩ hAC hθ) hm h0 hlim
    (fun _ hi _ hp ↦ woodinSparsePrefixCode_sparse hΩ hAC hθ hi hp) (actual_projection hΩ hAC hθ)
    (fun _ hi _ hj hij _ hp ↦ woodinSparsePrefixCode_section hΩ hAC hθ hi hj hij hp)

theorem woodinSparseActualInverseAutomorphism_restrict {q i : V}
    (hq : q ∈ woodinSparseInverseBase θ c) (hi : i ∈ θ) :
    ((woodinSparseInverseAutomorphism θ c m) ‘ q) ↾ (succ (woodinSourceIndex i)) =
      (m ‘ i) ‘ (q ↾ (succ (woodinSourceIndex i))) :=
  woodinSparseInverseAutomorphism_restrict (woodinSparsePrefixCode_valid hΩ hAC hθ) hm h0 hlim
    (fun _ hi _ hp ↦ woodinSparsePrefixCode_sparse hΩ hAC hθ hi hp) (actual_projection hΩ hAC hθ) hq hi

theorem woodinSparseActualDirectAutomorphism_restrict {q i : V}
    (hq : q ∈ woodinSparseDirectBase θ c) (hi : i ∈ θ) :
    ((woodinSparseDirectAutomorphism θ c m) ‘ q) ↾ (succ (woodinSourceIndex i)) =
      (m ‘ i) ‘ (q ↾ (succ (woodinSourceIndex i))) :=
  woodinSparseDirectAutomorphism_restrict (woodinSparsePrefixCode_valid hΩ hAC hθ) hm h0 hlim
    (fun _ hi _ hp ↦ woodinSparsePrefixCode_sparse hΩ hAC hθ hi hp) (actual_projection hΩ hAC hθ)
    (fun _ hi _ hj hij _ hp ↦ woodinSparsePrefixCode_section hΩ hAC hθ hi hj hij hp) hq hi

theorem woodinSparseActualInverseAutomorphism_section {k p : V}
    (hk : k ∈ θ) (hp : p ∈ (forcingCodeP c) ‘ k) :
    p ∈ woodinSparseInverseBase θ c ∧ (woodinSparseInverseAutomorphism θ c m) ‘ p = (m ‘ k) ‘ p :=
  woodinSparseInverseAutomorphism_section (woodinSparsePrefixCode_valid hΩ hAC hθ) hm h0 hlim
    (fun _ hi _ hp ↦ woodinSparsePrefixCode_sparse hΩ hAC hθ hi hp) (actual_projection hΩ hAC hθ)
    (fun _ hi _ hj hij _ hp ↦ woodinSparsePrefixCode_section hΩ hAC hθ hi hj hij hp) hk hp

theorem woodinSparseActualDirectAutomorphism_section {k p : V}
    (hk : k ∈ θ) (hp : p ∈ (forcingCodeP c) ‘ k) :
    p ∈ woodinSparseDirectBase θ c ∧ (woodinSparseDirectAutomorphism θ c m) ‘ p = (m ‘ k) ‘ p :=
  woodinSparseDirectAutomorphism_section (woodinSparsePrefixCode_valid hΩ hAC hθ) hm h0 hlim
    (fun _ hi _ hp ↦ woodinSparsePrefixCode_sparse hΩ hAC hθ hi hp) (actual_projection hΩ hAC hθ)
    (fun _ hi _ hj hij _ hp ↦ woodinSparsePrefixCode_section hΩ hAC hθ hi hj hij hp) hk hp

end ZFVP
