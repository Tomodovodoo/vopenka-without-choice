import ZFVP.ModelTheory.SolovaySymmetricSupport

/-! Lifting an automorphism of a forcing preorder to its Boolean completion. The completion
`booleanConditions P R` consists of the nonempty regular subsets of `P`, ordered by inclusion.
An automorphism `π` of `(P, R)` carries regular sets to regular sets, so the pointwise image
`imageAction π` is a map of the completion to itself. Packaged as a set function by
`definableGraph`, it is an automorphism of `(booleanConditions P R, booleanOrder P R)`, so it is
an element of the group `forcingAutomorphisms (booleanConditions P R) (booleanOrder P R)` used by
the Solovay symmetric system. The assignment is a group homomorphism: it sends the identity to
the identity and composites to composites. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The image action on regular sets -/

/-- An automorphism carries regular sets to regular sets. -/
theorem imageAction_regular {P R π A : V} (hπ : IsForcingAutomorphism P R π)
    (hA : IsForcingRegular P R A) : IsForcingRegular P R (imageAction π A) := by
  refine ⟨imageAction_subset hπ hA.1, ?_, ?_⟩
  · intro x hx q hq hqx
    obtain ⟨p, hp, rfl⟩ := (mem_imageAction_iff _ _ _).mp hx
    obtain ⟨q₀, hq₀, rfl⟩ := forcingAutomorphism_surjective hπ q hq
    exact (value_mem_imageAction_iff hπ hA.1 hq₀).mpr
      (hA.2.1 p hp q₀ hq₀ ((hπ.2.2.2 q₀ hq₀ p (hA.1 p hp)).mpr hqx))
  · intro x hx hd
    obtain ⟨p, hp, rfl⟩ := forcingAutomorphism_surjective hπ x hx
    refine (value_mem_imageAction_iff hπ hA.1 hp).mpr (hA.2.2 p hp ?_)
    intro q hq hqp
    obtain ⟨r, hr, hrq⟩ := hd (π ‘ q) (function_value_mem hπ.1 hq) ((hπ.2.2.2 q hq p hp).mp hqp)
    obtain ⟨r₀, hr₀, rfl⟩ := (mem_imageAction_iff _ _ _).mp hr
    exact ⟨r₀, hr₀, (hπ.2.2.2 r₀ (hA.1 r₀ hr₀) q hq).mpr hrq⟩

/-- An automorphism carries conditions of the Boolean completion to conditions. -/
theorem imageAction_mem_booleanConditions {P R π A : V} (hπ : IsForcingAutomorphism P R π)
    (hA : A ∈ booleanConditions P R) : imageAction π A ∈ booleanConditions P R := by
  obtain ⟨hreg, p, hp⟩ := (mem_booleanConditions_iff P R A).mp hA
  exact (mem_booleanConditions_iff P R _).mpr ⟨imageAction_regular hπ hreg,
    π ‘ p, (value_mem_imageAction_iff hπ hreg.1 (hreg.1 p hp)).mpr hp⟩

/-- The image action of an automorphism is injective on subsets of the poset. -/
theorem imageAction_injective {P R π A C : V} (hπ : IsForcingAutomorphism P R π) (hA : A ⊆ P)
    (hC : C ⊆ P) (h : imageAction π A = imageAction π C) : A = C := by
  apply mem_ext
  intro q
  constructor
  · intro hq
    have hmem := (value_mem_imageAction_iff hπ hA (hA q hq)).mpr hq
    rw [h] at hmem
    exact (value_mem_imageAction_iff hπ hC (hA q hq)).mp hmem
  · intro hq
    have hmem := (value_mem_imageAction_iff hπ hC (hC q hq)).mpr hq
    rw [← h] at hmem
    exact (value_mem_imageAction_iff hπ hA (hC q hq)).mp hmem

/-- The image action is monotone and reflects inclusion. -/
theorem imageAction_subset_iff {P R π A C : V} (hπ : IsForcingAutomorphism P R π) (hA : A ⊆ P)
    (hC : C ⊆ P) : imageAction π A ⊆ imageAction π C ↔ A ⊆ C := by
  constructor
  · intro h q hq
    exact (value_mem_imageAction_iff hπ hC (hA q hq)).mp
      (h _ ((value_mem_imageAction_iff hπ hA (hA q hq)).mpr hq))
  · intro h x hx
    obtain ⟨p, hp, rfl⟩ := (mem_imageAction_iff _ _ _).mp hx
    exact (value_mem_imageAction_iff hπ hC (hA p hp)).mpr (h p hp)

/-- Every subset of the poset is the image of its preimage under the inverse automorphism. -/
theorem imageAction_converseGraph_image {P R π C : V} (hπ : IsForcingAutomorphism P R π)
    (hC : C ⊆ P) : imageAction π (imageAction (converseGraph π) C) = C := by
  have hi := forcingAutomorphism_inverse hπ
  rw [← imageAction_compose hi.1 hπ.1 hC, forcingAutomorphism_inverse_compose hπ,
    imageAction_identity hC]

/-! ### The lift as a set function -/

/-- The map of the Boolean completion induced by an automorphism `π` of the base poset: it sends
a regular set to its pointwise image under `π`. -/
noncomputable def booleanLift (P R π : V) : V :=
  definableGraph (booleanConditions P R) (imageAction π) (by definability)

theorem booleanLift_mem_function {P R π : V} (hπ : IsForcingAutomorphism P R π) :
    booleanLift P R π ∈ booleanConditions P R ^ booleanConditions P R :=
  definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun _ hA ↦ imageAction_mem_booleanConditions hπ hA)

theorem booleanLift_value {P R π A : V} (hA : A ∈ booleanConditions P R) :
    (booleanLift P R π) ‘ A = imageAction π A := by
  unfold booleanLift
  exact value_definableGraph _ _ _ hA

theorem booleanLift_injective {P R π : V} (hπ : IsForcingAutomorphism P R π) :
    Injective (booleanLift P R π) := by
  intro A C B hA hC
  unfold booleanLift at hA hC
  rw [pair_mem_definableGraph_iff] at hA hC
  obtain ⟨hA, hAB⟩ := hA
  obtain ⟨hC, hCB⟩ := hC
  exact imageAction_injective hπ ((mem_booleanConditions_iff P R A).mp hA).1.1
    ((mem_booleanConditions_iff P R C).mp hC).1.1 (hAB.symm.trans hCB)

theorem booleanLift_range {P R π : V} (hπ : IsForcingAutomorphism P R π) :
    range (booleanLift P R π) = booleanConditions P R := by
  unfold booleanLift
  rw [range_definableGraph]
  apply mem_ext
  intro C
  rw [repl_spec]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact imageAction_mem_booleanConditions hπ hA
  · intro hC
    have hCP : C ⊆ P := ((mem_booleanConditions_iff P R C).mp hC).1.1
    exact ⟨imageAction (converseGraph π) C,
      imageAction_mem_booleanConditions (forcingAutomorphism_inverse hπ) hC,
      (imageAction_converseGraph_image hπ hCP).symm⟩

/-! ### The lift is an automorphism of the completion -/

theorem booleanLift_isForcingAutomorphism {P R π : V} (hπ : IsForcingAutomorphism P R π) :
    IsForcingAutomorphism (booleanConditions P R) (booleanOrder P R) (booleanLift P R π) := by
  refine ⟨booleanLift_mem_function hπ, booleanLift_injective hπ, booleanLift_range hπ, ?_⟩
  intro A hA C hC
  rw [kpair_mem_booleanOrder_iff, booleanLift_value hA, booleanLift_value hC,
    kpair_mem_booleanOrder_iff]
  have hAP : A ⊆ P := ((mem_booleanConditions_iff P R A).mp hA).1.1
  have hCP : C ⊆ P := ((mem_booleanConditions_iff P R C).mp hC).1.1
  exact ⟨fun h ↦ ⟨imageAction_mem_booleanConditions hπ hA,
      imageAction_mem_booleanConditions hπ hC, (imageAction_subset_iff hπ hAP hCP).mpr h.2.2⟩,
    fun h ↦ ⟨hA, hC, (imageAction_subset_iff hπ hAP hCP).mp h.2.2⟩⟩

theorem booleanLift_mem_forcingAutomorphisms {P R π : V} (hπ : IsForcingAutomorphism P R π) :
    booleanLift P R π ∈ forcingAutomorphisms (booleanConditions P R) (booleanOrder P R) :=
  (mem_forcingAutomorphisms_iff _ _ _).mpr (booleanLift_isForcingAutomorphism hπ)

/-! ### The lift is a group homomorphism -/

theorem booleanLift_identity (P R : V) :
    booleanLift P R (identity P) = identity (booleanConditions P R) := by
  have h1 := booleanLift_mem_function (forcingAutomorphism_identity P (R := R))
  have h2 := identity_mem_function (booleanConditions P R)
  have : IsFunction (booleanLift P R (identity P)) := IsFunction.of_mem h1
  have : IsFunction (identity (booleanConditions P R) : V) := IsFunction.of_mem h2
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function h1, domain_eq_of_mem_function h2]
  · intro A hA
    have hA' : A ∈ booleanConditions P R := domain_eq_of_mem_function h1 ▸ hA
    rw [booleanLift_value hA', identity_value hA',
      imageAction_identity ((mem_booleanConditions_iff P R A).mp hA').1.1]

/-- `compose π ρ` acts as `ρ` after `π`, and so does its lift. -/
theorem booleanLift_compose {P R π ρ : V} (hπ : IsForcingAutomorphism P R π)
    (hρ : IsForcingAutomorphism P R ρ) :
    booleanLift P R (compose π ρ) = compose (booleanLift P R π) (booleanLift P R ρ) := by
  have h1 := booleanLift_mem_function (forcingAutomorphism_compose hπ hρ)
  have hLπ := booleanLift_mem_function hπ
  have hLρ := booleanLift_mem_function hρ
  have h2 := compose_function hLπ hLρ
  have : IsFunction (booleanLift P R (compose π ρ)) := IsFunction.of_mem h1
  have : IsFunction (compose (booleanLift P R π) (booleanLift P R ρ)) := IsFunction.of_mem h2
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function h1, domain_eq_of_mem_function h2]
  · intro A hA
    have hA' : A ∈ booleanConditions P R := domain_eq_of_mem_function h1 ▸ hA
    have hAP : A ⊆ P := ((mem_booleanConditions_iff P R A).mp hA').1.1
    rw [booleanLift_value hA', value_compose_of_mem_function hLπ hLρ hA',
      booleanLift_value (π := π) hA',
      booleanLift_value (π := ρ) (imageAction_mem_booleanConditions hπ hA'),
      imageAction_compose hπ.1 hρ.1 hAP]

/-! ### Bridge to the Solovay symmetric system -/

/-- The lift of `π` sends the Boolean value `‖ǩ ∈ σ‖` to the Boolean value `‖ǩ ∈ πσ‖`. -/
theorem booleanLift_value_atomicMembership {P R one π k σ : V} (hR : IsForcingPoset P R)
    (hone : IsForcingTop P R one) (hπ : IsForcingAutomorphism P R π) (hσ : IsForcingName P σ)
    (hb : atomicMembership P R (checkName one k) σ ∈ booleanConditions P R) :
    (booleanLift P R π) ‘ (atomicMembership P R (checkName one k) σ) =
      atomicMembership P R (checkName one k) (nameAction π σ) := by
  rw [booleanLift_value hb]
  exact imageAction_atomicMembership_checkName hR hone hπ hσ

/-- The lift of `π` fixes the Boolean value `‖ǩ ∈ σ‖` exactly when `‖ǩ ∈ πσ‖` is that same
value. -/
theorem booleanLift_fixes_supportValue_iff {P R one π k σ : V} (hR : IsForcingPoset P R)
    (hone : IsForcingTop P R one) (hπ : IsForcingAutomorphism P R π) (hσ : IsForcingName P σ)
    (hb : atomicMembership P R (checkName one k) σ ∈ booleanConditions P R) :
    (booleanLift P R π) ‘ (atomicMembership P R (checkName one k) σ) =
        atomicMembership P R (checkName one k) σ ↔
      atomicMembership P R (checkName one k) (nameAction π σ) =
        atomicMembership P R (checkName one k) σ := by
  rw [booleanLift_value_atomicMembership hR hone hπ hσ hb]

/-- Every automorphism in the forced stabilizer of a set of saturated nice names lifts to an
automorphism of the Boolean completion that fixes each condition of the support algebra. -/
theorem booleanLift_fixes_supportAlgebra {P R Γ one K E : V} (hR : IsForcingPoset P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hone : IsForcingTop P R one)
    (hE : ∀ σ ∈ E, IsSaturatedNiceName P R one K σ) {π : V}
    (hπ : π ∈ forcedStabilizer P R Γ E) :
    ∀ d ∈ supportAlgebra P R one K E, d ∈ booleanConditions P R →
      (booleanLift P R π) ‘ d = d := by
  intro d hd hdB
  rw [booleanLift_value hdB]
  exact supportAlgebra_fixed_of_forcedStabilizer hR hΓ hone hE hπ d hd

end ZFVP
