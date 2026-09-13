import ZFVP.ModelTheory.SolovayNiceNameValues
import ZFVP.ModelTheory.SolovaySymmetricSupport

/-! The self-reflection properties of the class name `Ṙ_can` of the Solovay symmetric system
(Karagila-Schilhan Definitions 9.1 and 9.2), for the realization of `Ṙ_can` used here: the class
of saturated nice names for subsets of a ground set `K`, with the filter `niceNameFilter` it
generates.

The class is fixed by every automorphism of the poset: a name is a saturated nice name if and
only if its image under an automorphism is, so the set of automorphisms that map the class to
itself is the whole group. A checked ground set is fixed syntactically by every automorphism, so
its stabilizer and its forced stabilizer are also the whole group. Finally, for a ground set
`r0 ⊆ K` the value of `ř0` in the Boolean extension is exactly the value of the saturated nice
name built from `ř0`, so `ř0` lies in the class and in the symmetric model. The last group of
results records that the system is set sized: its poset, group and filter are elements of `V` and
form a symmetric system, and the filter is the definable subset of `℘ Γ` cut out by the
generated-filter condition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The class of saturated nice names is equivariant -/

/-- A name is a saturated nice name over `K` exactly when its image under an automorphism is.
This is the paper's `π Ṙ_can = Ṙ_can` for the realization of `Ṙ_can` by nice names. -/
theorem saturatedNiceName_nameAction_iff {P R one K π τ : V} (hR : IsForcingPoset P R)
    (hone : IsForcingTop P R one) (hπ : IsForcingAutomorphism P R π) (hτ : IsForcingName P τ) :
    IsSaturatedNiceName P R one K (nameAction π τ) ↔ IsSaturatedNiceName P R one K τ := by
  refine ⟨fun h ↦ ?_, saturatedNiceName_nameAction hR hone hπ⟩
  have hi := forcingAutomorphism_inverse hπ
  have h1 := saturatedNiceName_nameAction hR hone hi h
  rwa [nameAction_compose hπ.1 hi.1 hτ, forcingAutomorphism_compose_inverse hπ,
    nameAction_identity hτ] at h1

/-- The automorphisms in `Γ` that map the class of saturated nice names over `K` to itself. -/
noncomputable def niceNameClassStabilizer (P R Γ one K : V) : V :=
  sep Γ (fun π ↦ ∀ τ σ, IsForcingName P τ → σ = nameAction π τ →
      (IsSaturatedNiceName P R one K σ ↔ IsSaturatedNiceName P R one K τ))
    (by have := isSaturatedNiceName_definable P R one K; definability)

theorem mem_niceNameClassStabilizer_iff (P R Γ one K π : V) :
    π ∈ niceNameClassStabilizer P R Γ one K ↔ π ∈ Γ ∧ ∀ τ, IsForcingName P τ →
      (IsSaturatedNiceName P R one K (nameAction π τ) ↔ IsSaturatedNiceName P R one K τ) := by
  rw [niceNameClassStabilizer, mem_sep_iff]
  exact and_congr_right fun _ ↦
    ⟨fun h τ hτ ↦ h τ _ hτ rfl, fun h τ σ hτ hσ ↦ hσ ▸ h τ hτ⟩

/-- The stabilizer of the class of saturated nice names is the whole automorphism group. -/
theorem niceNameClassStabilizer_eq {P R Γ one : V} (hR : IsForcingPoset P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hone : IsForcingTop P R one) (K : V) :
    niceNameClassStabilizer P R Γ one K = Γ := by
  apply mem_ext
  intro π
  rw [mem_niceNameClassStabilizer_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun τ hτ ↦
    saturatedNiceName_nameAction_iff hR hone (hΓ.1 π h) hτ⟩⟩

/-! ### Checked ground sets -/

/-- The forced stabilizer of a single check is the whole automorphism group. -/
theorem forcedStabilizer_checkName_singleton {P R Γ one : V} (hR : IsForcingPoset P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hone : IsForcingTop P R one) (a : V) :
    forcedStabilizer P R Γ ({checkName one a} : V) = Γ := by
  apply mem_ext
  intro π
  rw [mem_forcedStabilizer]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun τ hτ ↦ ?_⟩⟩
  rw [mem_singleton_iff.mp hτ,
    nameAction_checkName hone.1 (forcingAutomorphism_top hR hone (hΓ.1 π h)) a]
  exact forcedEqual_refl hR.1 _

namespace ForcingContext

variable (A : ForcingContext V)

/-- On the Boolean completion, the forced stabilizer of a check is all of `Aut(B)`: the paper's
"`ř0` has stabilizer `Aut(B)`". -/
theorem checkName_forcedStabilizer_top (a : V) :
    forcedStabilizer (booleanConditions A.P A.R) (booleanOrder A.P A.R)
        (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R))
        ({checkName A.P a} : V) =
      forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R) :=
  forcedStabilizer_checkName_singleton (booleanOrder_poset _ _)
    (forcingAutomorphisms_group _ _) (booleanOrder_top ⟨A.one, A.top.1⟩) a

/-- The syntactic stabilizer of a check on the Boolean completion is all of `Aut(B)`; this is
`nameStabilizer_checkName` of `ZFVP/SetTheory/HereditarySymmetry.lean`. -/
theorem checkName_nameStabilizer_top (a : V) :
    nameStabilizer (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R))
        (checkName A.P a) =
      forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R) :=
  nameStabilizer_checkName (booleanOrder_poset _ _) (forcingAutomorphisms_group _ _)
    (booleanOrder_top ⟨A.one, A.top.1⟩) a

/-- The stabilizer of the class of saturated nice names over `K` on the Boolean completion is all
of `Aut(B)`: the paper's "`Ṙ_can` has stabilizer `Aut(B)`". -/
theorem niceName_class_stabilizer_top (K : V) :
    niceNameClassStabilizer (booleanConditions A.P A.R) (booleanOrder A.P A.R)
        (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R)) A.P K =
      forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R) :=
  niceNameClassStabilizer_eq (booleanOrder_poset _ _) (forcingAutomorphisms_group _ _)
    (booleanOrder_top ⟨A.one, A.top.1⟩) K

/-- Checks are monotone for inclusion. -/
theorem check_subset_check {r0 K : V} (h : r0 ⊆ K) : A.check r0 ⊆ A.check K := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (A.mem_check_iff r0 x).mp hx
  exact (A.mem_check_iff K _).mpr ⟨y, h y hy, rfl⟩

end ForcingContext

/-! ### Ground sets below `K` reflect into the class -/

namespace ForcingContext

variable (A : ForcingContext V)

/-- For `r0 ⊆ K` the nice name over `K` of `ř0` has the same value as `ř0` itself. This is the
sharp form of "`1 ⊩ ř0 ∈ Ṙ_can`": the ground set is literally the value of a saturated nice
name. -/
theorem ofName_booleanNiceName_checkName {r0 K : V} (h : r0 ⊆ K) :
    A.booleanContext.ofName (A.booleanNiceName K
        ⟨checkName A.booleanContext.one r0, checkName_isName A.booleanContext.top.1 r0⟩) =
      A.booleanContext.check r0 := by
  apply mem_ext
  intro x
  rw [A.mem_ofName_booleanNiceName_iff, ← A.booleanContext.check_eq_ofName_checkName]
  exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨A.booleanContext.check_subset_check h x hx, hx⟩⟩

/-- The saturated nice name of `ř0` is a hereditarily symmetric name of the nice-name system whose
value is `ř0`. -/
theorem toOrdinary_niceSymmetricName_checkName {r0 K : V} (h : r0 ⊆ K) :
    (A.niceSymmetricContext K).toOrdinary ((A.niceSymmetricContext K).ofName
        (A.niceSymmetricName K ⟨checkName A.booleanContext.one r0,
          checkName_isName A.booleanContext.top.1 r0⟩)) =
      A.booleanContext.check r0 :=
  (A.toOrdinary_ofName_niceSymmetricName K _).trans (A.ofName_booleanNiceName_checkName h)

/-- For `r0 ⊆ K` the value of `ř0` in the Boolean extension is a subset of the checked `K` and is
the value of a saturated nice name. -/
theorem exists_saturatedNiceName_check {r0 K : V} (h : r0 ⊆ K) :
    A.booleanContext.check r0 ⊆ A.booleanContext.check K ∧
      ∃ τ : (A.niceSymmetricContext K).Name,
        IsSaturatedNiceName A.booleanContext.P A.booleanContext.R A.booleanContext.one K τ.val ∧
        (A.niceSymmetricContext K).toOrdinary ((A.niceSymmetricContext K).ofName τ) =
          A.booleanContext.check r0 :=
  ⟨A.booleanContext.check_subset_check h,
    _, A.niceSymmetricName_saturated K _, A.toOrdinary_niceSymmetricName_checkName h⟩

/-- For a ground set `r0` of pairs of naturals, `ř0` is a subset of the checked `ω × ω` in the
poset extension and lies in the range of the Solovay symmetric model. -/
theorem check_mem_range_of_subset {r0 : V} (h : r0 ⊆ (ω : V) ×ˢ (ω : V)) :
    A.check r0 ⊆ A.check ((ω : V) ×ˢ (ω : V)) ∧ A.check r0 ∈ Set.range A.solovayInclusion :=
  ⟨A.check_subset_check h, A.solovay_check_mem_range r0⟩

end ForcingContext

/-! ### The system is set sized -/

theorem mem_niceNameFilter_iff (P R Γ one K H : V) :
    H ∈ niceNameFilter P R Γ one K ↔ IsForcingSubgroup P Γ H ∧ ∃ E, IsInternallyFinite E ∧
      (∀ σ ∈ E, IsSaturatedNiceName P R one K σ) ∧ forcedStabilizer P R Γ E ⊆ H :=
  mem_forcedStabilizerFilter P R Γ (IsSaturatedNiceName P R one K)
    (isSaturatedNiceName_definable P R one K) H

theorem niceNameFilter_subset_power (P R Γ one K : V) :
    niceNameFilter P R Γ one K ⊆ ℘ Γ := by
  intro H hH
  exact mem_power_iff.mpr ((mem_niceNameFilter_iff P R Γ one K H).mp hH).1.1

/-- The condition defining `niceNameFilter` inside `℘ Γ` is a set-theoretic formula with
parameters `P`, `R`, `Γ`, `one`, `K`. -/
theorem niceNameFilter_definable (P R Γ one K : V) :
    ℒₛₑₜ-predicate[V] (fun H ↦ IsForcingSubgroup P Γ H ∧ ∃ E, IsInternallyFinite E ∧
      (∀ σ ∈ E, IsSaturatedNiceName P R one K σ) ∧ forcedStabilizer P R Γ E ⊆ H) := by
  have := isSaturatedNiceName_definable P R one K
  have := forcedStabilizer_definable (V := V) P R
  definability

namespace ForcingContext

variable (A : ForcingContext V)

/-- The three data of the Solovay system are sets of `V`, and together with the Boolean order they
form a symmetric system in the sense of `IsSymmetricSystem`. -/
theorem solovaySystem_setSized :
    IsSymmetricSystem A.solovayContext.P A.solovayContext.R A.solovayContext.Γ
      A.solovayContext.F :=
  ⟨A.solovayContext.poset, ⟨A.solovayContext.one, A.solovayContext.top⟩,
    A.solovayContext.group, A.solovayContext.normal⟩

/-- The filter of the Solovay system is a definable subset of `℘ Aut(B)`. -/
theorem solovayFilter_subset_power :
    A.solovayContext.F ⊆ ℘ A.solovayContext.Γ :=
  niceNameFilter_subset_power _ _ _ _ _

end ForcingContext

end ZFVP
