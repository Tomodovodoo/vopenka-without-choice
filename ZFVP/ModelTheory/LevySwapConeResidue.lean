import ZFVP.ModelTheory.LevySwapConeTransfer
import ZFVP.ModelTheory.LevyConePairArrangement
import ZFVP.ModelTheory.LevyConeComplementHomogeneity

/-! The cone hypothesis of the Solovay corollary as one statement about the pair of conditions of
Jech, Set Theory, Lemma 25.5.

`cor:Solovay` is now proved with no open hypothesis at all, as
`ZFVP.Unconditional.solovay_corollary` in `ZFVP/ModelTheory/SolovayCorollaryUnconditional.lean`,
which closes the cone hypothesis by a different route (`levy_coneOrbitTransfer_finite`); the
conditional exports here are kept as the record of the reduction.

The chain, from the top. `solovay_corollary_final` gives `cor:Solovay` from the statement that the
value of every hereditarily symmetric name is definable in the extension from ground sets, reals
and ordinals; `ForcingContext.groundRealDefinable_booleanReal_of_finite_cone` gives that statement
from `ForcingContext.ConeOrbitTransfer` for the finite sequences of saturated nice names that
enumerate a support; `levy_coneOrbitTransfer_of_swapConeData_finite` gives `ConeOrbitTransfer` for
such a sequence from `ForcingContext.SwapConeData`, at an ordinal `ξ < κ` below which the base
support values are determined, and the ordinal is produced by
`levy_exists_determined_below_finite_support`. What is proved here is the last step:
`levy_swapConeData_of_conePairAgrees` gives `SwapConeData` from
`ForcingContext.ConePairAgrees`, and `solovay_corollary_of_conePairAgrees` is `cor:Solovay` with
`ConePairAgrees` as its only open assumption.

`ConePairAgrees` is `ForcingContext.ValueOfConeIsCone` of
`ZFVP/ModelTheory/LevyConePairArrangement.lean` with two clauses added. In words: for every orbit
filter `H` and every quadruple `τ σ p₀ q₀` carrying the clauses of Lemma 25.5, with `p₀` met by the
generic and `q̌₀ ∈ H`, there is a condition `r'` of the Levy collapse whose regular cone lies below
`q₀` and has its check in `H`, and a condition `r` of the Levy collapse with

* `‖(coneRegular r')ˇ ∈ τ‖ ∩ p₀ = coneRegular r`, which is `ValueOfConeIsCone`,
* `domain r = domain r'`,
* `r` and `r'` agree at every coordinate of `ω × ξ` where both are defined.

The first clause is the residue of the cone construction and by `orbitConeData_left_unique` it is
what makes both conditions of Lemma 25.5 regular cones of conditions of the collapse at once. The
other two are what the value swap `levySwapAutomorphism κ r r'` needs in order to supply the
complementary cone isomorphism with its support clause. `valueOfConeIsCone_of_conePairAgrees` is
the projection onto the first clause. The other direction is not proved here:
`inter_nonempty_iff_of_coneImage` and `levy_supportValues_decided_alike_of_swapConeData` say how far
the support clause constrains the pair, namely that `r` and `r'` decide every base support value
alike, and that is weaker than agreement at the coordinates of `ω × ξ`.

`exists_orbitConeData_cone_isomorphism_support` is `exists_orbit_cone_isomorphism_support` with the
data it consumes kept in the conclusion: the names `τ`, `σ`, the clauses of Lemma 25.5 at the pair
it produces, the value clause `ψ ‘ b = ‖b̌ ∈ τ‖ ∩ p₀`, and the support clause in `coneImage` form.
Without the value clause there is nothing to apply `ConePairAgrees` to, since the residue speaks
about the value map and the exported form of the construction speaks only about `ψ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable {A : ForcingContext V}

/-! ### Lemma 25.5 with the data it was built from -/

/-- `exists_orbit_cone_isomorphism_support` with the names and the clauses kept. For an orbit
filter over a support of saturated nice names there are names `τ`, `σ`, a condition `r` of the
generic filter and a condition `q₀` of the filter carrying the clauses of Lemma 25.5 at
`(coneRegular r, q₀)`, and an isomorphism `ψ` of the cone below `q₀` onto the cone below
`coneRegular r` which is the value map `b ↦ ‖b̌ ∈ τ‖ ∩ coneRegular r`, carries `H` to the generic
pointwise, and fixes the base support values.

The proof is that of `exists_orbit_cone_isomorphism_support`; only the conclusion is larger. -/
theorem exists_orbitConeData_cone_isomorphism_support (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {s k : V} [IsFunction s] (hsdom : domain s = k)
    (hs : ∀ i ∈ k, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P
      ((ω : V) ×ˢ (ω : V)) (s ‘ i))
    {p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H)
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a) :
    ∃ τ σ : V, ∃ r ∈ A.G, ∃ q₀ ∈ booleanConditions A.P A.R, ∃ ψ : V,
      (∀ b : V, (A.check b ∈ H ↔ ∃ t ∈ A.G, t ∈ A.booleanMemValue τ b)) ∧
      A.IsOrbitConeData τ σ (coneRegular A.P A.R r) q₀ ∧
      A.check q₀ ∈ H ∧
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q₀)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q₀))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (coneRegular A.P A.R r))
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (coneRegular A.P A.R r))) ψ ∧
      (∀ b ∈ booleanConditions A.P A.R, b ⊆ q₀ →
        ψ ‘ b = A.booleanMemValue τ b ∩ coneRegular A.P A.R r) ∧
      (∀ c ∈ booleanConditions A.P A.R, c ⊆ q₀ →
        (A.check c ∈ H ↔ A.check (ψ ‘ c) ∈ A.boolGenericSet)) ∧
      (∀ a ∈ supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s),
        coneImage A.P A.R q₀ ψ (a ∩ q₀) = a ∩ coneRegular A.P A.R r) := by
  classical
  obtain ⟨τ, σ, p₀, q₀, hval, hd, hp₀G, hq₀H, hdata⟩ := exists_orbitConeData hAC hH hPf
  obtain ⟨p₁, hp₁B, hp₁G, hp₁⟩ :=
    exists_condition_booleanMemValue_eq_on_supportAlgebra hAC hsdom hs hH hval
  obtain ⟨w, hwG, hw⟩ := meets_inter (booleanConditions_regular hdata.1)
    (booleanConditions_regular hp₁B) hp₀G hp₁G
  have hwP : w ∈ A.P := A.generic.1.1 w hwG
  have hp'B : coneRegular A.P A.R w ∈ booleanConditions A.P A.R :=
    coneRegular_mem_booleanConditions A.order hwP
  have hp'G : ∃ t ∈ A.G, t ∈ coneRegular A.P A.R w :=
    ⟨w, hwG, self_mem_coneRegular A.order hwP⟩
  have hp'p₀ : coneRegular A.P A.R w ⊆ p₀ := coneRegular_subset_of_mem A.order
    (booleanConditions_regular hdata.1) (mem_inter_iff.mp hw).1
  have hp'p₁ : coneRegular A.P A.R w ⊆ p₁ := coneRegular_subset_of_mem A.order
    (booleanConditions_regular hp₁B) (mem_inter_iff.mp hw).2
  have hdata' := A.orbitConeData_shrink_left hdata hp'B hp'p₀
  have hq'H : A.check (A.orbitInverseValue σ (coneRegular A.P A.R w) ∩ q₀) ∈ H :=
    A.check_orbitInverseValue_inter_mem hH.2.2.1 hd hp'B hp'G hq₀H
  obtain ⟨ψ, hiso, htr, hψ⟩ := A.exists_cone_isomorphism_of_data hdata' hval hp'G
  have hsupp : ∀ dd ∈ supportAlgebraBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s),
      dd ∩ (A.orbitInverseValue σ (coneRegular A.P A.R w) ∩ q₀) ∈ booleanConditions A.P A.R →
      ψ ‘ (dd ∩ (A.orbitInverseValue σ (coneRegular A.P A.R w) ∩ q₀)) =
        dd ∩ coneRegular A.P A.R w := by
    intro dd hdd hddq
    have hddB : dd ∈ booleanConditions A.P A.R := by
      refine (mem_booleanConditions_iff _ _ _).mpr
        ⟨((mem_algebraPreimage_iff _ _ _ _).mp hdd).1, ?_⟩
      obtain ⟨z, hz⟩ := booleanConditions_nonempty hddq
      exact ⟨z, (mem_inter_iff.mp hz).1⟩
    have hfix : A.booleanMemValue τ dd ∩ coneRegular A.P A.R w = dd ∩ coneRegular A.P A.R w := by
      have h := hp₁ dd hdd hddB
      rw [SetTheory.mem_ext_iff] at h
      apply mem_ext
      intro z
      constructor
      · intro hz
        obtain ⟨hzv, hzp⟩ := mem_inter_iff.mp hz
        exact mem_inter_iff.mpr
          ⟨(mem_inter_iff.mp ((h z).mp (mem_inter_iff.mpr ⟨hzv, hp'p₁ z hzp⟩))).1, hzp⟩
      · intro hz
        obtain ⟨hzd, hzp⟩ := mem_inter_iff.mp hz
        exact mem_inter_iff.mpr
          ⟨(mem_inter_iff.mp ((h z).mpr (mem_inter_iff.mpr ⟨hzd, hp'p₁ z hzp⟩))).1, hzp⟩
    rw [hψ _ hddq (fun z hz ↦ (mem_inter_iff.mp hz).2),
      A.orbitConeData_inter_eq hdata' hddB hdata'.2.1]
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨hzi, hzp⟩ := mem_inter_iff.mp hz
      have hz' : z ∈ A.booleanMemValue τ dd ∩ coneRegular A.P A.R w :=
        mem_inter_iff.mpr ⟨(mem_inter_iff.mp hzi).1, hzp⟩
      rw [hfix] at hz'
      exact mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz').1, hzp⟩
    · intro hz
      obtain ⟨hzd, hzp⟩ := mem_inter_iff.mp hz
      have hz' : z ∈ dd ∩ coneRegular A.P A.R w := mem_inter_iff.mpr ⟨hzd, hzp⟩
      rw [← hfix] at hz'
      exact mem_inter_iff.mpr
        ⟨mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz').1, hdata'.2.2.2.2.2.2.1 z hzp⟩, hzp⟩
  exact ⟨τ, σ, w, hwG, _, hdata'.2.1, ψ, hval, hdata', hq'H, hiso, hψ, htr,
    fun a ha ↦ coneImage_of_support_clause hdata'.2.1 hp'B hiso hsupp ha⟩

/-! ### The residue, with the swap clauses -/

/-- The statement that is left open. It is `ValueOfConeIsCone` for the data of an orbit filter,
strengthened by asking that the two conditions can be taken with the same domain and agreeing at
every coordinate of `ω × ξ` where both are defined.

For every orbit filter `H` over the support sequence `s` indexed by `k`, and every quadruple
`τ σ p₀ q₀` carrying the clauses of Lemma 25.5 with the value clause for `H`, with `p₀` met by the
generic and `q̌₀ ∈ H`, there are conditions `r`, `r'` of `levyCollapse κ` with `coneRegular r' ⊆ q₀`,
the check of `coneRegular r'` in `H`, `‖(coneRegular r')ˇ ∈ τ‖ ∩ p₀ = coneRegular r`,
`domain r = domain r'`, and `r ‘ z = r' ‘ z` for every `z ∈ (ω : V) ×ˢ ξ` in both domains.

The first three clauses are `ValueOfConeIsCone`, which by `orbitConeData_left_unique` is exactly
what makes both conditions of Lemma 25.5 regular cones of conditions of the collapse. The last two
are what `levy_complement_cone_isomorphism_support_of_determined` needs in order to build the
complementary cone isomorphism from the value swap of `r` and `r'`. -/
def ConePairAgrees (A : ForcingContext V) (κ ξ : V) (Pf : SetTheorySemisentence 2) (s k : V)
    (p : A.Model) : Prop :=
  ∀ H : A.Model, IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H →
    ∀ τ σ p₀ q₀ : V, A.IsOrbitConeData τ σ p₀ q₀ →
      (∀ b : V, (A.check b ∈ H ↔ ∃ t ∈ A.G, t ∈ A.booleanMemValue τ b)) →
      (∃ t ∈ A.G, t ∈ p₀) → A.check q₀ ∈ H →
      ∃ r' ∈ levyCollapse κ, coneRegular A.P A.R r' ⊆ q₀ ∧
        A.check (coneRegular A.P A.R r') ∈ H ∧
        ∃ r ∈ levyCollapse κ,
          A.booleanMemValue τ (coneRegular A.P A.R r') ∩ p₀ = coneRegular A.P A.R r ∧
          domain r = domain r' ∧
          (∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z)

end ForcingContext

/-! ### What the support clause forces about the pair

The support clause of `SwapConeData` says that the isomorphism carries the relative trace of every
base support value on `coneRegular r` to its relative trace on `coneRegular r'`. Since `coneImage`
of the empty set is the empty set and the image of a condition is a condition, this says exactly
that `r` and `r'` decide every base support value alike. It does not say that `r` and `r'` agree at
any coordinate: the base support values generate a subalgebra of the completion, and two conditions
of the collapse with different values at a coordinate of `ω × ξ` can meet exactly the same members
of that subalgebra as soon as no support value depends on that coordinate. So the agreement clause
of `ConePairAgrees` is not a consequence of the support clause together with determinacy below `ξ`;
determinacy says that each support value is decided by the restriction of a condition to `ω × ξ`,
not that the support values separate those restrictions. -/

/-- A cone isomorphism carrying the relative trace of a regular set to its relative trace makes the
two conditions decide that set alike. -/
theorem inter_nonempty_iff_of_coneImage {P R b0 c0 f a : V} (hb0 : b0 ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) b0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b0))
      (forcingCone (booleanConditions P R) (booleanOrder P R) c0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) c0)) f)
    (ha : IsForcingRegular P R a) (hcone : coneImage P R b0 f (a ∩ b0) = a ∩ c0) :
    (∃ z : V, z ∈ a ∩ b0) ↔ ∃ z : V, z ∈ a ∩ c0 := by
  rcases inter_mem_forcingCone_or_empty ha hb0 with hc | hc
  · refine ⟨fun _ ↦ ?_, fun _ ↦ booleanConditions_nonempty ((mem_forcingCone_iff _ _ _ _).mp hc).1⟩
    rw [coneImage_value hf hc] at hcone
    rw [← hcone]
    exact booleanConditions_nonempty
      ((mem_forcingCone_iff _ _ _ _).mp (function_value_mem hf.1 hc)).1
  · rw [hc, coneImage_empty] at hcone
    rw [hc]
    exact ⟨fun ⟨z, hz⟩ ↦ absurd hz not_mem_empty,
      fun ⟨z, hz⟩ ↦ absurd (by rw [← hcone] at hz; exact hz) not_mem_empty⟩

/-! ### The Levy exports -/

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

omit [IsOrdinal κ] hAC hU hc hω hκ in
/-- The residue of `LevyConePairArrangement` is the first clause of `ConePairAgrees`. -/
theorem valueOfConeIsCone_of_conePairAgrees {ξ s k : V}
    (hpair : (levyContext κ hG).ConePairAgrees κ ξ groundFormula s k (solovayParam κ hG))
    {H : (levyContext κ hG).Model}
    (hH : IsOrbitFilter groundFormula
      ((levyContext κ hG).check (regularSets (levyCollapse κ) (levyOrder κ)))
      ((levyContext κ hG).check (boolMaximalAntichains (levyCollapse κ) (levyOrder κ)))
      ((levyContext κ hG).check (levyCollapse κ)) ((levyContext κ hG).check s)
      ((levyContext κ hG).check k) ((levyContext κ hG).orbitSupportReal s k)
      (solovayParam κ hG) H)
    {τ σ p₀ q₀ : V} (hdata : (levyContext κ hG).IsOrbitConeData τ σ p₀ q₀)
    (hval : ∀ b : V, ((levyContext κ hG).check b ∈ H ↔
      ∃ t ∈ G, t ∈ (levyContext κ hG).booleanMemValue τ b))
    (hp₀G : ∃ t ∈ G, t ∈ p₀) (hq₀H : (levyContext κ hG).check q₀ ∈ H) :
    (levyContext κ hG).ValueOfConeIsCone H τ p₀ q₀ := by
  obtain ⟨r', hr'levy, hr'q₀, hr'H, r, hrlevy, hvalue, -, -⟩ :=
    hpair H hH τ σ p₀ q₀ hdata hval hp₀G hq₀H
  exact ⟨r', hr'levy, hr'q₀, hr'H, r, hrlevy, hvalue⟩

include hAC hU hc hω hκ in
/-- The swap data from the residue. The two conditions are the pair the residue returns: the
condition on the side of the generic is the value of the cone on the side of the filter, so the
isomorphism produced by Lemma 25.5 restricts to an isomorphism of the two regular cones, and its
inverse is the map the swap data asks for. The domain clause and the agreement clause are the two
clauses the residue adds. -/
theorem levy_swapConeData_of_conePairAgrees {ξ s k : V} (hsf : IsFunction s)
    (hsdom : domain s = k)
    (hpair : (levyContext κ hG).ConePairAgrees κ ξ groundFormula s k (solovayParam κ hG)) :
    (levyContext κ hG).SwapConeData κ ξ groundFormula s k (solovayParam κ hG) := by
  have := hsf
  intro hE H hH
  have hs : ∀ i ∈ k, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V))
      (s ‘ i) := by
    intro i hi
    exact hE _ (mem_range_of_kpair_mem (kpair_value_mem (by rw [hsdom]; exact hi)))
  obtain ⟨τ, σ, r₀, hr₀G, q₀, hq₀B, ψ, hval, hdata, hq₀H, hiso, hvalmap, hfilter, hsupp⟩ :=
    ForcingContext.exists_orbitConeData_cone_isomorphism_support (A := levyContext κ hG) hAC hsdom hs hH
      (levy_check_of_evalb_groundFormula hAC hU hc hω hκ hG)
  have hr₀P : r₀ ∈ levyCollapse κ := (levyContext κ hG).generic.1.1 r₀ hr₀G
  have hp₀B : coneRegular (levyCollapse κ) (levyOrder κ) r₀ ∈
      booleanConditions (levyCollapse κ) (levyOrder κ) :=
    coneRegular_mem_booleanConditions (levyContext κ hG).order hr₀P
  obtain ⟨r', hr'levy, hr'q₀, hr'H, r, hrlevy, hvalue, hdomeq, hagree⟩ :=
    hpair H hH τ σ _ q₀ hdata hval
      ⟨r₀, hr₀G, self_mem_coneRegular (levyContext κ hG).order hr₀P⟩ hq₀H
  have hq₁B : coneRegular (levyCollapse κ) (levyOrder κ) r' ∈
      booleanConditions (levyCollapse κ) (levyOrder κ) :=
    coneRegular_mem_booleanConditions (levyContext κ hG).order hr'levy
  have hp₁B : coneRegular (levyCollapse κ) (levyOrder κ) r ∈
      booleanConditions (levyCollapse κ) (levyOrder κ) :=
    coneRegular_mem_booleanConditions (levyContext κ hG).order hrlevy
  have hψq₁ : ψ ‘ (coneRegular (levyCollapse κ) (levyOrder κ) r') =
      coneRegular (levyCollapse κ) (levyOrder κ) r := by
    rw [hvalmap _ hq₁B hr'q₀]; exact hvalue
  obtain ⟨-, hgen, hisoR, hfilterR⟩ :=
    ForcingContext.coneRestrict_filterTransfer (A := levyContext κ hG) hp₀B hq₀B hiso hq₁B hr'q₀ hr'H hfilter
  rw [hψq₁] at hgen hisoR
  refine ⟨r, hrlevy, r', hr'levy,
    converseGraph (coneRestrictMap (levyCollapse κ) (levyOrder κ)
      (coneRegular (levyCollapse κ) (levyOrder κ) r') ψ),
    hdomeq, hagree, hgen, hr'H, isForcingIsomorphism_inverse hisoR,
    ForcingContext.filterTransfer_inverse (A := levyContext κ hG) hp₁B hisoR hfilterR, fun a ha ↦ ?_⟩
  have hareg : IsForcingRegular (levyCollapse κ) (levyOrder κ) a :=
    (mem_regularSets_iff _ _ _).mp
      (supportValuesBase_subset_regularSets (levyContext κ hG).order _ _ _ a ha)
  refine coneImage_inverse hisoR hq₁B hareg ?_
  have h := coneIsomorphism_restrict_coneImage hiso hp₀B hq₀B hq₁B hr'q₀ hareg (hsupp a ha)
  rwa [hψq₁] at h

omit [IsOrdinal κ] hAC hU hc hω hκ in
/-- The pair of the swap data decides every base support value alike. This is what the support
clause forces about `r` and `r'`; the agreement of `r` and `r'` on `ω × ξ` is not part of it, and
is asked for in `ConePairAgrees`. -/
theorem levy_supportValues_decided_alike_of_swapConeData {ξ s k : V}
    (hswap : (levyContext κ hG).SwapConeData κ ξ groundFormula s k (solovayParam κ hG))
    (hE : ∀ σ ∈ range s, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ)
    {H : (levyContext κ hG).Model}
    (hH : IsOrbitFilter groundFormula
      ((levyContext κ hG).check (regularSets (levyCollapse κ) (levyOrder κ)))
      ((levyContext κ hG).check (boolMaximalAntichains (levyCollapse κ) (levyOrder κ)))
      ((levyContext κ hG).check (levyCollapse κ)) ((levyContext κ hG).check s)
      ((levyContext κ hG).check k) ((levyContext κ hG).orbitSupportReal s k)
      (solovayParam κ hG) H) :
    ∃ r ∈ levyCollapse κ, ∃ r' ∈ levyCollapse κ,
      domain r = domain r' ∧
      (∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z) ∧
      ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
          ((ω : V) ×ˢ (ω : V)) (range s),
        ((∃ z : V, z ∈ a ∩ coneRegular (levyCollapse κ) (levyOrder κ) r) ↔
          ∃ z : V, z ∈ a ∩ coneRegular (levyCollapse κ) (levyOrder κ) r') := by
  obtain ⟨r, hr, r', hr', f, hdom, hagree, -, -, hf, -, hsupp⟩ := hswap hE H hH
  refine ⟨r, hr, r', hr', hdom, hagree, fun a ha ↦ ?_⟩
  have hareg : IsForcingRegular (levyCollapse κ) (levyOrder κ) a :=
    (mem_regularSets_iff _ _ _).mp
      (supportValuesBase_subset_regularSets (levyContext κ hG).order _ _ _ a ha)
  exact inter_nonempty_iff_of_coneImage
    (coneRegular_mem_booleanConditions (levyContext κ hG).order hr) hf hareg (hsupp a ha)

include hAC hU hc hω hκ in
/-- The hypothesis `hpt` of `solovay_corollary_final`, from the residue for the finite sequences of
saturated nice names that enumerate a support. -/
theorem groundRealDefinable_solovayInclusion_of_conePairAgrees
    (hpair : ∀ s k : V, k ∈ (ω : V) → IsFunction s → domain s = k →
      (∀ σ ∈ range s, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ) →
      ∀ ξ ∈ κ,
        (∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
            ((ω : V) ×ˢ (ω : V)) (range s), IsLevyDeterminedBelow κ ξ a) →
        (levyContext κ hG).ConePairAgrees κ ξ groundFormula s k (solovayParam κ hG))
    (x : (levySolovayContext κ hG).Model) :
    (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x) := by
  obtain ⟨τ, rfl⟩ := (levySolovayContext κ hG).ofName_surjective x
  refine ForcingContext.groundRealDefinable_booleanReal_of_finite_cone (levyContext κ hG)
    groundFormula (p := solovayParam κ hG) ?_ ?_ (fun s n hn hsf hsdom hE ↦ ?_) τ
  · rw [solovayParam_eq_check]
    exact ForcingContext.groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
  · intro a
    exact (eval_groundFormula _ _).mpr (levy_isGround_check hAC hU hc hω hκ hG a)
  · exact levy_coneOrbitTransfer_of_swapConeData_finite hAC hU hc hω hκ hG hn hsf hsdom
      (fun ξ hξ hdet ↦ levy_swapConeData_of_conePairAgrees hAC hU hc hω hκ hG hsf hsdom
        (hpair s n hn hsf hsdom hE ξ hξ hdet))

include hAC hU hc hω hκ in
/-- `cor:Solovay` with the residue as its only open assumption. The clauses are those of
`solovay_corollary_of_transfer`.

The open statement, in words: for every orbit filter over a finite support of saturated nice names
and every quadruple carrying the clauses of Lemma 25.5, the pair of conditions can be taken to be
the regular cones of two conditions of the Levy collapse of the same domain agreeing on `ω × ξ`,
where `ξ < κ` is an ordinal below which the base support values are determined. -/
theorem solovay_corollary_of_conePairAgrees [Countable V]
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (hpair : ∀ s k : V, k ∈ (ω : V) → IsFunction s → domain s = k →
      (∀ σ ∈ range s, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ) →
      ∀ ξ ∈ κ,
        (∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
            ((ω : V) ×ˢ (ω : V)) (range s), IsLevyDeterminedBelow κ ξ a) →
        (levyContext κ hG).ConePairAgrees κ ξ groundFormula s k (solovayParam κ hG)) :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    (SolovayHOD κ hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 ∧
    (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := SolovayHOD κ hG) φ) ∧
    InternalDependentChoice (SolovayHOD κ hG) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → IsLebesgueMeasurable X) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → BaireProperty X) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → PerfectSetProperty X) ∧
    ¬ InternalChoice (SolovayHOD κ hG) ∧
    hartogsNumber (ω : SolovayHOD κ hG) = solovayCheck hAC hU hc hω hκ hG κ ∧
    IsNonprincipalSetUltrafilter (solovayCheck hAC hU hc hω hκ hG κ)
      (solovayUltrafilter hAC hU hc hω hκ hG) ∧
    IsOrdinalComplete (solovayCheck hAC hU hc hω hκ hG κ)
      (solovayUltrafilter hAC hU hc hω hκ hG) :=
  solovay_corollary_final hAC hU hc hω hκ hG hVP
    (groundRealDefinable_solovayInclusion_of_conePairAgrees hAC hU hc hω hκ hG hpair)

end

end ZFVP
