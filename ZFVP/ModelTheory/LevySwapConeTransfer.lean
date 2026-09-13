import ZFVP.ModelTheory.LevySwapDeterminedSupport
import ZFVP.ModelTheory.LevySupportValueBound
import ZFVP.ModelTheory.SolovayFiniteSupportTransfer

/-! The cone hypothesis of the Solovay corollary as one statement about a value-swap pair.

`ForcingContext.ConeOrbitTransfer` (`ZFVP/ModelTheory/LevyOrbitTransferReduction.lean`) asks for
two cone isomorphisms: one of the cone below the condition met by the generic onto the cone below
the condition in `H`, and one of the two complementary cones, each with its support clause. The
split in `ZFVP/ModelTheory/LevyConeTraceAlignment.lean` left the complementary half as a separate
open hypothesis `ForcingContext.ComplementConeAligned` beside `ForcingContext.ConeTraceAligned`.

For the Levy collapse the complementary half is not open. If the two conditions are the regular
cones of two collapse conditions `r` and `r'` of the same domain that agree at every coordinate of
`ω × ξ`, then the value swap `levySwapAutomorphism κ r r'` carries the one cone onto the other and
fixes every base support value determined below `ξ`
(`levy_complement_cone_isomorphism_support_of_determined`). And for a finite support there always
is such a `ξ < κ` (`levy_exists_determined_below_finite_support`).

So the whole cone hypothesis collapses to `ForcingContext.SwapConeData`: the positive side of
`ConeOrbitTransfer` with the two conditions required to be regular cones of collapse conditions of
equal domain agreeing below `ξ`. Nothing about the complementary cones is left in it.

* `levy_coneOrbitTransfer_of_swapConeData`: `SwapConeData` at a `ξ` determining the base support
  values gives `ConeOrbitTransfer`.
* `levy_coneOrbitTransfer_of_swapConeData_finite`: for a finite sequence `s` the `ξ` is produced,
  and the hypothesis is asked for at every `ξ ∈ κ` that determines the base support values, so it
  is a `ξ` the hypothesis gets to see.
* `solovay_corollary_of_swapConeData`: `cor:Solovay` with `SwapConeData` for finite sequences of
  saturated nice names as its only open assumption.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-! ### The residual hypothesis -/

/-- The positive half of `ForcingContext.ConeOrbitTransfer`, with the two conditions arranged as a
value-swap pair of the Levy collapse. For every orbit filter `H` over a support of saturated nice
names there are two conditions `r`, `r'` of `levyCollapse κ` with

* the same domain,
* the same values at every coordinate of `ω × ξ` where both are defined,

such that the regular cone of `r` is met by the generic, the check of the regular cone of `r'` is
in `H`, and some `f` is an isomorphism of the cone below `coneRegular r` onto the cone below
`coneRegular r'` carrying the generic to `H` pointwise and fixing the base support values of
`range s` relatively.

Nothing is asked about the complementary cones. Under the agreement clause the value swap of `r`
and `r'` supplies the complementary isomorphism and its support clause, provided the base support
values are determined below `ξ`. -/
def SwapConeData (A : ForcingContext V) (κ ξ : V) (Pf : SetTheorySemisentence 2) (s k : V)
    (p : A.Model) : Prop :=
  (∀ σ ∈ range s, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P
      ((ω : V) ×ˢ (ω : V)) σ) →
  ∀ H : A.Model, IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H →
    ∃ r ∈ levyCollapse κ, ∃ r' ∈ levyCollapse κ, ∃ f : V,
      domain r = domain r' ∧
      (∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z) ∧
      (∃ t ∈ A.G, t ∈ coneRegular A.P A.R r) ∧
      A.check (coneRegular A.P A.R r') ∈ H ∧
      IsForcingIsomorphism
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (coneRegular A.P A.R r))
          (restrictedOrder (booleanOrder A.P A.R)
            (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
              (coneRegular A.P A.R r)))
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (coneRegular A.P A.R r'))
          (restrictedOrder (booleanOrder A.P A.R)
            (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
              (coneRegular A.P A.R r'))) f ∧
      (∀ b ∈ booleanConditions A.P A.R, b ⊆ coneRegular A.P A.R r →
        (A.check (f ‘ b) ∈ H ↔ A.check b ∈ A.boolGenericSet)) ∧
      (∀ a ∈ supportValuesBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s),
        coneImage A.P A.R (coneRegular A.P A.R r) f (a ∩ coneRegular A.P A.R r) =
          a ∩ coneRegular A.P A.R r')

/-! ### The value of a symmetric name, from the cone hypothesis for finite sequences -/

/-- The value of a hereditarily symmetric name of the Solovay system is definable in the extension
from ground sets, reals and ordinals, given the cone hypothesis for finite sequences of saturated
nice names. This is `groundRealDefinable_booleanReal_of_finite_transfer` with the cone hypothesis
in place of the transfer statement: the sequence its proof feeds in enumerates a support, so its
values are saturated nice names and not merely nice names. -/
theorem groundRealDefinable_booleanReal_of_finite_cone (A : ForcingContext V)
    (Pf : SetTheorySemisentence 2) {p : A.Model} (hp : A.IsGroundRealDefinable p)
    (hground : ∀ a : V, Pf.Evalb ![A.check a, p])
    (hcone : ∀ s n : V, n ∈ (ω : V) → IsFunction s → domain s = n →
      (∀ σ ∈ range s, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P
        ((ω : V) ×ˢ (ω : V)) σ) →
      A.ConeOrbitTransfer Pf s n p)
    (τ : A.solovayContext.Name) :
    A.IsGroundRealDefinable (A.booleanReal ⟨τ.val, τ.property.1⟩) := by
  obtain ⟨E, hEf, hE, hEs⟩ := A.solovay_exists_support τ
  obtain ⟨s, hsfin, hsrange⟩ := exists_finiteSequence_range hEf
  obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff E s).mp hsfin
  have hsf : IsFunction s := IsFunction.of_mem hsn
  have hsdom : domain s = n := domain_eq_of_mem_function hsn
  have hnω : n ⊆ (ω : V) := IsOrdinal.toIsTransitive.transitive n hn
  have hsval : ∀ i ∈ n, s ‘ i ∈ E := by
    intro i hi
    rw [← hsrange]
    exact mem_range_of_kpair_mem (kpair_value_mem (by rw [hsdom]; exact hi))
  have hs : ∀ i ∈ n, IsNiceName (booleanConditions A.P A.R) A.P ((ω : V) ×ˢ (ω : V)) (s ‘ i) :=
    fun i hi ↦ (hE _ (hsval i hi)).nice
  have hErange : ∀ σ ∈ range s, IsSaturatedNiceName (booleanConditions A.P A.R)
      (booleanOrder A.P A.R) A.P ((ω : V) ×ˢ (ω : V)) σ := by
    rw [hsrange]
    exact hE
  have hsym : forcedStabilizer (booleanConditions A.P A.R) (booleanOrder A.P A.R)
      (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R)) (range s) ⊆
      nameStabilizer (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R))
        τ.val := by
    rw [hsrange]
    exact hEs
  set τ' : ForcingName A.booleanContext.P := ⟨τ.val, τ.property.1⟩ with hτ'
  have hsub1 : A.booleanReal τ' ⊆ A.solovayOrbitUnion Pf s n τ.val p :=
    A.booleanReal_subset_solovayOrbitUnion hsdom τ' hs Pf hground
  have hsub2 : A.solovayOrbitUnion Pf s n τ.val p ⊆ A.booleanReal τ' :=
    A.solovayOrbitUnion_subset_booleanReal Pf hsdom τ' hsym
      (orbitTransfer_of_coneOrbitTransfer Pf hErange (hcone s n hn hsf hsdom hErange))
  have heq : A.booleanReal τ' = A.solovayOrbitUnion Pf s n τ.val p :=
    mem_ext (fun z ↦ ⟨fun h ↦ hsub1 z h, fun h ↦ hsub2 z h⟩)
  rw [heq]
  exact A.groundRealDefinable_solovayOrbitUnion Pf s τ.val hnω hp

end ForcingContext

/-! ### The Levy exports -/

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

omit [IsOrdinal κ] in
/-- The cone hypothesis from the swap data. The isomorphism of the complementary cones and its
support clause come from the value swap of `r` and `r'`; the positive isomorphism, the filter
clause and the positive support clause are the swap data itself. -/
theorem levy_coneOrbitTransfer_of_swapConeData {ξ s k : V}
    (hdet : ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
        ((ω : V) ×ˢ (ω : V)) (range s), IsLevyDeterminedBelow κ ξ a)
    (hswap : (levyContext κ hG).SwapConeData κ ξ groundFormula s k (solovayParam κ hG)) :
    (levyContext κ hG).ConeOrbitTransfer groundFormula s k (solovayParam κ hG) := by
  intro hE H hH
  obtain ⟨r, hr, r', hr', f, hdom, hagree, hmeet, hq0H, hf, hfilter, hsupp⟩ := hswap hE H hH
  obtain ⟨⟨g, hg, hgsupp⟩, -⟩ :=
    levy_complement_cone_isomorphism_support_of_determined (E := range s) hr hr' hdom hagree hdet
  exact ⟨coneRegular (levyCollapse κ) (levyOrder κ) r,
    coneRegular_mem_booleanConditions (levyCollapse_poset κ).1 hr,
    coneRegular (levyCollapse κ) (levyOrder κ) r',
    coneRegular_mem_booleanConditions (levyCollapse_poset κ).1 hr',
    f, g, hf, hg, hmeet, hq0H, hfilter, fun a ha ↦ ⟨hsupp a ha, hgsupp a ha⟩⟩

include hAC hU hc hω hκ in
/-- The cone hypothesis for a finite sequence, from the swap data at every ordinal `ξ < κ` that
determines the base support values. The ordinal comes from
`levy_exists_determined_below_finite_support`, and it is handed to the hypothesis together with
the determinacy statement, so the hypothesis is asked about exactly the `ξ` that is used. -/
theorem levy_coneOrbitTransfer_of_swapConeData_finite {s n k : V} (hn : n ∈ (ω : V))
    (hsf : IsFunction s) (hsdom : domain s = n)
    (hswap : ∀ ξ ∈ κ,
      (∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
          ((ω : V) ×ˢ (ω : V)) (range s), IsLevyDeterminedBelow κ ξ a) →
      (levyContext κ hG).SwapConeData κ ξ groundFormula s k (solovayParam κ hG)) :
    (levyContext κ hG).ConeOrbitTransfer groundFormula s k (solovayParam κ hG) := by
  have hnfin : IsInternallyFinite n := ⟨n, hn, CardLE.refl n, CardLE.refl n⟩
  have hsfin : IsInternallyFinite s := internallyFinite_function (by rw [hsdom]; exact hnfin)
  have hrfin : IsInternallyFinite (range s) := internallyFinite_range hsfin
  obtain ⟨ξ, hξ, hdet⟩ := levy_exists_determined_below_finite_support hAC hU hc hω hκ hrfin
  exact levy_coneOrbitTransfer_of_swapConeData hG hdet (hswap ξ hξ hdet)

include hAC hU hc hω hκ in
/-- The hypothesis `hpt` of `solovay_corollary_final`, from the swap data for finite sequences of
saturated nice names. -/
theorem groundRealDefinable_solovayInclusion_of_swapConeData
    (hswap : ∀ s n k : V, n ∈ (ω : V) → IsFunction s → domain s = n →
      (∀ σ ∈ range s, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ) →
      ∀ ξ ∈ κ,
        (∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
            ((ω : V) ×ˢ (ω : V)) (range s), IsLevyDeterminedBelow κ ξ a) →
        (levyContext κ hG).SwapConeData κ ξ groundFormula s k (solovayParam κ hG))
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
      (hswap s n n hn hsf hsdom hE)

include hAC hU hc hω hκ in
/-- `cor:Solovay` with the swap data as its only open assumption, for finite sequences of
saturated nice names. The clauses are those of `solovay_corollary_of_transfer`. -/
theorem solovay_corollary_of_swapConeData [Countable V]
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (hswap : ∀ s n k : V, n ∈ (ω : V) → IsFunction s → domain s = n →
      (∀ σ ∈ range s, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ) →
      ∀ ξ ∈ κ,
        (∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
            ((ω : V) ×ˢ (ω : V)) (range s), IsLevyDeterminedBelow κ ξ a) →
        (levyContext κ hG).SwapConeData κ ξ groundFormula s k (solovayParam κ hG)) :
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
    (groundRealDefinable_solovayInclusion_of_swapConeData hAC hU hc hω hκ hG hswap)

end

end ZFVP
