import ZFVP.ModelTheory.LevyOrbitConeSupportGeneral
import ZFVP.ModelTheory.LevyHighConeDensity
import ZFVP.ModelTheory.LevyComplementRelativeIsomorphism
import ZFVP.ModelTheory.LevySwapConeTransfer

/-! The cone hypothesis of the Solovay corollary for the Levy collapse, with nothing left open.

`ForcingContext.ConeOrbitTransfer` (`ZFVP/ModelTheory/LevyOrbitTransferReduction.lean`) asks, for
every orbit filter `H`, for a condition `p0` met by the generic, a condition `q0` whose check is in
`H`, an isomorphism of the cone of `p0` onto the cone of `q0` carrying the generic to `H` and
fixing the base support values, and an isomorphism of the two complementary cones fixing them too.

Both halves are available for the Levy collapse once the pair is arranged so that each side sits
inside the regular cone of a condition using a coordinate in a column at or above `ξ`.

* `exists_orbitConeData_cone_isomorphism_support_general` (Jech 25.5) builds a first pair
  `(coneRegular r, q₀)` and, more to the point, keeps the clause that rebuilds the isomorphism, the
  filter clause and the support clause at every later shrinking of that pair.
* `levy_exists_high_trace_coneRegular_below` shrinks the right side to the regular cone of a high
  condition `r'`, and `levy_exists_high_generic_condition` shrinks the left side to the regular cone
  of a high condition `w` of the generic. `orbitConeData_shrink_right` and
  `orbitConeData_shrink_left` carry the data of Lemma 25.5 along.
* The pair that comes out is `p0 = coneRegular w` and `q0 = orbitInverseValue σ p0 ∩ coneRegular r'`,
  so `p0` is the cone of a high condition and `q0` sits inside the cone of a high condition. That is
  exactly the input of `levy_exists_complement_cone_isomorphism_supportValues`, which supplies the
  complementary isomorphism and its support clause.

`levy_coneOrbitTransfer_of_determined` assembles the two, given an ordinal `ξ < κ` below which
every base support value is determined. For a finite support such a `ξ` exists
(`levy_exists_determined_below_finite_support`), which gives the hypothesis-free
`levy_coneOrbitTransfer_finite`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- The cone hypothesis for the Levy collapse, for a support sequence whose base support values are
all determined below one `ξ < κ`. No open hypothesis: both cone isomorphisms are built.

The pair of conditions is arranged with a high condition on each side, and then the positive
isomorphism is the inverse of the value map of Lemma 25.5 at that pair, while the complementary
isomorphism comes from relative homogeneity below `ξ`. -/
theorem levy_coneOrbitTransfer_of_determined {ξ s k : V} (hξκ : ξ ∈ κ)
    (hsf : IsFunction s) (hsdom : domain s = k)
    (hdet : ∀ a, a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
        ((ω : V) ×ˢ (ω : V)) (range s) → IsLevyDeterminedBelow κ ξ a) :
    (levyContext κ hG).ConeOrbitTransfer groundFormula s k (solovayParam κ hG) := by
  have := hsf
  have hξ : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξκ
  intro hE H hH
  have hs : ∀ i ∈ k, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V))
      (s ‘ i) := fun i hi ↦
    hE _ (mem_range_of_kpair_mem (kpair_value_mem (by rw [hsdom]; exact hi)))
  -- Jech 25.5, with the clause that rebuilds everything at a smaller pair
  obtain ⟨τ, σ, r, hrG, q₀, hq₀B, ψ, hval, hd, hdata, hq₀H, -, -, -, -, hgen⟩ :=
    ForcingContext.exists_orbitConeData_cone_isomorphism_support_general
      (A := levyContext κ hG) hAC hsdom hs hH
      (levy_check_of_evalb_groundFormula hAC hU hc hω hκ hG)
  have hrP : r ∈ levyCollapse κ := (levyContext κ hG).generic.1.1 r hrG
  have hp₀G : ∃ t ∈ G, t ∈ coneRegular (levyCollapse κ) (levyOrder κ) r :=
    ⟨r, hrG, self_mem_coneRegular (levyContext κ hG).order hrP⟩
  -- shrink the side of the filter to the regular cone of a high condition
  obtain ⟨r', hr'P, hr'high, hr'q₀, hr'H⟩ :=
    ForcingContext.levy_exists_high_trace_coneRegular_below (A := levyContext κ hG) hAC rfl rfl
      hξ hξκ hω hH hq₀B hq₀H
  have hq'B : coneRegular (levyCollapse κ) (levyOrder κ) r' ∈
      booleanConditions (levyCollapse κ) (levyOrder κ) :=
    coneRegular_mem_booleanConditions (levyContext κ hG).order hr'P
  have hdata2 := (levyContext κ hG).orbitConeData_shrink_right hdata hq'B hr'q₀
  have hregset : IsForcingRegular (levyCollapse κ) (levyOrder κ)
      ((levyContext κ hG).booleanMemValue τ (coneRegular (levyCollapse κ) (levyOrder κ) r') ∩
        coneRegular (levyCollapse κ) (levyOrder κ) r) :=
    forcingRegular_inter ((levyContext κ hG).booleanMemValue_regular τ _)
      (booleanConditions_regular hdata.1)
  obtain ⟨w0, hw0G, hw0⟩ : ∃ t ∈ G, t ∈ (levyContext κ hG).booleanMemValue τ
      (coneRegular (levyCollapse κ) (levyOrder κ) r') ∩
      coneRegular (levyCollapse κ) (levyOrder κ) r :=
    ForcingContext.meets_inter ((levyContext κ hG).booleanMemValue_regular τ _)
      (booleanConditions_regular hdata.1) ((hval _).mp hr'H) hp₀G
  -- shrink the side of the generic to the regular cone of a high condition
  obtain ⟨w, hwG, hwP, hw0w, hwhigh⟩ := levy_exists_high_generic_condition hξ hξκ hω hG hw0G
  have hw0P : w0 ∈ levyCollapse κ := hG.1.1 w0 hw0G
  have hwmem : w ∈ (levyContext κ hG).booleanMemValue τ
      (coneRegular (levyCollapse κ) (levyOrder κ) r') ∩
      coneRegular (levyCollapse κ) (levyOrder κ) r :=
    hregset.2.1 w0 hw0 w hwP ((pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hwP, hw0P, hw0w⟩)
  have hpsub := coneRegular_subset_of_mem (levyContext κ hG).order hregset hwmem
  have hpB : coneRegular (levyCollapse κ) (levyOrder κ) w ∈
      booleanConditions (levyCollapse κ) (levyOrder κ) :=
    coneRegular_mem_booleanConditions (levyContext κ hG).order hwP
  have hpG : ∃ t ∈ G, t ∈ coneRegular (levyCollapse κ) (levyOrder κ) w :=
    ⟨w, hwG, self_mem_coneRegular (levyContext κ hG).order hwP⟩
  have hdata3 := (levyContext κ hG).orbitConeData_shrink_left hdata2 hpB hpsub
  have hq0H : (levyContext κ hG).check
      ((levyContext κ hG).orbitInverseValue σ (coneRegular (levyCollapse κ) (levyOrder κ) w) ∩
        coneRegular (levyCollapse κ) (levyOrder κ) r') ∈ H :=
    (levyContext κ hG).check_orbitInverseValue_inter_mem hH.2.2.1 hd hpB hpG hr'H
  -- the isomorphism of Lemma 25.5 at the shrunk pair, and its inverse
  obtain ⟨ψ', hiso', -, hfil', hsupp'⟩ :=
    hgen _ _ hdata3 (fun z hz ↦ (mem_inter_iff.mp (hpsub z hz)).2) hpG
  -- the complementary cones, by relative homogeneity below `ξ`
  obtain ⟨n, hn, α, hα, hξα, hωα, β, hmemw⟩ := hwhigh
  obtain ⟨n', hn', α', hα', hξα', hωα', β', hmemr'⟩ := hr'high
  obtain ⟨g, hg, hgsupp⟩ :=
    levy_exists_complement_cone_isomorphism_supportValues (K := (ω : V) ×ˢ (ω : V))
      (E := range s) hAC hξ hwP hn hα hξα hωα hmemw hpB (subset_refl _)
      hr'P hn' hα' hξα' hωα' hmemr' hdata3.2.1 (fun z hz ↦ (mem_inter_iff.mp hz).2) hdet
  refine ⟨coneRegular (levyCollapse κ) (levyOrder κ) w, hpB, _, hdata3.2.1,
    converseGraph ψ', g, isForcingIsomorphism_inverse hiso', hg, hpG, hq0H,
    ForcingContext.filterTransfer_inverse (A := levyContext κ hG) hpB hiso' hfil',
    fun a ha ↦ ⟨?_, hgsupp a ha⟩⟩
  have hareg : IsForcingRegular (levyCollapse κ) (levyOrder κ) a :=
    (mem_regularSets_iff _ _ _).mp
      (supportValuesBase_subset_regularSets (levyContext κ hG).order _ _ _ a ha)
  exact coneImage_inverse hiso' hdata3.2.1 hareg (hsupp' a ha)

include hAC hU hc hω hκ in
/-- The cone hypothesis of the Solovay corollary for the Levy collapse and a finite support
sequence, with no open hypothesis. The ordinal `ξ < κ` below which all base support values are
determined comes from `levy_exists_determined_below_finite_support`. -/
theorem levy_coneOrbitTransfer_finite {s n : V} (hn : n ∈ (ω : V))
    (hsf : IsFunction s) (hsdom : domain s = n) :
    (levyContext κ hG).ConeOrbitTransfer groundFormula s n (solovayParam κ hG) := by
  have hnfin : IsInternallyFinite n := ⟨n, hn, CardLE.refl n, CardLE.refl n⟩
  have hsfin : IsInternallyFinite s := internallyFinite_function (by rw [hsdom]; exact hnfin)
  have hrfin : IsInternallyFinite (range s) := internallyFinite_range hsfin
  obtain ⟨ξ, hξ, hdet⟩ := levy_exists_determined_below_finite_support hAC hU hc hω hκ hrfin
  exact levy_coneOrbitTransfer_of_determined hAC hU hc hω hκ hG hξ hsf hsdom hdet

end

end ZFVP
