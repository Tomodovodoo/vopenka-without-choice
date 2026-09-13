import ZFVP.ModelTheory.SolovayOrbitDefinable
import ZFVP.ModelTheory.GenericFilterModel

/-! Filters of the extension on the checked Boolean completion, and what has to be proved to get
the transfer statement of Karagila and Schilhan, Lemma 9.3 (Jech, Set Theory, Lemma 25.5).

A filter `H` of `V[G]` on the checked completion `B̌`, `B = booleanConditions P R`, that is an
antichain-generic ultrafilter relative to the checked maximal antichains is exactly a `B`-generic
filter over the ground model: `filterTrace_externalGeneric` turns the five internal clauses into
`IsExternalForcingGeneric B (booleanOrder P R)` for the ground set of conditions whose checks lie
in `H`. This is the step that lets one speak of `V[H]` at all.

The map `π` of the classical proof is the ground function `b ↦ ‖b̌ ∈ Ḣ‖` for a ground name `Ḣ`
of `H`; here it is `booleanValueFamily` and `exists_booleanValueFamily` records what it does:
`b̌ ∈ H` holds exactly when the generic meets `π b`. So the map is available as a ground set
function on all of `B` together with its defining property.

What the transfer statement asks for is not this map but a ground automorphism `π` of `B` with
`H = π"G`. `orbitTransfer_iff_pointwise` reduces that image equation to the pointwise statement
`π b ∈ H ↔ b ∈ G` for `b ∈ B`, which is the form in which the classical proof produces it.
The step that is not carried out here is the one that produces the automorphism: that the map
`b ↦ ‖b̌ ∈ Ḣ‖` is a complete automorphism of `B`. See the module docstring of
`ZFVP/ModelTheory/LevyGaloisFactor.lean` for the other route and its own gap. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable {A : ForcingContext V}

/-! ### Filters of the extension on the checked completion -/

/-- A collection of checked regular sets all of whose members are nonempty is a collection of
checked Boolean conditions. -/
theorem subset_check_booleanConditions_of_clauses {H : A.Model}
    (h1 : ∀ u ∈ H, u ∈ A.check (regularSets A.P A.R)) (h4 : ∀ u ∈ H, ∃ z, z ∈ u) :
    H ⊆ A.check (booleanConditions A.P A.R) := by
  intro u hu
  obtain ⟨u₀, hu₀, rfl⟩ := (A.mem_check_iff _ _).mp (h1 u hu)
  obtain ⟨z, hz⟩ := h4 _ hu
  obtain ⟨z₀, hz₀, rfl⟩ := (A.mem_check_iff _ _).mp hz
  exact (A.check_mem_iff _ _).mpr ((mem_booleanConditions_iff _ _ _).mpr
    ⟨(mem_regularSets_iff _ _ _).mp hu₀, z₀, hz₀⟩)

/-- An antichain-generic ultrafilter of the extension on the checked regular sets, containing the
checked top, is the check of a `B`-generic filter over the ground model: the ground conditions
whose checks lie in `H` form a generic filter on the Boolean completion. The internal clause of
meeting every checked maximal antichain gives genericity, because with choice every dense subset
of the completion contains a maximal antichain. -/
theorem filterTrace_externalGeneric (hAC : InternalChoice V) {H : A.Model}
    (h1 : ∀ u ∈ H, u ∈ A.check (regularSets A.P A.R))
    (h2 : ∀ u ∈ H, ∀ u' ∈ A.check (regularSets A.P A.R), u ⊆ u' → u' ∈ H)
    (h3 : ∀ u ∈ H, ∀ u' ∈ H, u ∩ u' ∈ H)
    (h4 : ∀ u ∈ H, ∃ z, z ∈ u)
    (h5 : ∀ Y ∈ A.check (boolMaximalAntichains A.P A.R), ∃ a ∈ Y, a ∈ H)
    (h6 : A.check A.P ∈ H) :
    IsExternalForcingGeneric (booleanConditions A.P A.R) (booleanOrder A.P A.R)
      (A.filterTrace (H := H)) := by
  have hsub : H ⊆ A.check (booleanConditions A.P A.R) :=
    subset_check_booleanConditions_of_clauses h1 h4
  have hmem : ∀ b : V, A.check b ∈ H → b ∈ booleanConditions A.P A.R := by
    intro b hb
    exact (A.check_mem_iff _ _).mp (hsub _ hb)
  refine ⟨⟨fun b hb ↦ hmem b hb, ⟨A.P, h6⟩, ?_, ?_⟩, ?_⟩
  · intro b hb c hc hbc
    obtain ⟨-, -, hsubbc⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hbc
    refine h2 _ hb _ ?_ ((A.checkEmbedding.subset_iff _ _).mpr hsubbc)
    exact (A.check_mem_iff _ _).mpr ((mem_regularSets_iff _ _ _).mpr (booleanConditions_regular hc))
  · intro b hb c hc
    have hinter : A.check (b ∩ c) ∈ H := by
      rw [A.check_inter]
      exact h3 _ hb _ hc
    have hbc : b ∩ c ∈ booleanConditions A.P A.R := hmem _ hinter
    exact ⟨b ∩ c, hinter, (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨hbc, hmem b hb, fun z hz ↦ (mem_inter_iff.mp hz).1⟩,
      (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨hbc, hmem c hc, fun z hz ↦ (mem_inter_iff.mp hz).2⟩⟩
  · intro D hD
    have hdense : ∀ b ∈ booleanConditions A.P A.R, ∃ d ∈ D, d ⊆ b := by
      intro b hb
      obtain ⟨d, hd, hdb⟩ := hD.2 b hb
      exact ⟨d, hd, ((kpair_mem_booleanOrder_iff _ _ _ _).mp hdb).2.2⟩
    obtain ⟨M, hM⟩ := exists_maximalAntichain (booleanOrder_poset A.P A.R).1 hD.1
      (wellOrderable_of_internalChoice hAC D)
    have hMA : M ∈ boolMaximalAntichains A.P A.R :=
      maximalAntichainIn_dense_mem A.order hD.1 hdense hM
    obtain ⟨a, ha, haH⟩ := h5 (A.check M) ((A.check_mem_iff _ _).mpr hMA)
    obtain ⟨a₀, ha₀, rfl⟩ := (A.mem_check_iff _ _).mp ha
    exact ⟨a₀, haH, hM.2.1 a₀ ha₀⟩

/-- The clauses of the previous theorem are satisfiable: the generic ultrafilter of the extension
satisfies them, and the filter it traces out is the generic filter on the completion. -/
theorem filterTrace_boolGenericSet_externalGeneric (hAC : InternalChoice V)
    (A : ForcingContext V) :
    IsExternalForcingGeneric (booleanConditions A.P A.R) (booleanOrder A.P A.R)
      (A.filterTrace (H := A.boolGenericSet)) := by
  have hgen := A.boolGenericSet_antichainGeneric
  refine filterTrace_externalGeneric hAC hgen.subset hgen.upward hgen.inter (fun u hu ↦ ?_)
    hgen.meets A.check_top_mem_boolGenericSet
  obtain ⟨-, q, -, hq⟩ := mem_sep_iff.mp hu
  exact ⟨q, hq⟩

/-! ### The ground map `b ↦ ‖b̌ ∈ Ḣ‖` -/

/-- Every set of the extension is the value of a ground name, and for a ground name `τ` the
membership of a checked set in that value is decided by the Boolean value `‖b̌ ∈ τ‖`, a regular
set of the ground poset met by the generic. This is the map `π` of Jech, Lemma 25.5, as a
definable map of the ground model. -/
theorem exists_booleanValueFamily (A : ForcingContext V) (H : A.Model) :
    ∃ τ : V, IsForcingName (booleanConditions A.P A.R) τ ∧
      ∀ b : V, (A.check b ∈ H ↔ ∃ p ∈ A.G, p ∈ A.booleanMemValue τ b) := by
  obtain ⟨τ, hτ⟩ := A.booleanContext.ofName_surjective (A.booleanEquiv H)
  have hH : A.booleanReal τ = H := by
    unfold booleanReal
    rw [hτ, Equiv.symm_apply_apply]
  refine ⟨τ.val, τ.property, fun b ↦ ?_⟩
  rw [A.booleanMemValue_meets τ b, ← A.check_mem_booleanReal_iff τ b, hH]

/-- The same map, packaged as a ground function on any ground set of conditions. -/
theorem exists_ground_valueMap (A : ForcingContext V) (H : A.Model) (Q : V) :
    ∃ f : V, f ∈ regularSets A.P A.R ^ Q ∧
      ∀ b ∈ Q, (A.check b ∈ H ↔ ∃ p ∈ A.G, p ∈ f ‘ b) := by
  obtain ⟨τ, -, hτ⟩ := A.exists_booleanValueFamily H
  refine ⟨A.booleanValueFamily τ Q, A.booleanValueFamily_mem_function τ Q, fun b hb ↦ ?_⟩
  rw [A.booleanValueFamily_value hb]
  exact hτ b

/-! ### The image of the generic under a ground automorphism -/

/-- The image of the generic ultrafilter under the check of a ground automorphism of the
completion, read off elementwise. -/
theorem mem_range_check_restrict_iff {π : V}
    (hπ : IsForcingAutomorphism (booleanConditions A.P A.R) (booleanOrder A.P A.R) π)
    (z : A.Model) :
    z ∈ range ((A.check π) ↾ A.boolGenericSet) ↔
      ∃ b ∈ booleanConditions A.P A.R, A.check b ∈ A.boolGenericSet ∧ z = A.check (π ‘ b) := by
  have : IsFunction π := IsFunction.of_mem hπ.1
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := mem_range_iff.mp hz
    obtain ⟨hwπ, hwG⟩ := kpair_mem_restrict_iff.mp hw
    obtain ⟨u, hu, hue⟩ := (A.mem_check_iff π _).mp hwπ
    obtain ⟨b, hb, c, hc, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hπ.1 u hu)
    rw [A.check_kpair] at hue
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hue.symm
    exact ⟨b, hb, hwG, (value_eq_of_kpair_mem hu).symm ▸ rfl⟩
  · rintro ⟨b, hb, hbG, rfl⟩
    have hpair : (⟨b, π ‘ b⟩ₖ : V) ∈ π :=
      kpair_value_mem (by rw [domain_eq_of_mem_function hπ.1]; exact hb)
    refine mem_range_of_kpair_mem (x := A.check b) (kpair_mem_restrict_iff.mpr ⟨?_, hbG⟩)
    rw [← A.check_kpair]
    exact (A.check_mem_iff _ _).mpr hpair

/-- The image equation `H = π"G` of the transfer statement is the pointwise statement that `π b`
lies in `H` exactly when `b` lies in the generic. -/
theorem eq_range_check_restrict_iff {π : V}
    (hπ : IsForcingAutomorphism (booleanConditions A.P A.R) (booleanOrder A.P A.R) π)
    {H : A.Model} (hH : H ⊆ A.check (booleanConditions A.P A.R)) :
    H = range ((A.check π) ↾ A.boolGenericSet) ↔
      ∀ b ∈ booleanConditions A.P A.R,
        (A.check (π ‘ b) ∈ H ↔ A.check b ∈ A.boolGenericSet) := by
  have : IsFunction π := IsFunction.of_mem hπ.1
  constructor
  · intro he b hb
    rw [he, mem_range_check_restrict_iff hπ]
    constructor
    · rintro ⟨b', hb', hb'G, heq⟩
      have : π ‘ b' = π ‘ b := (A.check_eq_iff _ _).mp heq.symm
      rwa [injective_value_eq hπ.1 hπ.2.1 hb' hb this] at hb'G
    · intro hbG
      exact ⟨b, hb, hbG, rfl⟩
  · intro hpt
    apply mem_ext
    intro z
    rw [mem_range_check_restrict_iff hπ]
    constructor
    · intro hz
      obtain ⟨c, hc, rfl⟩ := (A.mem_check_iff _ _).mp (hH z hz)
      obtain ⟨b, hb, hbc⟩ := forcingAutomorphism_surjective hπ c hc
      exact ⟨b, hb, (hpt b hb).mp (by rw [hbc]; exact hz), by rw [hbc]⟩
    · rintro ⟨b, hb, hbG, rfl⟩
      exact (hpt b hb).mpr hbG

/-! ### The transfer statement in pointwise form -/

/-- Every filter of the extension satisfying the orbit clauses consists of checked Boolean
conditions. -/
theorem subset_check_booleanConditions_of_isOrbitFilter {Pf : SetTheorySemisentence 2}
    {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H) :
    H ⊆ A.check (booleanConditions A.P A.R) :=
  subset_check_booleanConditions_of_clauses hH.1 hH.2.2.2.1

/-- The transfer statement of Karagila and Schilhan, Lemma 9.3, in pointwise form: instead of
asking for the image equation `H = π"G` one asks that `π b` lie in `H` exactly for the `b` of the
generic. The two are the same statement. -/
theorem orbitTransfer_iff_pointwise (A : ForcingContext V) (Pf : SetTheorySemisentence 2)
    (s k : V) (p : A.Model) :
    A.OrbitTransfer Pf s k p ↔
      ∀ H : A.Model, IsOrbitFilter Pf (A.check (regularSets A.P A.R))
          (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
          (A.orbitSupportReal s k) p H →
        ∃ π ∈ forcedStabilizer (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R)) (range s),
          ∀ b ∈ booleanConditions A.P A.R,
            (A.check (π ‘ b) ∈ H ↔ A.check b ∈ A.boolGenericSet) := by
  constructor
  · intro htr H hH
    obtain ⟨π, hπE, he⟩ := htr H hH
    have hπ : IsForcingAutomorphism (booleanConditions A.P A.R) (booleanOrder A.P A.R) π :=
      (mem_forcingAutomorphisms_iff _ _ _).mp (mem_sep_iff.mp hπE).1
    exact ⟨π, hπE, (eq_range_check_restrict_iff hπ (subset_check_booleanConditions_of_isOrbitFilter hH)).mp he⟩
  · intro hpt H hH
    obtain ⟨π, hπE, hb⟩ := hpt H hH
    have hπ : IsForcingAutomorphism (booleanConditions A.P A.R) (booleanOrder A.P A.R) π :=
      (mem_forcingAutomorphisms_iff _ _ _).mp (mem_sep_iff.mp hπE).1
    exact ⟨π, hπE, (eq_range_check_restrict_iff hπ (subset_check_booleanConditions_of_isOrbitFilter hH)).mpr hb⟩

/-! ### What is left of the transfer statement -/

/-- If a ground function agrees on the completion with the Boolean-value map of a name of `H`,
then the membership of a checked condition in `H` is the membership of its image in the generic
ultrafilter. -/
theorem check_mem_boolGenericSet_of_valueMap {τ : V} {H : A.Model}
    (hval : ∀ b : V, (A.check b ∈ H ↔ ∃ q ∈ A.G, q ∈ A.booleanMemValue τ b)) {f : V}
    (hf : f ∈ booleanConditions A.P A.R ^ booleanConditions A.P A.R)
    (hfv : ∀ b ∈ booleanConditions A.P A.R, f ‘ b = A.booleanMemValue τ b) :
    ∀ b ∈ booleanConditions A.P A.R, (A.check b ∈ H ↔ A.check (f ‘ b) ∈ A.boolGenericSet) := by
  intro b hb
  have hreg : f ‘ b ∈ regularSets A.P A.R :=
    (mem_regularSets_iff _ _ _).mpr (booleanConditions_regular (function_value_mem hf hb))
  rw [hval b, A.check_mem_boolGenericSet_iff, hfv b hb]
  exact ⟨fun h ↦ ⟨hfv b hb ▸ hreg, h⟩, fun h ↦ h.2⟩

/-- What is left of the transfer statement of Karagila and Schilhan, Lemma 9.3, once the map of
the classical proof is in place: the statement follows from the assertion that for a ground name
`τ` of the filter `H` the Boolean-value map `b ↦ ‖b̌ ∈ τ‖` is (given by) an automorphism `f` of
the completion whose inverse lies in the forced stabilizer of the support. Nothing else about `H`
is used: the value map is produced by `exists_booleanValueFamily`, and the image equation
`H = π"G` is recovered from the pointwise form with `π = f⁻¹`. -/
theorem orbitTransfer_of_booleanMemValue_automorphism (A : ForcingContext V)
    (Pf : SetTheorySemisentence 2) (s k : V) (p : A.Model)
    (h : ∀ (H : A.Model) (τ : V), IsOrbitFilter Pf (A.check (regularSets A.P A.R))
        (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
        (A.orbitSupportReal s k) p H →
      (∀ b : V, (A.check b ∈ H ↔ ∃ q ∈ A.G, q ∈ A.booleanMemValue τ b)) →
      ∃ f : V, IsForcingAutomorphism (booleanConditions A.P A.R) (booleanOrder A.P A.R) f ∧
        (∀ b ∈ booleanConditions A.P A.R, f ‘ b = A.booleanMemValue τ b) ∧
        converseGraph f ∈ forcedStabilizer (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R)) (range s)) :
    A.OrbitTransfer Pf s k p := by
  rw [A.orbitTransfer_iff_pointwise]
  intro H hH
  obtain ⟨τ, -, hval⟩ := A.exists_booleanValueFamily H
  obtain ⟨f, hf, hfv, hstab⟩ := h H τ hH hval
  refine ⟨converseGraph f, hstab, fun b hb ↦ ?_⟩
  have hmem : (converseGraph f) ‘ b ∈ booleanConditions A.P A.R :=
    function_value_mem (forcingAutomorphism_inverse hf).1 hb
  have hkey := check_mem_boolGenericSet_of_valueMap hval hf.1 hfv _ hmem
  rwa [value_converseGraph_value hf.1 hf.2.1 (hf.2.2.1 ▸ hb)] at hkey

end ForcingContext

end ZFVP
