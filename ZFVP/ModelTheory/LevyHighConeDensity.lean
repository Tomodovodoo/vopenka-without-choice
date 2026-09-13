import ZFVP.ModelTheory.LevyHighCoordinateTrace
import ZFVP.ModelTheory.LevyConeTraceArrangement
import ZFVP.ModelTheory.BooleanOrbitConeIsomorphism

/-! Conditions that use a coordinate in a high column are dense, on both sides.

Fix `ξ ⊆ κ`. Call a condition of `Coll(ω, <κ)` high for `ξ` when it gives a value at a coordinate
`⟨n, α⟩` with `n ∈ ω`, `α ∈ κ`, `ξ ⊆ α` and `ω ⊆ α` (`IsHighLevyCondition`). By
`levy_exists_highCoordinate_extension` every condition extends to a high one, so the high
conditions are dense (`levyHigh_dense`).

Two consequences, one for each of the two filters that show up in Jech 25.5.

* On the side of the generic filter `G`: any condition met by `G` is extended by a high condition
  met by `G` (`levy_exists_high_generic_condition`).

* On the side of an orbit filter `H`: `exists_trace_coneRegular_below` produces, below a nonzero
  Boolean condition `q` of `H`, a condition `r` of the base poset whose regular cone lies inside
  `q` and whose check is in `H`. Cutting the dense set of that proof down to the high conditions
  gives the same with `r` high (`levy_exists_high_trace_coneRegular_below`).

Both are stated so that the pair `(b0, c0)` of Jech 25.5 can be arranged with a high condition on
each side. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### High conditions -/

/-- A condition of `Coll(ω, <κ)` is high for `ξ` when it gives a value at some coordinate
`⟨n, α⟩` whose column `α` lies at or above both `ξ` and `ω`. -/
def IsHighLevyCondition (κ ξ p : V) : Prop :=
  ∃ n, n ∈ (ω : V) ∧ ∃ α, α ∈ κ ∧ ξ ⊆ α ∧ (ω : V) ⊆ α ∧ ∃ β, ⟨⟨n, α⟩ₖ, β⟩ₖ ∈ p

instance isHighLevyCondition_definable (κ ξ : V) :
    ℒₛₑₜ-predicate[V] (IsHighLevyCondition κ ξ) := by
  unfold IsHighLevyCondition
  definability

/-- Being high is inherited by extensions. -/
theorem IsHighLevyCondition.mono {κ ξ p q : V} (h : IsHighLevyCondition κ ξ p) (hpq : p ⊆ q) :
    IsHighLevyCondition κ ξ q := by
  obtain ⟨n, hn, α, hα, hξα, hωα, β, hβ⟩ := h
  exact ⟨n, hn, α, hα, hξα, hωα, β, hpq _ hβ⟩

/-- The high conditions of `Coll(ω, <κ)`. -/
noncomputable def levyHighConditions (κ ξ : V) : V :=
  {p ∈ levyCollapse κ ; IsHighLevyCondition κ ξ p}

theorem mem_levyHighConditions_iff {κ ξ p : V} :
    p ∈ levyHighConditions κ ξ ↔ p ∈ levyCollapse κ ∧ IsHighLevyCondition κ ξ p := by
  rw [levyHighConditions]; exact mem_sep_iff

/-- The high conditions are dense in `Coll(ω, <κ)`. This is
`levy_exists_highCoordinate_extension` read as a density statement. -/
theorem levyHigh_dense {κ ξ : V} [IsOrdinal κ] (hξ : ξ ⊆ κ) (hξκ : ξ ∈ κ) (hω : (ω : V) ∈ κ) :
    ForcingDense (levyCollapse κ) (levyOrder κ) (levyHighConditions κ ξ) := by
  refine ⟨sep_subset, fun p hp ↦ ?_⟩
  obtain ⟨r, hr, hpr, n, α, β, hn, hα, hξα, hωα, hmem⟩ :=
    levy_exists_highCoordinate_extension hξ hξκ hω hp
  exact ⟨r, mem_levyHighConditions_iff.mpr ⟨hr, n, hn, α, hα, hξα, hωα, β, hmem⟩,
    (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hr, hp, hpr⟩⟩

/-! ### The generic side -/

/-- Every condition met by an external generic filter on `Coll(ω, <κ)` is extended by a high
condition met by the same filter. The high conditions are dense, so `G` meets them, and the filter
clause of `G` gives a common extension in `G` of the two; a common extension of a high condition is
high. -/
theorem levy_exists_high_generic_condition {κ ξ w : V} [IsOrdinal κ] (hξ : ξ ⊆ κ) (hξκ : ξ ∈ κ)
    (hω : (ω : V) ∈ κ) {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G) (hw : w ∈ G) :
    ∃ w', w' ∈ G ∧ w' ∈ levyCollapse κ ∧ w ⊆ w' ∧ IsHighLevyCondition κ ξ w' := by
  obtain ⟨r, hrG, hrD⟩ := hG.2 _ (levyHigh_dense hξ hξκ hω)
  obtain ⟨-, hrhigh⟩ := mem_levyHighConditions_iff.mp hrD
  obtain ⟨w', hw'G, hw'w, hw'r⟩ := hG.1.2.2.2 w hw r hrG
  refine ⟨w', hw'G, hG.1.1 w' hw'G, ((pair_mem_reverseInclusionOrder _ _ _).mp hw'w).2.2,
    hrhigh.mono ((pair_mem_reverseInclusionOrder _ _ _).mp hw'r).2.2⟩

/-! ### The orbit filter side -/

namespace ForcingContext

variable {A : ForcingContext V}

/-- `exists_trace_coneRegular_below` with the condition of the base poset taken high.

Below a nonzero Boolean condition `q` of the orbit filter `H` there is a high condition `r'` of
`Coll(ω, <κ)` whose regular cone lies inside `q` and whose check lies in `H`. The proof is the one
of `exists_trace_coneRegular_below` with the dense set cut down: instead of the regular cone of an
arbitrary condition below the given one, take the regular cone of a high extension of it, which is
still inside `q` because regular cones shrink as conditions grow. -/
theorem levy_exists_high_trace_coneRegular_below (hAC : InternalChoice V) {κ ξ : V} [IsOrdinal κ]
    (hP : A.P = levyCollapse κ) (hR : A.R = levyOrder κ) (hξ : ξ ⊆ κ) (hξκ : ξ ∈ κ)
    (hω : (ω : V) ∈ κ)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    {q : V} (hqB : q ∈ booleanConditions A.P A.R) (hqH : A.check q ∈ H) :
    ∃ r' , r' ∈ levyCollapse κ ∧ IsHighLevyCondition κ ξ r' ∧
      coneRegular A.P A.R r' ⊆ q ∧ A.check (coneRegular A.P A.R r') ∈ H := by
  classical
  set D : V := sep (booleanConditions A.P A.R)
    (fun b ↦ (∃ r ∈ A.P, b = coneRegular A.P A.R r ∧ IsHighLevyCondition κ ξ r ∧ b ⊆ q) ∨
      b ∩ q = (∅ : V))
    (by definability) with hDdef
  have hmemD : ∀ b : V, b ∈ D ↔ b ∈ booleanConditions A.P A.R ∧
      ((∃ r ∈ A.P, b = coneRegular A.P A.R r ∧ IsHighLevyCondition κ ξ r ∧ b ⊆ q) ∨
        b ∩ q = (∅ : V)) :=
    fun b ↦ by rw [hDdef]; exact mem_sep_iff
  have hqreg := booleanConditions_regular hqB
  have hDdense : ForcingDense (booleanConditions A.P A.R) (booleanOrder A.P A.R) D := by
    refine ⟨sep_subset, fun u hu ↦ ?_⟩
    have hureg := booleanConditions_regular hu
    by_cases hne : ∃ z : V, z ∈ u ∩ q
    · obtain ⟨z, hz⟩ := hne
      have hzP : z ∈ A.P := hureg.1 z (mem_inter_iff.mp hz).1
      have hzL : z ∈ levyCollapse κ := hP ▸ hzP
      obtain ⟨r, hrL, hzr, n, α, β, hn, hα, hξα, hωα, hrmem⟩ :=
        levy_exists_highCoordinate_extension hξ hξκ hω hzL
      have hrP : r ∈ A.P := by rw [hP]; exact hrL
      have hrz : ⟨r, z⟩ₖ ∈ A.R := by
        rw [hR]
        exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hrL, hzL, hzr⟩
      have hrhigh : IsHighLevyCondition κ ξ r := ⟨n, hn, α, hα, hξα, hωα, β, hrmem⟩
      have hsubz : coneRegular A.P A.R z ⊆ u ∩ q :=
        coneRegular_subset_of_mem A.order (forcingRegular_inter hureg hqreg) hz
      have hsub : coneRegular A.P A.R r ⊆ u ∩ q :=
        SetTheory.subset_trans (coneRegular_subset_coneRegular A.order hzP hrP hrz) hsubz
      refine ⟨coneRegular A.P A.R r, (hmemD _).mpr
        ⟨coneRegular_mem_booleanConditions A.order hrP,
          Or.inl ⟨r, hrP, rfl, hrhigh, fun t ht ↦ (mem_inter_iff.mp (hsub t ht)).2⟩⟩, ?_⟩
      exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨coneRegular_mem_booleanConditions A.order hrP, hu,
          fun t ht ↦ (mem_inter_iff.mp (hsub t ht)).1⟩
    · refine ⟨u, (hmemD u).mpr ⟨hu, Or.inr (mem_ext (fun z ↦
        ⟨fun hz ↦ absurd ⟨z, hz⟩ hne, fun hz ↦ absurd hz not_mem_empty⟩))⟩,
        (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hu, hu, subset_refl _⟩⟩
  have hgen := filterTrace_externalGeneric hAC hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2.1
    hH.2.2.2.2.2.1
  obtain ⟨b, hbT, hbD⟩ := hgen.2 D hDdense
  have hbH : A.check b ∈ H := hbT
  obtain ⟨hbB, hcases⟩ := (hmemD b).mp hbD
  rcases hcases with ⟨r, hrP, rfl, hrhigh, hsub⟩ | hempty
  · exact ⟨r, hP ▸ hrP, hrhigh, hsub, hbH⟩
  · exfalso
    have hinter : A.check (b ∩ q) ∈ H := by
      rw [A.check_inter]
      exact hH.2.2.1 _ hbH _ hqH
    rw [hempty] at hinter
    obtain ⟨z, hz⟩ := hH.2.2.2.1 _ hinter
    rw [A.check_empty] at hz
    exact not_mem_empty hz

end ForcingContext

end ZFVP
