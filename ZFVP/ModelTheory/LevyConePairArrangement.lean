import ZFVP.ModelTheory.LevyConeTraceArrangement
import ZFVP.ModelTheory.LevyOrbitTransferCone
import ZFVP.ModelTheory.LevyBooleanHomogeneity

/-! How far the cone data of Jech, Set Theory, Lemma 25.5 can be shrunk, and why both sides cannot
be regular cones of conditions at once.

`ZFVP/ModelTheory/BooleanOrbitConeIsomorphism.lean` builds, for an orbit filter `H`, a pair of
Boolean conditions `p` (met by the generic) and `q` (with `q̌ ∈ H`) carrying the clauses
`IsOrbitConeData A τ σ p q`, and the two shrinking lemmas say that the clauses survive shrinking on
either side: `orbitConeData_shrink_left` replaces `(p, q)` by `(p₁, ‖p̌₁ ∈ σ‖ ∩ q)` for any Boolean
condition `p₁ ⊆ p`, and `orbitConeData_shrink_right` replaces `(p, q)` by `(‖q̌₁ ∈ τ‖ ∩ p, q₁)` for
any `q₁ ⊆ q`. Each lemma keeps the condition it is told about and recomputes the other one.

The two-step form is `orbitConeData_shrink_left_right`: shrink left to `p₁`, then right to `q₁`, and
the pair is `(‖q̌₁ ∈ τ‖ ∩ p₁, q₁)`. The left condition is a Boolean condition below `p₁` and in
general is not `p₁`. That is the whole obstruction of wave 4, and it is not an artefact of the
proof:

* `orbitConeData_left_unique`. Given `IsOrbitConeData A τ σ p q` and Boolean conditions `p₁ ⊆ p`,
  `q₁ ⊆ q`, the clauses `IsOrbitConeData A τ σ p₁ q₁` hold **exactly when** `‖q̌₁ ∈ τ‖ ∩ p = p₁`.
  So once the condition on the side of the filter is prescribed, the condition on the side of the
  generic is determined: it is the image of `q₁` under the isomorphism. The easy half is
  `orbitConeData_shrink_right`. The other half uses the data at `(p, q)` only: if `‖q̌₁ ∈ τ‖ ∩ p`
  had a part `c` outside `p₁`, the inverse value `d = ‖č ∈ σ‖ ∩ q` would satisfy
  `‖ď ∈ τ‖ ∩ p = c ⊆ ‖q̌₁ ∈ τ‖ ∩ p`, hence `d ⊆ q₁` because the value map reflects inclusion, and
  then the nonvanishing clause of `IsOrbitConeData A τ σ p₁ q₁` would give a condition in
  `c ∩ p₁ ⊆ ¬p₁ ∩ p₁ = ∅`.

Taking both sides to be regular cones of conditions therefore asks that `‖(coneRegular r')ˇ ∈ τ‖`
meet `p` in a regular cone, and nothing in the construction delivers that: the value map is an
isomorphism of cones of the completion, not of the poset, and it need not send the cone of a
condition to the cone of a condition. `ValueOfConeIsCone` is that residue as a single statement,
`valueOfConeIsCone_of_pair` shows it is necessary, and
`exists_orbit_cone_isomorphism_coneRegular_pair` shows it is sufficient: nothing else is missing.

What is proved without the residue:

* `exists_orbitConeData_coneRegular_pair_below` and
  `exists_orbit_cone_isomorphism_coneRegular_right_below`: the condition on the side of the filter
  can be taken to be a regular cone `coneRegular r'` with `(coneRegular r')ˇ ∈ H`, and then the
  condition on the side of the generic is a Boolean condition met by the generic and contained in
  the regular cone `coneRegular r` of a condition `r` of the generic filter. This is
  `exists_orbit_cone_isomorphism_coneRegular_right` with the extra information that the left
  condition sits inside a cone of the generic filter.
* `exists_orbitConeData_coneRegular_left_of_data`: below the left condition there is always a
  regular cone (`exists_coneRegular_subset`), and shrinking to it keeps the clauses. So either side
  alone can be normalized at any time; only the pair cannot.

The last section proves a density fact for a later wave, about the Levy collapse rather than the
completion. `exists_common_domain_extensions` normalizes two conditions to a common domain by
filling each one in on the coordinates the other uses. That construction already keeps agreement:
outside `domain r ∩ domain r'` the two extensions take the same value by construction, so if `r`
and `r'` agree on the overlap inside `ω × ξ` then the extensions agree on `ω × ξ`.
`levy_exists_common_domain_extensions_agreeing` states that, and adds the automorphism
`levySwapAutomorphism κ r₁ r₁'` that carries the one extension to the other.

`InternalChoice V` enters only through `exists_orbitConeData` and `exists_trace_coneRegular_below`.
The Levy section uses no choice. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable {A : ForcingContext V}

/-! ### The left condition is determined by the right one -/

/-- Given the clauses at `(p, q)`, the clauses at a pair of smaller conditions `p₁ ⊆ p`, `q₁ ⊆ q`
hold exactly when `p₁` is the value of `q₁` cut down to `p`. One direction is
`orbitConeData_shrink_right`; the other says that no other choice of `p₁` works. -/
theorem orbitConeData_left_unique {τ σ p q p₁ q₁ : V} (hdata : A.IsOrbitConeData τ σ p q)
    (hp₁ : p₁ ∈ booleanConditions A.P A.R) (hp₁p : p₁ ⊆ p)
    (hq₁ : q₁ ∈ booleanConditions A.P A.R) (hq₁q : q₁ ⊆ q) :
    A.IsOrbitConeData τ σ p₁ q₁ ↔ A.booleanMemValue τ q₁ ∩ p = p₁ := by
  constructor
  · intro hdata₁
    have hbreg : IsForcingRegular A.P A.R (A.booleanMemValue τ q₁ ∩ p) :=
      forcingRegular_inter (A.booleanMemValue_regular τ q₁) (booleanConditions_regular hdata.1)
    have hp₁reg := booleanConditions_regular hp₁
    refine SetTheory.subset_antisymm ?_ (fun z hz ↦
      mem_inter_iff.mpr ⟨hdata₁.2.2.2.2.2.2.1 z hz, hp₁p z hz⟩)
    by_contra hsub
    obtain ⟨z₀, hz₀b, hz₀p₁⟩ : ∃ z : V, z ∈ A.booleanMemValue τ q₁ ∩ p ∧ z ∉ p₁ := by
      by_contra hcon
      exact hsub (fun z hz ↦ by
        by_contra hzp
        exact hcon ⟨z, hz, hzp⟩)
    have hz₀P : z₀ ∈ A.P := hbreg.1 z₀ hz₀b
    obtain ⟨t, htn, htz⟩ := exists_forcingNegation_of_not_mem hz₀P hz₀p₁ hp₁reg.2.2
    have htP : t ∈ A.P := forcingNegation_subset _ _ _ t htn
    have htb : t ∈ A.booleanMemValue τ q₁ ∩ p := hbreg.2.1 z₀ hz₀b t htP htz
    set c : V := (A.booleanMemValue τ q₁ ∩ p) ∩ forcingNegation A.P A.R p₁ with hcdef
    have hcreg : IsForcingRegular A.P A.R c :=
      forcingRegular_inter hbreg (forcingNegation_regular A.order hp₁reg.2.1)
    have hcB : c ∈ booleanConditions A.P A.R :=
      (mem_booleanConditions_iff _ _ _).mpr ⟨hcreg, t, mem_inter_iff.mpr ⟨htb, htn⟩⟩
    have hcp : c ⊆ p := fun z hz ↦ (mem_inter_iff.mp (mem_inter_iff.mp hz).1).2
    obtain ⟨hdB, hdq, hdval⟩ := A.orbitConeData_inverse_value hdata hcB hcp
    set d : V := A.orbitInverseValue σ c ∩ q with hddef
    have hdq₁ : d ⊆ q₁ := by
      refine A.orbitConeData_subset_of_value_subset hdata hdB hq₁ hdq (fun z hz ↦ ?_)
      rw [hdval] at hz
      exact (mem_inter_iff.mp hz).1
    obtain ⟨y, hy⟩ := hdata₁.2.2.2.2.2.2.2 d hdB hdq₁
    obtain ⟨hyv, hyp₁⟩ := mem_inter_iff.mp hy
    have hyc : y ∈ c := by
      rw [← hdval]
      exact mem_inter_iff.mpr ⟨hyv, hp₁p y hyp₁⟩
    have hemp := inter_forcingNegation_eq_empty A.order hp₁reg.1
    rw [SetTheory.mem_ext_iff] at hemp
    exact not_mem_empty ((hemp y).mp (mem_inter_iff.mpr ⟨hyp₁, (mem_inter_iff.mp hyc).2⟩))
  · intro h
    have hstep := A.orbitConeData_shrink_right hdata hq₁ hq₁q
    rwa [h] at hstep

/-! ### Shrinking on the left and then on the right -/

/-- The two shrinking lemmas in sequence. Shrink to a Boolean condition `p₁ ⊆ p` on the side of the
generic, then to a Boolean condition `q₁` below the matching condition `‖p̌₁ ∈ σ‖ ∩ q` on the side
of the filter. All eight clauses survive, and the resulting pair is `(‖q̌₁ ∈ τ‖ ∩ p₁, q₁)`.

Nothing in the clauses breaks. What the second step breaks is the choice made in the first: the
left condition is no longer `p₁` but a Boolean condition below it, and by the last clause it is
`p₁` again exactly when `p₁ ⊆ ‖q̌₁ ∈ τ‖`. -/
theorem orbitConeData_shrink_left_right {τ σ p q p₁ q₁ : V} (hdata : A.IsOrbitConeData τ σ p q)
    (hp₁ : p₁ ∈ booleanConditions A.P A.R) (hp₁p : p₁ ⊆ p)
    (hq₁ : q₁ ∈ booleanConditions A.P A.R)
    (hq₁q : q₁ ⊆ A.orbitInverseValue σ p₁ ∩ q) :
    A.IsOrbitConeData τ σ p₁ (A.orbitInverseValue σ p₁ ∩ q) ∧
      A.IsOrbitConeData τ σ (A.booleanMemValue τ q₁ ∩ p₁) q₁ ∧
      A.booleanMemValue τ q₁ ∩ p₁ ⊆ p₁ ∧
      (A.IsOrbitConeData τ σ p₁ q₁ ↔ A.booleanMemValue τ q₁ ∩ p₁ = p₁) := by
  have hleft := A.orbitConeData_shrink_left hdata hp₁ hp₁p
  exact ⟨hleft, A.orbitConeData_shrink_right hleft hq₁ hq₁q,
    fun z hz ↦ (mem_inter_iff.mp hz).2,
    A.orbitConeData_left_unique hleft hp₁ (subset_refl _) hq₁ hq₁q⟩

/-- Either side alone can be normalized to a regular cone at any time: below the condition on the
side of the generic there is the regular cone of a condition of the poset, and shrinking to it
keeps the clauses. -/
theorem exists_orbitConeData_coneRegular_left_of_data {τ σ p q : V}
    (hdata : A.IsOrbitConeData τ σ p q) :
    ∃ r ∈ A.P, coneRegular A.P A.R r ⊆ p ∧
      A.IsOrbitConeData τ σ (coneRegular A.P A.R r)
        (A.orbitInverseValue σ (coneRegular A.P A.R r) ∩ q) := by
  obtain ⟨r, hrP, hsub⟩ := exists_coneRegular_subset A.order hdata.1
  exact ⟨r, hrP, hsub,
    A.orbitConeData_shrink_left hdata (coneRegular_mem_booleanConditions A.order hrP) hsub⟩

/-! ### The best pair that is available -/

/-- The two-step shrink for the data of Lemma 25.5. The condition on the side of the filter is the
regular cone of a condition of the poset, with its check in the filter; the condition on the side of
the generic is met by the generic and sits inside the regular cone of a condition `r` of the generic
filter, but is itself only a Boolean condition, namely the value of the cone on the right. -/
theorem exists_orbitConeData_coneRegular_pair_below (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a) :
    ∃ τ σ r r' : V, r ∈ A.G ∧ r' ∈ A.P ∧
      (∀ b : V, (A.check b ∈ H ↔ ∃ t ∈ A.G, t ∈ A.booleanMemValue τ b)) ∧
      A.check (coneRegular A.P A.R r') ∈ H ∧
      A.booleanMemValue τ (coneRegular A.P A.R r') ∩ coneRegular A.P A.R r ∈
        booleanConditions A.P A.R ∧
      A.booleanMemValue τ (coneRegular A.P A.R r') ∩ coneRegular A.P A.R r ⊆
        coneRegular A.P A.R r ∧
      (∃ t ∈ A.G, t ∈ A.booleanMemValue τ (coneRegular A.P A.R r') ∩ coneRegular A.P A.R r) ∧
      A.IsOrbitConeData τ σ
        (A.booleanMemValue τ (coneRegular A.P A.R r') ∩ coneRegular A.P A.R r)
        (coneRegular A.P A.R r') := by
  obtain ⟨τ, σ, p₀, q₀, hval, hd, hp₀G, hq₀H, hdata⟩ := exists_orbitConeData hAC hH hPf
  obtain ⟨r, hrG, hrp⟩ := hp₀G
  have hrP : r ∈ A.P := A.generic.1.1 r hrG
  have hp'B : coneRegular A.P A.R r ∈ booleanConditions A.P A.R :=
    coneRegular_mem_booleanConditions A.order hrP
  have hp'p : coneRegular A.P A.R r ⊆ p₀ :=
    coneRegular_subset_of_mem A.order (booleanConditions_regular hdata.1) hrp
  have hp'G : ∃ t ∈ A.G, t ∈ coneRegular A.P A.R r :=
    ⟨r, hrG, self_mem_coneRegular A.order hrP⟩
  have hleft := A.orbitConeData_shrink_left hdata hp'B hp'p
  have hq'H := A.check_orbitInverseValue_inter_mem hH.2.2.1 hd hp'B hp'G hq₀H
  obtain ⟨r', hr'P, hr'q, hr'H⟩ := exists_trace_coneRegular_below hAC hH hleft.2.1 hq'H
  have hq'B : coneRegular A.P A.R r' ∈ booleanConditions A.P A.R :=
    coneRegular_mem_booleanConditions A.order hr'P
  have hdata' := A.orbitConeData_shrink_right hleft hq'B hr'q
  refine ⟨τ, σ, r, r', hrG, hr'P, hval, hr'H, hdata'.1,
    fun z hz ↦ (mem_inter_iff.mp hz).2, ?_, hdata'⟩
  exact meets_inter (A.booleanMemValue_regular τ _) (booleanConditions_regular hp'B)
    ((hval _).mp hr'H) hp'G

/-- Lemma 25.5 with the condition on the side of the filter a regular cone, and the condition on the
side of the generic inside the regular cone of a condition of the generic filter. -/
theorem exists_orbit_cone_isomorphism_coneRegular_right_below (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a) :
    ∃ r ∈ A.G, ∃ r' ∈ A.P, ∃ p₁ ∈ booleanConditions A.P A.R, ∃ ψ : V,
      p₁ ⊆ coneRegular A.P A.R r ∧ (∃ t ∈ A.G, t ∈ p₁) ∧
      A.check (coneRegular A.P A.R r') ∈ H ∧
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (coneRegular A.P A.R r'))
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (coneRegular A.P A.R r')))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p₁)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p₁)) ψ ∧
      ∀ c ∈ booleanConditions A.P A.R, c ⊆ coneRegular A.P A.R r' →
        (A.check c ∈ H ↔ A.check (ψ ‘ c) ∈ A.boolGenericSet) := by
  obtain ⟨τ, σ, r, r', hrG, hr'P, hval, hr'H, hp₁B, hp₁sub, hp₁G, hdata⟩ :=
    exists_orbitConeData_coneRegular_pair_below hAC hH hPf
  obtain ⟨ψ, hiso, htr, -⟩ := A.exists_cone_isomorphism_of_data hdata hval hp₁G
  exact ⟨r, hrG, r', hr'P, _, hp₁B, ψ, hp₁sub, hp₁G, hr'H, hiso, htr⟩

/-! ### The residue -/

/-- The statement that is left open, and by `orbitConeData_left_unique` the only one that is left
open: below the condition `q` on the side of the filter there is a regular cone `coneRegular r'`
whose check is in the filter and whose value meets `p` in a regular cone.

`valueOfConeIsCone_of_pair` shows the condition is necessary, and
`exists_orbit_cone_isomorphism_coneRegular_pair` shows it is sufficient for both conditions of
Lemma 25.5 to be regular cones of conditions of the poset. What would close it is a lemma saying
that the value map `b ↦ ‖b̌ ∈ τ‖ ∩ p` sends the cone of some condition below `q` to the cone of a
condition. The value map is an isomorphism of cones of the completion, which does not by itself say
anything about cones of the poset. -/
def ValueOfConeIsCone (A : ForcingContext V) (H : A.Model) (τ p q : V) : Prop :=
  ∃ r' ∈ A.P, coneRegular A.P A.R r' ⊆ q ∧ A.check (coneRegular A.P A.R r') ∈ H ∧
    ∃ r ∈ A.P, A.booleanMemValue τ (coneRegular A.P A.R r') ∩ p = coneRegular A.P A.R r

/-- The residue is necessary. If the clauses hold at a pair of regular cones below `(p, q)`, then
the value of the cone on the right meets `p` in the cone on the left. -/
theorem valueOfConeIsCone_of_pair {τ σ p q r r' : V} (hdata : A.IsOrbitConeData τ σ p q)
    (hrP : r ∈ A.P) (hr'P : r' ∈ A.P) (hrp : coneRegular A.P A.R r ⊆ p)
    (hr'q : coneRegular A.P A.R r' ⊆ q)
    (hpair : A.IsOrbitConeData τ σ (coneRegular A.P A.R r) (coneRegular A.P A.R r')) :
    A.booleanMemValue τ (coneRegular A.P A.R r') ∩ p = coneRegular A.P A.R r :=
  (A.orbitConeData_left_unique hdata (coneRegular_mem_booleanConditions A.order hrP) hrp
    (coneRegular_mem_booleanConditions A.order hr'P) hr'q).mp hpair

/-- The residue is sufficient. From `ValueOfConeIsCone` at the data of Lemma 25.5, both conditions
are regular cones of conditions of the poset: the cone on the left is met by the generic, the check
of the cone on the right is in the filter, and the isomorphism carries the one filter to the
other. -/
theorem exists_orbit_cone_isomorphism_coneRegular_pair (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a)
    (hres : ∀ τ σ p₀ q₀ : V, A.IsOrbitConeData τ σ p₀ q₀ →
      (∀ b : V, (A.check b ∈ H ↔ ∃ t ∈ A.G, t ∈ A.booleanMemValue τ b)) →
      (∃ t ∈ A.G, t ∈ p₀) → A.check q₀ ∈ H → A.ValueOfConeIsCone H τ p₀ q₀) :
    ∃ r ∈ A.P, ∃ r' ∈ A.P, ∃ ψ : V,
      (∃ t ∈ A.G, t ∈ coneRegular A.P A.R r) ∧ A.check (coneRegular A.P A.R r') ∈ H ∧
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (coneRegular A.P A.R r'))
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (coneRegular A.P A.R r')))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
          (coneRegular A.P A.R r))
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R)
            (coneRegular A.P A.R r))) ψ ∧
      ∀ c ∈ booleanConditions A.P A.R, c ⊆ coneRegular A.P A.R r' →
        (A.check c ∈ H ↔ A.check (ψ ‘ c) ∈ A.boolGenericSet) := by
  obtain ⟨τ, σ, p₀, q₀, hval, -, hp₀G, hq₀H, hdata⟩ := exists_orbitConeData hAC hH hPf
  obtain ⟨r', hr'P, hr'q, hr'H, r, hrP, hvalue⟩ := hres τ σ p₀ q₀ hdata hval hp₀G hq₀H
  have hq'B : coneRegular A.P A.R r' ∈ booleanConditions A.P A.R :=
    coneRegular_mem_booleanConditions A.order hr'P
  have hdata' := A.orbitConeData_shrink_right hdata hq'B hr'q
  rw [hvalue] at hdata'
  have hp'G : ∃ t ∈ A.G, t ∈ coneRegular A.P A.R r := by
    rw [← hvalue]
    exact meets_inter (A.booleanMemValue_regular τ _) (booleanConditions_regular hdata.1)
      ((hval _).mp hr'H) hp₀G
  obtain ⟨ψ, hiso, htr, -⟩ := A.exists_cone_isomorphism_of_data hdata' hval hp'G
  exact ⟨r, hrP, r', hr'P, ψ, hp'G, hr'H, hiso, htr⟩

end ForcingContext

/-! ### Common domains keeping agreement below an ordinal -/

section Levy

variable {κ : V}

/-- Two conditions of the Levy collapse with the same domain are carried to each other by the swap
automorphism, named. -/
theorem levy_swapAutomorphism_of_domain_eq {r r' : V} (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ) (hdom : domain r = domain r') :
    IsForcingAutomorphism (levyCollapse κ) (levyOrder κ) (levySwapAutomorphism κ r r') ∧
      (levySwapAutomorphism κ r r') ‘ r = r' := by
  refine ⟨levySwapAutomorphism_isForcingAutomorphism hr hr', ?_⟩
  rw [levySwapAutomorphism_value hr]
  exact levySwapCondition_self (levyCollapse_isFunction hr) (levyCollapse_isFunction hr') hdom

/-- Normalizing two conditions of the Levy collapse to a common domain can be done while keeping
their agreement on `ω × ξ`. Fill each condition in on the coordinates the other uses, copying the
other's value there; the two extensions then agree at every coordinate outside
`domain r ∩ domain r'`, so agreement of `r` and `r'` on the overlap inside `ω × ξ` is enough. The
pair of extensions is carried to itself by `levySwapAutomorphism`. -/
theorem levy_exists_common_domain_extensions_agreeing {ξ r r' : V} (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ)
    (hagree : ∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z) :
    ∃ r₁ r₁' : V, r ⊆ r₁ ∧ r' ⊆ r₁' ∧ r₁ ∈ levyCollapse κ ∧ r₁' ∈ levyCollapse κ ∧
      domain r₁ = domain r₁' ∧
      (∀ z ∈ domain r₁, z ∈ domain r₁' → z ∈ (ω : V) ×ˢ ξ → r₁ ‘ z = r₁' ‘ z) ∧
      IsForcingAutomorphism (levyCollapse κ) (levyOrder κ) (levySwapAutomorphism κ r₁ r₁') ∧
      (levySwapAutomorphism κ r₁ r₁') ‘ r₁ = r₁' := by
  have hrf := levyCollapse_isFunction hr
  have hr'f := levyCollapse_isFunction hr'
  set Aset : V := {w ∈ r' ; kpair.π₁ w ∉ domain r} with hA
  set Bset : V := {w ∈ r ; kpair.π₁ w ∉ domain r'} with hB
  have hA' : Aset ∈ levyCollapse κ := levyCollapse_subset hr' sep_subset
  have hB' : Bset ∈ levyCollapse κ := levyCollapse_subset hr sep_subset
  have h1 : r ∪ Aset ∈ levyCollapse κ := by
    refine levyCollapse_union hr hA' (fun x y z hxy hxz ↦ ?_)
    obtain ⟨-, hnot⟩ := mem_sep_iff.mp hxz
    simp only [kpair.π₁_kpair] at hnot
    exact absurd (mem_domain_of_kpair_mem hxy) hnot
  have h2 : r' ∪ Bset ∈ levyCollapse κ := by
    refine levyCollapse_union hr' hB' (fun x y z hxy hxz ↦ ?_)
    obtain ⟨-, hnot⟩ := mem_sep_iff.mp hxz
    simp only [kpair.π₁_kpair] at hnot
    exact absurd (mem_domain_of_kpair_mem hxy) hnot
  have hdomain : ∀ s t : V, IsFunction s → IsFunction t →
      domain (s ∪ {w ∈ t ; kpair.π₁ w ∉ domain s}) = domain s ∪ domain t := by
    intro s t hs ht
    have := hs
    have := ht
    apply mem_ext
    intro x
    rw [mem_domain_iff, mem_union_iff]
    constructor
    · rintro ⟨y, hy⟩
      rcases mem_union_iff.mp hy with hy | hy
      · exact Or.inl (mem_domain_of_kpair_mem hy)
      · exact Or.inr (mem_domain_of_kpair_mem (mem_sep_iff.mp hy).1)
    · rintro (hx | hx)
      · exact ⟨s ‘ x, mem_union_iff.mpr (Or.inl (kpair_value_mem hx))⟩
      · by_cases hxs : x ∈ domain s
        · exact ⟨s ‘ x, mem_union_iff.mpr (Or.inl (kpair_value_mem hxs))⟩
        · refine ⟨t ‘ x, mem_union_iff.mpr (Or.inr (mem_sep_iff.mpr ⟨kpair_value_mem hx, ?_⟩))⟩
          simpa only [kpair.π₁_kpair] using hxs
  set r₁ : V := r ∪ Aset with hr₁def
  set r₁' : V := r' ∪ Bset with hr₁'def
  have hf1 := levyCollapse_isFunction h1
  have hf2 := levyCollapse_isFunction h2
  have hdom1 : domain r₁ = domain r ∪ domain r' := by
    rw [hr₁def, hA]; exact hdomain r r' inferInstance inferInstance
  have hdom2 : domain r₁' = domain r' ∪ domain r := by
    rw [hr₁'def, hB]; exact hdomain r' r inferInstance inferInstance
  have hdomeq : domain r₁ = domain r₁' := by
    rw [hdom1, hdom2]
    apply mem_ext
    intro x
    simp only [mem_union_iff]
    tauto
  -- values of the two extensions
  have hv1 : ∀ z : V, z ∈ domain r → r₁ ‘ z = r ‘ z := fun z hz ↦
    value_eq_of_kpair_mem (subset_union_left r Aset _ (kpair_value_mem hz))
  have hv2 : ∀ z : V, z ∉ domain r → z ∈ domain r' → r₁ ‘ z = r' ‘ z := by
    intro z hz hz'
    refine value_eq_of_kpair_mem (subset_union_right r Aset _ ?_)
    exact mem_sep_iff.mpr ⟨kpair_value_mem hz', by simpa only [kpair.π₁_kpair] using hz⟩
  have hv1' : ∀ z : V, z ∈ domain r' → r₁' ‘ z = r' ‘ z := fun z hz ↦
    value_eq_of_kpair_mem (subset_union_left r' Bset _ (kpair_value_mem hz))
  have hv2' : ∀ z : V, z ∉ domain r' → z ∈ domain r → r₁' ‘ z = r ‘ z := by
    intro z hz hz'
    refine value_eq_of_kpair_mem (subset_union_right r' Bset _ ?_)
    exact mem_sep_iff.mpr ⟨kpair_value_mem hz', by simpa only [kpair.π₁_kpair] using hz⟩
  refine ⟨r₁, r₁', subset_union_left r Aset, subset_union_left r' Bset, h1, h2, hdomeq,
    fun z hz _ hzω ↦ ?_, levySwapAutomorphism_isForcingAutomorphism h1 h2, ?_⟩
  · by_cases hzr : z ∈ domain r
    · by_cases hzr' : z ∈ domain r'
      · rw [hv1 z hzr, hv1' z hzr']
        exact hagree z hzr hzr' hzω
      · rw [hv1 z hzr, hv2' z hzr' hzr]
    · have hzr' : z ∈ domain r' := by
        rw [hdom1] at hz
        rcases mem_union_iff.mp hz with h | h
        · exact absurd h hzr
        · exact h
      rw [hv2 z hzr hzr', hv1' z hzr']
  · rw [levySwapAutomorphism_value h1]
    exact levySwapCondition_self (levyCollapse_isFunction h1) (levyCollapse_isFunction h2) hdomeq

end Levy

end ZFVP
