import ZFVP.ModelTheory.LevyConePairArrangement
import ZFVP.ModelTheory.LevyConeAlgebraProperties
import ZFVP.ModelTheory.LevySupportGalois

/-! What the residue `ForcingContext.ValueOfConeIsCone` of the two-cone form of Jech, Set Theory,
Lemma 25.5 amounts to, and one sufficient condition for it that the Levy collapse can supply.

`ZFVP/ModelTheory/LevyConePairArrangement.lean` isolates the residue: for the cone data
`IsOrbitConeData τ σ p q` of Lemma 25.5, both conditions of the pair are regular cones of
conditions of the poset exactly when some regular cone `coneRegular r'` below `q` whose check lies
in the orbit filter has `‖(coneRegular r')ˇ ∈ τ‖ ∩ p` again a regular cone of a condition.

### The residue is a statement about one isomorphism

`orbitConeData_isomorphism` makes `b ↦ ‖b̌ ∈ τ‖ ∩ p` an isomorphism `ψ` of the cone of the
completion below `q` onto the cone below `p`. `valueOfConeIsCone_iff_image_coneRegular` rewrites
the residue with `ψ`: it says that `ψ` carries the cone of some condition below `q`, with check in
the filter, to the cone of a condition. `exists_cone_isomorphism_valueOfConeIsCone_iff` states the
same with the isomorphism produced. So the open statement is about a single isomorphism of cones of
the completion of the collapse, and asks it to carry one condition cone to a condition cone.

### Why density gives only half of it

Regular cones of conditions are dense in the completion (`exists_coneRegular_subset`,
`levy_cone_coneRegular_dense`), so condition cones sit below every nonzero condition on either
side. `exists_coneRegular_preimage_below` is the useful form: below a Boolean condition `p₁ ⊆ p`
there is a condition cone `coneRegular r`, and its preimage `‖(coneRegular r)ˇ ∈ σ‖ ∩ q` under the
isomorphism is a Boolean condition below `q` with value exactly `coneRegular r`. The preimage is a
Boolean condition and in general not a condition cone, which is why one round does not close the
residue: the residue asks for a condition cone whose *image* is a condition cone, and density
produces a condition cone on one side together with an unconstrained Boolean condition on the
other.

`exists_alternating_cone_step` is one round of the obvious repair. From a Boolean condition
`q₁ ⊆ q` it produces a condition cone `coneRegular r' ⊆ q₁`, a condition cone `coneRegular r`
below the image of `coneRegular r'`, and the preimage `d` of `coneRegular r`, a Boolean condition
with `coneRegular r' ⊇ d` and `‖ď ∈ τ‖ ∩ p = coneRegular r`. Feeding `d` back in as the new `q₁`
gives the next round. The rounds produce a decreasing sequence of condition cones
`coneRegular r'₀ ⊇ d₀ ⊇ coneRegular r'₁ ⊇ d₁ ⊇ ...` on the side of the filter, so a fusion
argument would have to find a nonzero condition below all of the `coneRegular r'ₙ`, that is, a
single condition of `Coll(ω, <κ)` extending an infinite decreasing sequence of its conditions.
Conditions of `Coll(ω, <κ)` are finite partial functions, and the collapse is not countably closed,
so nothing supplies that limit. This module does not prove the failure of countable closure; it
records the shape of the obstruction, and `valueOfConeIsCone_of_preimage_coneRegular` says exactly
what would have to happen instead: the alternation closes at a stage where the preimage `d` is
itself a condition cone.

### The sufficient condition that the project can supply

Asking that every Boolean condition of the completion be a condition cone is hopeless: a Boolean
condition is any nonzero regular set, and already the union of the cones of two incompatible
conditions is regular but is the cone of no single condition. What does work is the automorphism
group. An automorphism `π` of the poset carries condition cones to condition cones,
`imageAction_coneRegular`, and so does its lift to the completion, `booleanLift_coneRegular`.
`valueOfConeIsCone_of_lifted` therefore closes the residue at any condition cone where the value
map agrees with the lift of an automorphism, and `levy_valueOfConeIsCone_of_lifted` is that
statement for `Coll(ω, <κ)`.

`ValueAgreesWithLift` names what is left: below some Boolean condition of the filter the value map
is the lift of an automorphism of the poset. `valueOfConeIsCone_of_agreesWithLift` derives the
residue from it, using the trace density `exists_trace_coneRegular_below` to find a condition cone
with check in the filter below the condition of agreement. The converse fails to be available in
this generality: the residue gives a single condition cone carried to a condition cone, and one
matched pair does not produce an automorphism. What is provable is
`levy_exists_lift_agreement_at_of_valueOfConeIsCone`: for the Levy collapse, if the two conditions
of that matched pair have the same domain then the swap automorphism does agree with the value map
at that one condition cone. Agreement on a whole cone, which is what `ValueAgreesWithLift` asks
for, is not obtained. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable {A : ForcingContext V}

/-! ### The residue as a statement about the isomorphism of cones -/

/-- The residue rewritten with any map `ψ` that computes the value map on the cone below `q`: it
says that `ψ` sends the cone of some condition below `q`, whose check lies in the filter, to the
cone of a condition. -/
theorem valueOfConeIsCone_iff_image_coneRegular {τ p q ψ : V} {H : A.Model}
    (hψ : ∀ b ∈ booleanConditions A.P A.R, b ⊆ q → ψ ‘ b = A.booleanMemValue τ b ∩ p) :
    A.ValueOfConeIsCone H τ p q ↔
      ∃ r' ∈ A.P, coneRegular A.P A.R r' ⊆ q ∧ A.check (coneRegular A.P A.R r') ∈ H ∧
        ∃ r ∈ A.P, ψ ‘ (coneRegular A.P A.R r') = coneRegular A.P A.R r := by
  constructor
  · rintro ⟨r', hr'P, hr'q, hr'H, r, hrP, hval⟩
    refine ⟨r', hr'P, hr'q, hr'H, r, hrP, ?_⟩
    rw [hψ _ (coneRegular_mem_booleanConditions A.order hr'P) hr'q]
    exact hval
  · rintro ⟨r', hr'P, hr'q, hr'H, r, hrP, hval⟩
    refine ⟨r', hr'P, hr'q, hr'H, r, hrP, ?_⟩
    rw [← hψ _ (coneRegular_mem_booleanConditions A.order hr'P) hr'q]
    exact hval

/-- The reformulation with the isomorphism produced. From the clauses of the cone data there is an
isomorphism `ψ` of the cone of the completion below `q` onto the cone below `p`, and the residue is
the statement that `ψ` carries the cone of some condition below `q`, with check in the filter, to
the cone of a condition. -/
theorem exists_cone_isomorphism_valueOfConeIsCone_iff {τ σ p q : V} {H : A.Model}
    (hdata : A.IsOrbitConeData τ σ p q) :
    ∃ ψ : V,
      IsForcingIsomorphism
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) q))
        (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p)
        (restrictedOrder (booleanOrder A.P A.R)
          (forcingCone (booleanConditions A.P A.R) (booleanOrder A.P A.R) p)) ψ ∧
      (∀ b ∈ booleanConditions A.P A.R, b ⊆ q → ψ ‘ b = A.booleanMemValue τ b ∩ p) ∧
      (A.ValueOfConeIsCone H τ p q ↔
        ∃ r' ∈ A.P, coneRegular A.P A.R r' ⊆ q ∧ A.check (coneRegular A.P A.R r') ∈ H ∧
          ∃ r ∈ A.P, ψ ‘ (coneRegular A.P A.R r') = coneRegular A.P A.R r) := by
  obtain ⟨ψ, hiso, hψ⟩ := A.orbitConeData_isomorphism hdata
  exact ⟨ψ, hiso, hψ, valueOfConeIsCone_iff_image_coneRegular hψ⟩

/-! ### Density, and what one round of it gives -/

/-- Density in the form that matters. Below any Boolean condition `p₁ ⊆ p` there is a regular cone
of a condition of the poset, and the preimage of that cone under the isomorphism is a Boolean
condition below `q` whose value meets `p` in the cone again. The preimage is only a Boolean
condition: nothing here makes it a regular cone of a condition. -/
theorem exists_coneRegular_preimage_below {τ σ p q p₁ : V} (hdata : A.IsOrbitConeData τ σ p q)
    (hp₁B : p₁ ∈ booleanConditions A.P A.R) (hp₁p : p₁ ⊆ p) :
    ∃ r ∈ A.P, coneRegular A.P A.R r ⊆ p₁ ∧
      A.orbitInverseValue σ (coneRegular A.P A.R r) ∩ q ∈ booleanConditions A.P A.R ∧
      A.orbitInverseValue σ (coneRegular A.P A.R r) ∩ q ⊆ q ∧
      A.booleanMemValue τ (A.orbitInverseValue σ (coneRegular A.P A.R r) ∩ q) ∩ p
        = coneRegular A.P A.R r := by
  obtain ⟨r, hrP, hrsub⟩ := exists_coneRegular_subset A.order hp₁B
  obtain ⟨hdB, hdq, hdval⟩ := A.orbitConeData_inverse_value hdata
    (coneRegular_mem_booleanConditions A.order hrP) (subset_trans hrsub hp₁p)
  exact ⟨r, hrP, hrsub, hdB, hdq, hdval⟩

/-- The same on the other side: below any Boolean condition `q₁ ⊆ q` there is a regular cone of a
condition of the poset, and its image under the isomorphism is a Boolean condition below `p`. -/
theorem exists_coneRegular_image_below {τ σ p q q₁ : V} (hdata : A.IsOrbitConeData τ σ p q)
    (hq₁B : q₁ ∈ booleanConditions A.P A.R) (hq₁q : q₁ ⊆ q) :
    ∃ r' ∈ A.P, coneRegular A.P A.R r' ⊆ q₁ ∧
      A.booleanMemValue τ (coneRegular A.P A.R r') ∩ p ∈ booleanConditions A.P A.R ∧
      A.booleanMemValue τ (coneRegular A.P A.R r') ∩ p ⊆ p := by
  obtain ⟨r', hr'P, hr'sub⟩ := exists_coneRegular_subset A.order hq₁B
  obtain ⟨hvB, hvp⟩ := A.orbitConeData_value_mem hdata
    (coneRegular_mem_booleanConditions A.order hr'P) (subset_trans hr'sub hq₁q)
  exact ⟨r', hr'P, hr'sub, hvB, hvp⟩

/-- One round of the alternation. From a Boolean condition `q₁ ⊆ q` on the side of the filter:
take a condition cone `coneRegular r'` below `q₁`, then a condition cone `coneRegular r` below its
image, and pull that back. The pullback `d` is a Boolean condition below `coneRegular r'` with
value `coneRegular r`, and the next round starts from `d`. The output on the side of the filter is
a Boolean condition, not a condition cone, so the rounds do not stop. -/
theorem exists_alternating_cone_step {τ σ p q q₁ : V} (hdata : A.IsOrbitConeData τ σ p q)
    (hq₁B : q₁ ∈ booleanConditions A.P A.R) (hq₁q : q₁ ⊆ q) :
    ∃ r' ∈ A.P, coneRegular A.P A.R r' ⊆ q₁ ∧ ∃ r ∈ A.P,
      coneRegular A.P A.R r ⊆ A.booleanMemValue τ (coneRegular A.P A.R r') ∩ p ∧
      A.orbitInverseValue σ (coneRegular A.P A.R r) ∩ q ∈ booleanConditions A.P A.R ∧
      A.orbitInverseValue σ (coneRegular A.P A.R r) ∩ q ⊆ coneRegular A.P A.R r' ∧
      A.booleanMemValue τ (A.orbitInverseValue σ (coneRegular A.P A.R r) ∩ q) ∩ p
        = coneRegular A.P A.R r := by
  obtain ⟨r', hr'P, hr'sub⟩ := exists_coneRegular_subset A.order hq₁B
  have hr'B := coneRegular_mem_booleanConditions A.order hr'P
  have hr'q : coneRegular A.P A.R r' ⊆ q := subset_trans hr'sub hq₁q
  obtain ⟨hvB, hvp⟩ := A.orbitConeData_value_mem hdata hr'B hr'q
  obtain ⟨r, hrP, hrsub⟩ := exists_coneRegular_subset A.order hvB
  have hrB := coneRegular_mem_booleanConditions A.order hrP
  obtain ⟨hdB, hdq, hdval⟩ := A.orbitConeData_inverse_value hdata hrB
    (subset_trans hrsub hvp)
  refine ⟨r', hr'P, hr'sub, r, hrP, hrsub, hdB, ?_, hdval⟩
  refine A.orbitConeData_subset_of_value_subset hdata hdB hr'B hdq ?_
  rw [hdval]
  exact hrsub

/-- What would close the alternation. If at some stage the preimage of the condition cone
`coneRegular r` is itself the cone of a condition `s` whose check lies in the filter, then the
residue holds. -/
theorem valueOfConeIsCone_of_preimage_coneRegular {τ σ p q r s : V} {H : A.Model}
    (hdata : A.IsOrbitConeData τ σ p q) (hrP : r ∈ A.P) (hsP : s ∈ A.P)
    (hrp : coneRegular A.P A.R r ⊆ p)
    (hs : A.orbitInverseValue σ (coneRegular A.P A.R r) ∩ q = coneRegular A.P A.R s)
    (hsH : A.check (coneRegular A.P A.R s) ∈ H) :
    A.ValueOfConeIsCone H τ p q := by
  obtain ⟨hdB, hdq, hdval⟩ := A.orbitConeData_inverse_value hdata
    (coneRegular_mem_booleanConditions A.order hrP) hrp
  rw [hs] at hdq hdval
  exact ⟨s, hsP, hdq, hsH, r, hrP, hdval⟩

/-! ### The residue from an automorphism -/

/-- The sufficient condition. Automorphisms of the poset carry regular cones of conditions to
regular cones of conditions, and so do their lifts to the completion. So if at some condition cone
below `q` whose check lies in the filter the value map agrees with the lift of an automorphism,
the residue holds there. -/
theorem valueOfConeIsCone_of_lifted {τ p q : V} {H : A.Model} {π r' : V}
    (hπ : IsForcingAutomorphism A.P A.R π) (hr'P : r' ∈ A.P)
    (hr'q : coneRegular A.P A.R r' ⊆ q)
    (hr'H : A.check (coneRegular A.P A.R r') ∈ H)
    (hagree : A.booleanMemValue τ (coneRegular A.P A.R r') ∩ p
      = (booleanLift A.P A.R π) ‘ (coneRegular A.P A.R r')) :
    A.ValueOfConeIsCone H τ p q := by
  refine ⟨r', hr'P, hr'q, hr'H, π ‘ r', function_value_mem hπ.1 hr'P, ?_⟩
  rw [hagree, booleanLift_value (coneRegular_mem_booleanConditions A.order hr'P),
    imageAction_coneRegular hπ hr'P]

/-- The same for a forcing context over the Levy collapse `Coll(ω, <κ)`: if the value map agrees
at a condition cone below `q`, whose check is in the filter, with the lift of an automorphism of
the collapse, then the residue holds. -/
theorem levy_valueOfConeIsCone_of_lifted {κ τ p q : V} {H : A.Model} {π r' : V}
    (hAP : A.P = levyCollapse κ) (hAR : A.R = levyOrder κ)
    (hπ : IsForcingAutomorphism (levyCollapse κ) (levyOrder κ) π)
    (hr' : r' ∈ levyCollapse κ)
    (hr'q : coneRegular (levyCollapse κ) (levyOrder κ) r' ⊆ q)
    (hr'H : A.check (coneRegular (levyCollapse κ) (levyOrder κ) r') ∈ H)
    (hagree : A.booleanMemValue τ (coneRegular (levyCollapse κ) (levyOrder κ) r') ∩ p
      = (booleanLift (levyCollapse κ) (levyOrder κ) π) ‘
        (coneRegular (levyCollapse κ) (levyOrder κ) r')) :
    A.ValueOfConeIsCone H τ p q := by
  rw [← hAP] at hr'
  rw [← hAP, ← hAR] at hπ hr'q hr'H hagree
  exact valueOfConeIsCone_of_lifted hπ hr' hr'q hr'H hagree

/-! ### What is left -/

/-- What the residue is missing, as one statement: below some Boolean condition `q₁` of the filter,
the value map `b ↦ ‖b̌ ∈ τ‖ ∩ p` is the lift of an automorphism of the poset.

`valueOfConeIsCone_of_agreesWithLift` shows this implies `ValueOfConeIsCone`, so proving it for the
Levy collapse would close the two-cone form of Lemma 25.5. It is stronger than the residue as far
as this development can tell: the residue asks only that one condition cone go to a condition cone,
which is a single equation, while this asks for agreement with an automorphism on a whole cone. The
partial converse that is available is `levy_exists_lift_agreement_at_of_valueOfConeIsCone`. -/
def ValueAgreesWithLift (A : ForcingContext V) (H : A.Model) (τ p q : V) : Prop :=
  ∃ π : V, IsForcingAutomorphism A.P A.R π ∧
    ∃ q₁ ∈ booleanConditions A.P A.R, q₁ ⊆ q ∧ A.check q₁ ∈ H ∧
      ∀ b ∈ booleanConditions A.P A.R, b ⊆ q₁ →
        A.booleanMemValue τ b ∩ p = (booleanLift A.P A.R π) ‘ b

/-- Agreement with a lifted automorphism below a condition of the filter gives the residue. Below
the condition of agreement there is a regular cone of a condition of the poset whose check is in
the filter, by the trace density, and the value map is the lift there. -/
theorem valueOfConeIsCone_of_agreesWithLift (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W pf H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W pf H)
    {τ p q : V} (h : A.ValueAgreesWithLift H τ p q) :
    A.ValueOfConeIsCone H τ p q := by
  obtain ⟨π, hπ, q₁, hq₁B, hq₁q, hq₁H, hagree⟩ := h
  obtain ⟨r', hr'P, hr'sub, hr'H⟩ := exists_trace_coneRegular_below hAC hH hq₁B hq₁H
  exact valueOfConeIsCone_of_lifted hπ hr'P (subset_trans hr'sub hq₁q) hr'H
    (hagree _ (coneRegular_mem_booleanConditions A.order hr'P) hr'sub)

/-- The partial converse for the Levy collapse. The residue produces a condition cone
`coneRegular r'` below `q`, with check in the filter, whose value meets `p` in a condition cone
`coneRegular r`. If the two conditions have the same domain then the swap automorphism of the
collapse carries `r'` to `r`, so its lift agrees with the value map at `coneRegular r'`. This is
agreement at one condition, not on a cone, so it does not give `ValueAgreesWithLift`. -/
theorem levy_exists_lift_agreement_at_of_valueOfConeIsCone {κ τ p q : V} {H : A.Model}
    (hAP : A.P = levyCollapse κ) (hAR : A.R = levyOrder κ)
    (h : A.ValueOfConeIsCone H τ p q) :
    ∃ r' ∈ A.P, coneRegular A.P A.R r' ⊆ q ∧ A.check (coneRegular A.P A.R r') ∈ H ∧
      ∃ r ∈ A.P, A.booleanMemValue τ (coneRegular A.P A.R r') ∩ p = coneRegular A.P A.R r ∧
        (domain r' = domain r → ∃ π : V, IsForcingAutomorphism A.P A.R π ∧
          A.booleanMemValue τ (coneRegular A.P A.R r') ∩ p
            = (booleanLift A.P A.R π) ‘ (coneRegular A.P A.R r')) := by
  obtain ⟨r', hr'P, hr'q, hr'H, r, hrP, hval⟩ := h
  refine ⟨r', hr'P, hr'q, hr'H, r, hrP, hval, fun hdom ↦ ?_⟩
  have hr'L : r' ∈ levyCollapse κ := by rw [← hAP]; exact hr'P
  have hrL : r ∈ levyCollapse κ := by rw [← hAP]; exact hrP
  obtain ⟨π, hπ, hπval⟩ := exists_levyAutomorphism_of_domain_eq hr'L hrL hdom
  rw [← hAP, ← hAR] at hπ
  refine ⟨π, hπ, ?_⟩
  rw [hval, booleanLift_value (coneRegular_mem_booleanConditions A.order hr'P),
    imageAction_coneRegular hπ hr'P, hπval]

end ForcingContext

end ZFVP
