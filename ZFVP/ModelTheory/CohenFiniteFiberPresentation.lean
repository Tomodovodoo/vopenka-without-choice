import ZFVP.ModelTheory.CohenMinimumAssignment
import ZFVP.SetTheory.FiniteRangeFibers

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)

/-- Every Cohen-model set has a ground-indexed family of actual internal functions with
finite exact-support fibers, and at least one nonempty such fiber for each member. -/
theorem exists_finite_fiber_orbit_family (X : (cohenContext (ω : V) G hG).Name) :
    ∃ D : V, ∃ hD : IsCohenSupportPool D,
      ∀ x ∈ (cohenContext (ω : V) G hG).ofName X,
        IsInternallyFinite (familySupport (orbitFamily hG D hD) x) ∧
        (∃ j ∈ (cohenContext (ω : V) G hG).check D,
          IsNonempty (exactSupportFiber (orbitFamily hG D hD) j x)) ∧
        ∀ j ∈ (cohenContext (ω : V) G hG).check D,
          IsInternallyFinite (exactSupportFiber (orbitFamily hG D hD) j x) := by
  let S := cohenContext (ω : V) G hG
  obtain ⟨D, hD, hcover⟩ := exists_least_support_pool hG X
  let H := orbitFamily hG D hD
  have hHf := orbitFamily_mem_function hG D hD
  have : IsFunction H := IsFunction.of_mem hHf
  have hdom : domain H = S.check D := domain_eq_of_mem_function hHf
  refine ⟨D, hD, ?_⟩
  intro x hx
  obtain ⟨ν, E, hνD, heν, hE, hmin⟩ := hcover x hx
  let a := finiteAssignmentValue hG E hE.1 hE.2.1 (identity (ω : V)) (internalPermutation_identity _)
  let j := S.check ⟨ν.val, E⟩ₖ
  have hj : j ∈ S.check D := (S.check_mem_iff _ _).mpr hνD
  have hax : ⟨a, x⟩ₖ ∈ H ‘ j := by
    have hh := least_support_assignment_in_family hG hD ν hE hνD
    rwa [heν] at hh
  have ha : a ∈ familyAssignments H x := familyAssignments_of_pair (hdom.symm ▸ hj) hax
  have hleast : ∀ b ∈ familyAssignments H x, range a ⊆ range b := by
    intro b hb
    obtain ⟨_, k, hk, hbx⟩ := (mem_familyAssignments H x b).mp hb
    exact least_support_assignment_range_subset hG hD hE.1 hE.2.1 hmin (hdom ▸ hk) hbx
  have heq := familySupport_eq_range ha hleast
  have hfinite : IsInternallyFinite (familySupport H x) := by
    rw [heq]
    exact finiteAssignmentValue_range_finite hG E hE.1 hE.2.1
      (identity (ω : V)) (internalPermutation_identity _)
  refine ⟨hfinite, ⟨j, hj, ?_⟩, ?_⟩
  · exact ⟨a, (mem_exactSupportFiber H j x a).mpr
      ⟨mem_domain_of_kpair_mem hax, hax, heq.symm⟩⟩
  · intro k hk
    obtain ⟨B, hB, hfun⟩ := orbitFamily_inputs_fixed_finite_domain hG hD hk
    exact exactSupportFiber_finite hB hfinite hfun

end CohenModel

end ZFVP
