import ZFVP.ModelTheory.SchmerlInternalBranchMarkers
import ZFVP.ModelTheory.SchmerlInternalBranchCore
import ZFVP.ModelTheory.SchmerlInternalSpecializationProducts
import ZFVP.ModelTheory.SchmerlInternalCCCPreservation
import ZFVP.ModelTheory.SchmerlInternalBranchNamesPreservation
import ZFVP.ModelTheory.ForcingChoice

/-! The actual internal corrected weak-specialization extension. Markers,
the core, the poset, and the coloring are constructed; square ccc supplies
both omega-one preservation and preservation of full cofinal branches. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem check_monotone_anchor (F : ForcingContext V) {D A S a : V}
    (ha : a ∈ A ^ D)
    (hmono : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ S → ⟨a ‘ x, a ‘ y⟩ₖ ∈ S) :
    ∀ x ∈ F.check D, ∀ y ∈ F.check D,
      ⟨x, y⟩ₖ ∈ F.check S → ⟨(F.check a) ‘ x, (F.check a) ‘ y⟩ₖ ∈ F.check S := by
  let : IsFunction a := IsFunction.of_mem ha
  intro x hx y hy hxy
  obtain ⟨u, hu, rfl⟩ := (F.mem_check_iff D x).mp hx
  obtain ⟨v, hv, rfl⟩ := (F.mem_check_iff D y).mp hy
  rw [F.check_value ((domain_eq_of_mem_function ha).symm ▸ hu),
    F.check_value ((domain_eq_of_mem_function ha).symm ▸ hv)]
  exact (F.check_relation_iff S _ _).mpr (hmono u hu v hv ((F.check_relation_iff S u v).mp hxy))

theorem check_anchor_chain_fibers (F : ForcingContext V) {D A S a : V}
    (ha : a ∈ A ^ D)
    (hfiber : ∀ x ∈ D, ∀ y ∈ D, a ‘ x = a ‘ y → ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S) :
    ∀ x ∈ F.check D, ∀ y ∈ F.check D,
      (F.check a) ‘ x = (F.check a) ‘ y → ⟨x, y⟩ₖ ∈ F.check S ∨ ⟨y, x⟩ₖ ∈ F.check S := by
  let : IsFunction a := IsFunction.of_mem ha
  intro x hx y hy hxy
  obtain ⟨u, hu, rfl⟩ := (F.mem_check_iff D x).mp hx
  obtain ⟨v, hv, rfl⟩ := (F.mem_check_iff D y).mp hy
  rw [F.check_value ((domain_eq_of_mem_function ha).symm ▸ hu),
    F.check_value ((domain_eq_of_mem_function ha).symm ▸ hv)] at hxy
  exact (hfiber u hu v hv ((F.check_eq_iff _ _).mp hxy)).imp
    (F.check_relation_iff S u v).mpr (F.check_relation_iff S v u).mpr

end ForcingContext

namespace Schmerl

noncomputable def internalCofinalBranches (D S κ rank : V) : V :=
  {B ∈ ℘ D ; IsInternalCofinalBranch D S κ rank B}

theorem mem_internalCofinalBranches (D S κ rank B : V) :
    B ∈ internalCofinalBranches D S κ rank ↔ IsInternalCofinalBranch D S κ rank B := by
  simp only [internalCofinalBranches, mem_sep_iff, mem_power_iff]
  exact ⟨And.right, fun h ↦ ⟨h.1, h⟩⟩

theorem InternalSeparatedMarkerData.generic_weak_coloring
    {D S κ rank J m : V} (h : InternalSeparatedMarkerData D S κ rank J m)
    (G : Set V)
    (hG : IsExternalForcingGeneric (internalSpecialization (internalBranchCore D S J m) S)
      (reverseInclusionOrder (internalSpecialization (internalBranchCore D S J m) S)) G) :
    let F := internalSpecializationContext (internalBranchCore D S J m) S G hG
    ∃ f ∈ (ω : F.Model) ^ F.check D, InternallyWeakSpecialization (F.check D) (F.check S) f := by
  let C := internalBranchCore D S J m
  let a := internalBranchAnchor D S J m
  let F := internalSpecializationContext C S G hG
  let g := internalSpecializationColor C S G hG
  have hgspec := internalSpecializationColor_spec C S G hG
  change g ∈ F.check (ω : V) ^ F.check C ∧ InternallyStrict (F.check S) g at hgspec
  have hω : F.check (ω : V) = (ω : F.Model) := F.checkEmbedding.map_omega
  have hg : g ∈ (ω : F.Model) ^ F.check C := by
    simpa only [hω] using hgspec.1
  have ha : F.check a ∈ F.check C ^ F.check D :=
    (F.check_function_iff a D C).mpr h.anchor_function
  refine ⟨compose (F.check a) g, ?_⟩
  exact compose_strict_of_chain_fibers ha
    (F.check_monotone_anchor h.anchor_function
      (fun _ hx _ hy hxy ↦ h.anchor_monotone hx hy hxy))
    (F.check_anchor_chain_fibers h.anchor_function
      (fun _ hx _ hy he ↦ h.anchor_fibers_chain hx hy he)) hg hgspec.2

/-- A countable ambient ZFC model has an actual weak-specializing extension
which preserves omega-one and every full cofinal branch of the given tree.
The sole branch bound is internal, on the set of all its internal branches. -/
theorem exists_internal_weak_specialization_extension [Countable V] (hAC : InternalChoice V)
    {D S rank : V}
    (hT : InternalRankedTree D S (hartogsNumber (ω : V)) rank)
    (hord : IsForcingPoset D S)
    (hrankinj : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ S → rank ‘ x = rank ‘ y → x = y)
    (hcard : internalCofinalBranches D S (hartogsNumber (ω : V)) rank ≤# hartogsNumber (ω : V)) :
    ∃ F : ForcingContext V,
      InternalChoice F.Model ∧ F.check (hartogsNumber (ω : V)) = hartogsNumber (ω : F.Model) ∧
      (∃ f ∈ (ω : F.Model) ^ F.check D, InternallyWeakSpecialization (F.check D) (F.check S) f) ∧
      ∀ B : F.Model,
        IsInternalCofinalBranch (F.check D) (F.check S) (hartogsNumber (ω : F.Model)) (F.check rank) B →
        ∃ C : V, IsInternalCofinalBranch D S (hartogsNumber (ω : V)) rank C ∧ F.check C = B := by
  let J := internalCofinalBranches D S (hartogsNumber (ω : V)) rank
  have hbranches : ∀ B ∈ J, IsInternalCofinalBranch D S (hartogsNumber (ω : V)) rank B :=
    fun B hB ↦ (mem_internalCofinalBranches _ _ _ _ B).mp hB
  have hall : ∀ B : V, IsInternalCofinalBranch D S (hartogsNumber (ω : V)) rank B → B ∈ J :=
    fun B hB ↦ (mem_internalCofinalBranches _ _ _ _ B).mpr hB
  obtain ⟨m, hm, hmem, hsep⟩ := exists_internal_separated_branch_markers hAC hT hord hrankinj hcard hbranches
  have hdata : InternalSeparatedMarkerData D S (hartogsNumber (ω : V)) rank J m :=
    ⟨hord, hT, hm, hbranches, hmem, hsep⟩
  let C := internalBranchCore D S J m
  have hchains : ∀ B : V, B ⊆ C →
      (∀ x ∈ B, ∀ y ∈ B, ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S) → IsInternallyCountable B :=
    hdata.core_chains_countable hrankinj hall
  obtain ⟨G, hG, _⟩ := exists_externalForcingGeneric
    (internalSpecialization_poset C S).1 (empty_mem_internalSpecialization C S)
  let F := internalSpecializationContext C S G hG
  have hccc : IsInternallyCCC F.P F.R :=
    internalSpecialization_countable_antichains hAC hdata.core_reflexive hdata.core_below_linear hchains
  have hsquare : ∀ A : V,
      IsForcingAntichain (F.P ×ˢ F.P) (productOrder F.P F.R F.P F.R) A → IsInternallyCountable A :=
    internalSpecialization_square_countable_antichains hAC hdata.core_reflexive hdata.core_below_linear hchains
  have hω := F.check_hartogs_omega_of_internalCCC hAC hccc
  refine ⟨F, F.internalChoice_of_ground hAC, hω, hdata.generic_weak_coloring G hG, ?_⟩
  intro B hB
  rw [← hω] at hB
  exact F.exists_ground_cofinalBranch_of_internalSquareCCC hAC hT
    (hartogsNumber_omega_regular (dependentChoiceAt_of_internalChoice hAC (ω : V)))
    omega_mem_hartogs_omega hsquare hB

end Schmerl
end ZFVP
