import ZFVP.SetTheory.ForcingThreadAction
import ZFVP.SetTheory.ForcingThreadMaps
import ZFVP.ModelTheory.EquivalentSuborderRetraction
import ZFVP.ModelTheory.EquivalentSuborderFilterEquiv

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingThreadOrder_subcarrier_iff {θ R C D f g : V}
    (hD : D ⊆ C) (hf : f ∈ D) (hg : g ∈ D) :
    ⟨f, g⟩ₖ ∈ forcingThreadOrder θ R D ↔ ⟨f, g⟩ₖ ∈ forcingThreadOrder θ R C := by
  simp only [mem_forcingThreadOrder_iff, hf, hg, hD f hf, hD g hg, true_and]

theorem forcingThreadActionMap_equivalent {θ P R m C D f : V}
    (hC : ∀ f ∈ C, ∀ i ∈ θ, f ‘ i ∈ P ‘ i)
    (hD : D ⊆ C) (hmap : ∀ f ∈ C, forcingThreadAction θ m f ∈ D)
    (he : ∀ i ∈ θ, ∀ p ∈ P ‘ i,
      ⟨(m ‘ i) ‘ p, p⟩ₖ ∈ R ‘ i ∧ ⟨p, (m ‘ i) ‘ p⟩ₖ ∈ R ‘ i)
    (hf : f ∈ C) :
    ⟨(forcingThreadActionMap θ m C) ‘ f, f⟩ₖ ∈ forcingThreadOrder θ R C ∧
      ⟨f, (forcingThreadActionMap θ m C) ‘ f⟩ₖ ∈ forcingThreadOrder θ R C := by
  rw [forcingThreadActionMap_value hf]
  constructor
  · refine (mem_forcingThreadOrder_iff _ _ _ _ _).mpr ⟨hD _ (hmap f hf), hf, ?_⟩
    intro i hi
    rw [forcingThreadAction_value hi]
    exact (he i hi _ (hC f hf i hi)).1
  · refine (mem_forcingThreadOrder_iff _ _ _ _ _).mpr ⟨hf, hD _ (hmap f hf), ?_⟩
    intro i hi
    rw [forcingThreadAction_value hi]
    exact (he i hi _ (hC f hf i hi)).2

theorem forcingThreadActionMap_retraction {θ P R m C D : V}
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i))
    (hC : ∀ f ∈ C, ∀ i ∈ θ, f ‘ i ∈ P ‘ i)
    (hD : D ⊆ C) (hmap : ∀ f ∈ C, forcingThreadAction θ m f ∈ D)
    (hfix : ∀ f ∈ D, forcingThreadAction θ m f = f)
    (he : ∀ i ∈ θ, ∀ p ∈ P ‘ i,
      ⟨(m ‘ i) ‘ p, p⟩ₖ ∈ R ‘ i ∧ ⟨p, (m ‘ i) ‘ p⟩ₖ ∈ R ‘ i) :
    IsForcingRetraction D (forcingThreadOrder θ R D) C (forcingThreadOrder θ R C)
      (forcingThreadActionMap θ m C) := by
  have hm : forcingThreadActionMap θ m C ∈ D ^ C :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ hmap
  have hr := equivalentSuborderRetraction_spec (forcingThreadOrder_preorder hR hC) hD
    (fun _ hf _ hg ↦ forcingThreadOrder_subcarrier_iff hD hf hg) hm
    (fun _ hf ↦ forcingThreadActionMap_equivalent hC hD hmap he hf)
  have heq : equivalentSuborderRetraction C D (forcingThreadActionMap θ m C) =
      forcingThreadActionMap θ m C := by
    let := IsFunction.of_mem (equivalentSuborderRetraction_function hm)
    let := IsFunction.of_mem hm
    apply functions_eq_of_domain_values
    · rw [domain_eq_of_mem_function (equivalentSuborderRetraction_function hm), domain_eq_of_mem_function hm]
    intro f hf
    rw [domain_eq_of_mem_function (equivalentSuborderRetraction_function hm)] at hf
    rw [equivalentSuborderRetraction_value hf]
    classical
    by_cases hfd : f ∈ D
    · simp only [equivalentSuborderFix, hfd, ↓reduceIte, forcingThreadActionMap_value hf, hfix f hfd]
    · simp only [equivalentSuborderFix, hfd, ↓reduceIte]
  rwa [heq] at hr

/-- A coherent family of equivalent coordinate retractions yields an exact
retraction of inverse limits. The whole-thread map is specified internally. -/
theorem forcingInverseLimit_retraction {θ P N R π U m : V}
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i))
    (hP : ∀ i ∈ θ, P ‘ i ⊆ U) (hN : ∀ i ∈ θ, N ‘ i ⊆ P ‘ i)
    (hm : ∀ i ∈ θ, m ‘ i ∈ (N ‘ i) ^ (P ‘ i))
    (hfix : ∀ i ∈ θ, ∀ p ∈ N ‘ i, (m ‘ i) ‘ p = p)
    (he : ∀ i ∈ θ, ∀ p ∈ P ‘ i,
      ⟨(m ‘ i) ‘ p, p⟩ₖ ∈ R ‘ i ∧ ⟨p, (m ‘ i) ‘ p⟩ₖ ∈ R ‘ i)
    (hc : ∀ j ∈ θ, ∀ i ∈ j, i ∈ θ → ∀ p ∈ P ‘ j,
      (π ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ j) ‘ p) = (m ‘ i) ‘ ((π ‘ ⟨i, j⟩ₖ) ‘ p)) :
    IsForcingRetraction (forcingInverseLimit θ N π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ N π U))
      (forcingInverseLimit θ P π U) (forcingThreadOrder θ R (forcingInverseLimit θ P π U))
      (forcingThreadActionMap θ m (forcingInverseLimit θ P π U)) := by
  apply forcingThreadActionMap_retraction hR
    (fun _ hf ↦ ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1)
    (forcingInverseLimit_mono_coordinates hN) ?_ ?_ he
  · exact fun _ hf ↦ forcingThreadAction_mem_inverse hm
      (fun i hi p hp ↦ hP i hi p (hN i hi p hp)) hc hf
  · intro f hf
    obtain ⟨hfun, hv, _⟩ := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hf
    exact forcingThreadAction_fixes hfun hv hfix

/-- Commutation with sections preserves the same support witness at a direct limit. -/
theorem forcingDirectLimit_retraction {θ P N R π E U m : V}
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i))
    (hP : ∀ i ∈ θ, P ‘ i ⊆ U) (hN : ∀ i ∈ θ, N ‘ i ⊆ P ‘ i)
    (hm : ∀ i ∈ θ, m ‘ i ∈ (N ‘ i) ^ (P ‘ i))
    (hfix : ∀ i ∈ θ, ∀ p ∈ N ‘ i, (m ‘ i) ‘ p = p)
    (he : ∀ i ∈ θ, ∀ p ∈ P ‘ i,
      ⟨(m ‘ i) ‘ p, p⟩ₖ ∈ R ‘ i ∧ ⟨p, (m ‘ i) ‘ p⟩ₖ ∈ R ‘ i)
    (hc : ∀ j ∈ θ, ∀ i ∈ j, i ∈ θ → ∀ p ∈ P ‘ j,
      (π ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ j) ‘ p) = (m ‘ i) ‘ ((π ‘ ⟨i, j⟩ₖ) ‘ p))
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ P ‘ i,
      (m ‘ j) ‘ ((E ‘ ⟨i, j⟩ₖ) ‘ p) = (E ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ i) ‘ p)) :
    IsForcingRetraction (forcingDirectLimit θ N π E U)
      (forcingThreadOrder θ R (forcingDirectLimit θ N π E U))
      (forcingDirectLimit θ P π E U) (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))
      (forcingThreadActionMap θ m (forcingDirectLimit θ P π E U)) := by
  apply forcingThreadActionMap_retraction hR
    (fun _ hf ↦ ((mem_forcingInverseLimit_iff _ _ _ _ _).mp
      (forcingDirectLimit_subset _ _ _ _ _ _ hf)).2.1)
    (forcingDirectLimit_mono_coordinates hN) ?_ ?_ he
  · exact fun _ hf ↦ forcingThreadAction_mem_direct hm
      (fun i hi p hp ↦ hP i hi p (hN i hi p hp)) hc hE hf
  · intro f hf
    obtain ⟨hfun, hv, _⟩ := (mem_forcingInverseLimit_iff _ _ _ _ _).mp
      (forcingDirectLimit_subset _ _ _ _ _ _ hf)
    exact forcingThreadAction_fixes hfun hv hfix

noncomputable def forcingThreadGenericsEquiv {θ P R m C D : V}
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i))
    (hC : ∀ f ∈ C, ∀ i ∈ θ, f ‘ i ∈ P ‘ i)
    (hD : D ⊆ C) (hmap : ∀ f ∈ C, forcingThreadAction θ m f ∈ D)
    (he : ∀ i ∈ θ, ∀ p ∈ P ‘ i,
      ⟨(m ‘ i) ‘ p, p⟩ₖ ∈ R ‘ i ∧ ⟨p, (m ‘ i) ‘ p⟩ₖ ∈ R ‘ i) :
    {G : Set V // IsExternalForcingGeneric C (forcingThreadOrder θ R C) G} ≃
      {H : Set V // IsExternalForcingGeneric D (forcingThreadOrder θ R D) H} := by
  apply equivalentSuborderGenericsEquiv (forcingThreadOrder_preorder hR hC) hD
    (fun _ hf _ hg ↦ forcingThreadOrder_subcarrier_iff hD hf hg)
  intro f hf
  refine ⟨(forcingThreadActionMap θ m C) ‘ f, ?_,
    forcingThreadActionMap_equivalent hC hD hmap he hf⟩
  rw [forcingThreadActionMap_value hf]
  exact hmap f hf

theorem forcingThreadAction_generic_mem {θ P R m C D : V} {G : Set V} {f : V}
    (hC : ∀ f ∈ C, ∀ i ∈ θ, f ‘ i ∈ P ‘ i)
    (hD : D ⊆ C) (hmap : ∀ f ∈ C, forcingThreadAction θ m f ∈ D)
    (he : ∀ i ∈ θ, ∀ p ∈ P ‘ i,
      ⟨(m ‘ i) ‘ p, p⟩ₖ ∈ R ‘ i ∧ ⟨p, (m ‘ i) ‘ p⟩ₖ ∈ R ‘ i)
    (hG : IsExternalForcingFilter C (forcingThreadOrder θ R C) G) (hf : f ∈ G) :
    forcingThreadAction θ m f ∈ G ∧ forcingThreadAction θ m f ∈ D := by
  have hfC := hG.1 f hf
  have hh := (forcingThreadActionMap_equivalent hC hD hmap he hfC).2
  rw [forcingThreadActionMap_value hfC] at hh
  exact ⟨hG.2.2.1 f hf _ (hD _ (hmap f hfC)) hh, hmap f hfC⟩

/-- Restriction to the equivalent suborder leaves every earlier full-stage
generic unchanged after upward closure. -/
theorem forcingThread_coordinateGeneric_eq {θ P R m C D i : V} {G : Set V}
    (hi : i ∈ θ) (hR : IsForcingPreorder (P ‘ i) (R ‘ i))
    (hC : ∀ f ∈ C, ∀ j ∈ θ, f ‘ j ∈ P ‘ j)
    (hD : D ⊆ C) (hmap : ∀ f ∈ C, forcingThreadAction θ m f ∈ D)
    (he : ∀ j ∈ θ, ∀ p ∈ P ‘ j,
      ⟨(m ‘ j) ‘ p, p⟩ₖ ∈ R ‘ j ∧ ⟨p, (m ‘ j) ‘ p⟩ₖ ∈ R ‘ j)
    (hG : IsExternalForcingFilter C (forcingThreadOrder θ R C) G) :
    forcingProjectionGeneric (P ‘ i) (R ‘ i) (forcingThreadCoordinate C i) G =
      forcingProjectionGeneric (P ‘ i) (R ‘ i) (forcingThreadCoordinate D i) {f | f ∈ G ∧ f ∈ D} := by
  apply Set.ext
  intro p
  constructor
  · rintro ⟨hp, f, hf, hfp⟩
    have hfn := forcingThreadAction_generic_mem hC hD hmap he hG hf
    refine ⟨hp, forcingThreadAction θ m f, hfn, ?_⟩
    rw [forcingThreadCoordinate_value hfn.2]
    rw [forcingThreadCoordinate_value (hG.1 f hf)] at hfp
    have hh := (he i hi _ (hC f (hG.1 f hf) i hi)).1
    rw [← forcingThreadAction_value (m := m) (f := f) hi] at hh
    exact hR.2.2 _ (hC _ (hD _ hfn.2) i hi) _ (hC f (hG.1 f hf) i hi) p hp hh hfp
  · rintro ⟨hp, f, hf, hfp⟩
    refine ⟨hp, f, hf.1, ?_⟩
    rw [forcingThreadCoordinate_value (hG.1 f hf.1)]
    rwa [forcingThreadCoordinate_value hf.2] at hfp

end ZFVP
