import ZFVP.SetTheory.WoodinCollapseDirectedClosure
import ZFVP.ModelTheory.LocalSelectedUnionBound
import ZFVP.ModelTheory.DirectLimitQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Separative directedness supplies actual common extensions for each pair. -/
theorem IsForcingDirectedFamily.compatible {P R I f : V}
    (hR : IsForcingPreorder P R)
    (hf : IsForcingDirectedFamily P (forcingSeparativeOrder P R) I f)
    {i j : V} (hi : i ∈ I) (hj : j ∈ I) :
    ForcingCompatible P R (f ‘ i) (f ‘ j) := by
  obtain ⟨k, hk, hki, hkj⟩ := hf.2 i hi j hj
  exact (forcingSeparativeOrder_compatible_iff hR).mp
    ⟨f ‘ k, function_value_mem hf.1 hk, hki, hkj⟩

theorem compatible_range_of_separative_directed {P I f : V}
    (hP : ∀ p ∈ P, IsFunction p)
    (hf : IsForcingDirectedFamily P
      (forcingSeparativeOrder P (reverseInclusionOrder P)) I f) :
    CompatibleFunctionFamily (range f) := by
  let := IsFunction.of_mem hf.1
  intro p hp q hq x y z hxy hxz
  obtain ⟨i, hip⟩ := mem_range_iff.mp hp
  obtain ⟨j, hjq⟩ := mem_range_iff.mp hq
  have hi : i ∈ I := domain_eq_of_mem_function hf.1 ▸ mem_domain_of_kpair_mem hip
  have hj : j ∈ I := domain_eq_of_mem_function hf.1 ▸ mem_domain_of_kpair_mem hjq
  obtain ⟨r, hr, hrp, hrq⟩ := hf.compatible (reverseInclusionOrder_poset P).1 hi hj
  let := hP r hr
  have hpr : p ⊆ r := by
    rw [← value_eq_of_kpair_mem hip]
    exact ((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2
  have hqr : q ⊆ r := by
    rw [← value_eq_of_kpair_mem hjq]
    exact ((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2
  exact IsFunction.unique (hpr _ hxy) (hqr _ hxz)

/-- The union is an actual order lower bound, even when the family is only
directed for the separative preorder. The DC premise is internal to this model. -/
theorem woodinCollapse_separative_directed_union {κ δ α f : V}
    (hκ : IsRegularCardinal κ) (hα : α ∈ κ) (hDC : InternalDependentChoiceAt α)
    (hf : IsForcingDirectedFamily (woodinCollapse κ δ)
      (forcingSeparativeOrder (woodinCollapse κ δ) (woodinCollapseOrder κ δ)) α f) :
    ⋃ˢ range f ∈ woodinCollapse κ δ ∧
      ∀ i ∈ α, ⟨⋃ˢ range f, f ‘ i⟩ₖ ∈ woodinCollapseOrder κ δ := by
  have hc := compatible_range_of_separative_directed
    (fun p hp ↦ ((mem_woodinCollapse κ δ p).mp hp).2.1) hf
  have hu := woodinCollapse_sequence_union hκ hα hDC hf.1 hc
  refine ⟨hu, fun i hi ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hu, function_value_mem hf.1 hi, ?_⟩⟩
  intro x hx
  exact mem_sUnion_iff.mpr ⟨_, value_mem_range hf.1 hi, hx⟩

theorem woodinCollapse_separative_directedClosedAt {κ δ α : V}
    (hκ : IsRegularCardinal κ) (hα : α ∈ κ) (hDC : InternalDependentChoiceAt α) :
    IsForcingDirectedClosedAt (woodinCollapse κ δ)
      (forcingSeparativeOrder (woodinCollapse κ δ) (woodinCollapseOrder κ δ)) α := by
  intro f hf
  obtain ⟨hu, hb⟩ := woodinCollapse_separative_directed_union hκ hα hDC hf
  exact ⟨⋃ˢ range f, hu, fun i hi ↦
    forcingOrder_subset_separative (woodinCollapse_poset κ δ).1 _ (hb i hi)⟩

theorem IsForcingProjection.separative_directed_compose {P R Q S π I f : V}
    (h : IsForcingProjection P R Q S π)
    (hf : IsForcingDirectedFamily Q (forcingSeparativeOrder Q S) I f) :
    IsForcingDirectedFamily P (forcingSeparativeOrder P R) I (compose f π) := by
  refine ⟨compose_function hf.1 h.maps, fun i hi j hj ↦ ?_⟩
  obtain ⟨k, hk, hki, hkj⟩ := hf.2 i hi j hj
  refine ⟨k, hk, ?_, ?_⟩
  · rw [value_compose_of_mem_function hf.1 h.maps hk,
      value_compose_of_mem_function hf.1 h.maps hi]
    exact h.separative_monotone hki
  · rw [value_compose_of_mem_function hf.1 h.maps hk,
      value_compose_of_mem_function hf.1 h.maps hj]
    exact h.separative_monotone hkj

/-- One projected bound suffices when the family has a common section range. -/
theorem IsForcingSplitProjection.separative_directed_bound_of_range {P R Q S π E I f : V}
    (h : IsForcingSplitProjection P R Q S π E)
    (hc : IsForcingDirectedClosedAt P (forcingSeparativeOrder P R) I)
    (hf : IsForcingDirectedFamily Q (forcingSeparativeOrder Q S) I f)
    (hrange : ∀ i ∈ I, ∃ p ∈ P, E ‘ p = f ‘ i) :
    ∃ q ∈ Q, ∀ i ∈ I, ⟨q, f ‘ i⟩ₖ ∈ forcingSeparativeOrder Q S := by
  obtain ⟨p, hp, hb⟩ := hc _ (h.projection.separative_directed_compose hf)
  refine ⟨E ‘ p, function_value_mem h.maps hp, fun i hi ↦ ?_⟩
  obtain ⟨a, ha, hea⟩ := hrange i hi
  rw [← hea]
  apply (h.separative_below (function_value_mem h.maps hp) ha).mpr
  rw [h.right_inverse p hp]
  have hbi := hb i hi
  rwa [value_compose_of_mem_function hf.1 h.projection.maps hi,
    ← hea, h.right_inverse a ha] at hbi

/-- Surjective projections reflecting compatibility transfer directed closure
without choosing representatives of the indexed family. -/
theorem IsForcingProjection.separative_directedClosedAt {P R Q S π I : V}
    (h : IsForcingProjection P R Q S π)
    (hc : ∀ a ∈ Q, ∀ b ∈ Q,
      ForcingCompatible Q S a b ↔ ForcingCompatible P R (π ‘ a) (π ‘ b))
    (hsurj : ∀ p ∈ P, ∃ q ∈ Q, π ‘ q = p)
    (hclosed : IsForcingDirectedClosedAt P (forcingSeparativeOrder P R) I) :
    IsForcingDirectedClosedAt Q (forcingSeparativeOrder Q S) I := by
  intro f hf
  obtain ⟨p, hp, hb⟩ := hclosed _ (h.separative_directed_compose hf)
  obtain ⟨q, hq, he⟩ := hsurj p hp
  refine ⟨q, hq, fun i hi ↦ ?_⟩
  apply (h.separative_iff hc hq (function_value_mem hf.1 hi)).mpr
  rw [he]
  simpa only [value_compose_of_mem_function hf.1 h.maps hi] using hb i hi

/-- Project a bound after inserting the indexed family by the split section. -/
theorem IsForcingSplitProjection.separative_directedClosedAt_of_source {P R Q S π E I : V}
    (h : IsForcingSplitProjection P R Q S π E)
    (hc : IsForcingDirectedClosedAt Q (forcingSeparativeOrder Q S) I) :
    IsForcingDirectedClosedAt P (forcingSeparativeOrder P R) I := by
  intro f hf
  have hg : IsForcingDirectedFamily Q (forcingSeparativeOrder Q S) I (compose f E) := by
    refine ⟨compose_function hf.1 h.maps, fun i hi j hj ↦ ?_⟩
    obtain ⟨k, hk, hki, hkj⟩ := hf.2 i hi j hj
    refine ⟨k, hk, ?_, ?_⟩
    · rw [value_compose_of_mem_function hf.1 h.maps hk,
        value_compose_of_mem_function hf.1 h.maps hi]
      apply (h.separative_below (function_value_mem h.maps (function_value_mem hf.1 hk))
        (function_value_mem hf.1 hi)).mpr
      rwa [h.right_inverse _ (function_value_mem hf.1 hk)]
    · rw [value_compose_of_mem_function hf.1 h.maps hk,
        value_compose_of_mem_function hf.1 h.maps hj]
      apply (h.separative_below (function_value_mem h.maps (function_value_mem hf.1 hk))
        (function_value_mem hf.1 hj)).mpr
      rwa [h.right_inverse _ (function_value_mem hf.1 hk)]
  obtain ⟨q, hq, hb⟩ := hc _ hg
  refine ⟨π ‘ q, function_value_mem h.projection.maps hq, fun i hi ↦ ?_⟩
  have hh := h.projection.separative_monotone (hb i hi)
  rwa [value_compose_of_mem_function hf.1 h.maps hi,
    h.right_inverse _ (function_value_mem hf.1 hi)] at hh

namespace ForcingContext

theorem forcingSelectedUnion_collapse_directed_bound (A : ForcingContext V) {C D H : V}
    (hC : ∀ σ ∈ C, IsForcingName A.P σ) (hH : H ∈ C ^ D)
    (f : ForcingName A.P) {κ δ α : A.Model} (hf : A.ofName f ∈ A.check D ^ α)
    (hκ : IsRegularCardinal κ) (hα : α ∈ κ) (hDC : InternalDependentChoiceAt α)
    (hs : IsForcingDirectedFamily (woodinCollapse κ δ)
      (forcingSeparativeOrder (woodinCollapse κ δ) (woodinCollapseOrder κ δ)) α
      (compose (compose (A.ofName f) (A.check H)) (A.evaluationGraph C hC))) :
    let u := A.ofName ⟨forcingSelectedUnion A.P A.R A.one C H f.val,
      forcingSelectedUnion_isName _ _ _ _ _ _⟩
    u ∈ woodinCollapse κ δ ∧ ∀ i ∈ α,
      ⟨u, (compose (compose (A.ofName f) (A.check H)) (A.evaluationGraph C hC)) ‘ i⟩ₖ ∈
        woodinCollapseOrder κ δ := by
  dsimp only
  rw [A.forcingSelectedUnion_eq_union_range hC hH f hf]
  exact woodinCollapse_separative_directed_union hκ hα hDC hs

/-- Directed families of length below the intermediate cofinality have one common support.
This transports bounds from completed stage quotients to the direct-limit quotient. -/
theorem directLimit_quotient_separative_directedClosedAt (A : ForcingContext V)
    {θ P R π E U i : V} [IsOrdinal θ] {α : A.Model}
    (h : IsSplitForcingSystem θ P π E) (hi : i ∈ θ) (hAP : A.P = P ‘ i)
    (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hsplit : ∀ j ∈ θ, ∀ k ∈ θ, j ⊆ k →
      IsForcingSplitProjection (P ‘ j) (R ‘ j) (P ‘ k) (R ‘ k)
        (π ‘ ⟨j, k⟩ₖ) (E ‘ ⟨j, k⟩ₖ))
    (hα : α ∈ internalCofinality (A.check θ))
    (hc : ∀ k ∈ θ, i ⊆ k →
      IsForcingDirectedClosedAt (A.projectionQuotient (P ‘ k) (π ‘ ⟨i, k⟩ₖ))
        (forcingSeparativeOrder (A.projectionQuotient (P ‘ k) (π ‘ ⟨i, k⟩ₖ))
          (A.projectionQuotientOrder (P ‘ k) (R ‘ k) (π ‘ ⟨i, k⟩ₖ))) α) :
    IsForcingDirectedClosedAt
      (A.projectionQuotient (forcingDirectLimit θ P π E U)
        (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i))
      (forcingSeparativeOrder
        (A.projectionQuotient (forcingDirectLimit θ P π E U)
          (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i))
        (A.projectionQuotientOrder (forcingDirectLimit θ P π E U)
          (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))
          (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i))) α := by
  intro f hf
  let D := forcingDirectLimit θ P π E U
  let ρ := forcingThreadCoordinate D i
  have hρ : ρ ∈ A.P ^ D := by
    rw [hAP]
    exact (forcingDirectLimit_splitProjection h hi hU hsplit).projection.maps
  obtain ⟨k, hk, hik, hs⟩ := A.check_directLimit_cofinal_common_support h hi hα
    (fun a ha ↦ (mem_sep_iff.mp (function_value_mem hf.1 ha)).1)
  have hkproj := forcingDirectLimit_splitProjection h hk hU hsplit
  have hτ : (π ‘ ⟨i, k⟩ₖ) ∈ A.P ^ (P ‘ k) := by
    rw [hAP]
    exact (hsplit i hi k hk hik).projection.maps
  have hcomm : ∀ q ∈ D,
      (π ‘ ⟨i, k⟩ₖ) ‘ ((forcingThreadCoordinate D k) ‘ q) = ρ ‘ q := by
    intro q hq
    rw [forcingThreadCoordinate_value hq, forcingThreadCoordinate_value hq]
    exact forcingInverseLimit_project_subset h
      (forcingDirectLimit_subset _ _ _ _ _ _ hq) hi hk hik
  have hqproj := A.projectionQuotient_splitProjection hρ hτ hkproj hcomm
  let := IsOrdinal.of_mem hα
  apply hqproj.separative_directed_bound_of_range (hc k hk hik) hf
  intro a ha
  obtain ⟨q, hq, he, hsupport⟩ := hs a ha
  have hqa := function_value_mem hf.1 ha
  rw [he] at hqa
  have hqk := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp
    (forcingDirectLimit_subset _ _ _ _ _ _ hq)).2.1 k hk
  have hval : (A.projectionQuotientMap D ρ (forcingThreadCoordinate D k)) ‘ (A.check q) =
      A.check (q ‘ k) := by
    rw [A.projectionQuotientMap_value hkproj.projection.maps hq hqa,
      forcingThreadCoordinate_value hq]
  have hqkG := function_value_mem hqproj.projection.maps hqa
  rw [hval] at hqkG
  refine ⟨A.check (q ‘ k), hqkG, ?_⟩
  rw [A.projectionQuotientMap_value hkproj.maps hqk hqkG, he]
  congr 1
  rw [forcingThreadSection_value hqk]
  apply forcingThread_eq_of_support
    (forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem h hk hqk hU))
    (forcingDirectLimit_subset _ _ _ _ _ _ hq)
    (forcingSectionThread_support h hk hqk) hsupport
  rw [forcingSectionThread_value hk, forcingSectionValue_self h hk hqk]

theorem localSelectedUnion_collapse_directed_bound (A : ForcingContext V) {C D H δ p : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hp : p ∈ A.G)
    (hC : ∀ σ ∈ C, IsForcingName A.P σ) (hH : H ∈ C ^ D)
    (f : ForcingName A.P) {κ α : A.Model}
    (hf : A.ofName f ∈ A.check D ^ α)
    (hκ : IsRegularCardinal κ) (hκδ : κ ⊆ A.check δ)
    (hα : α ∈ κ) (hDC : InternalDependentChoiceAt α)
    (hs : IsForcingDirectedFamily (woodinCollapse κ (A.check δ))
      (forcingSeparativeOrder (woodinCollapse κ (A.check δ)) (woodinCollapseOrder κ (A.check δ))) α
      (compose (compose (A.ofName f) (A.check H)) (A.evaluationGraph C hC))) :
    let ν := forcingLocalCanonicalName A.P A.R A.one δ p
      (forcingSelectedUnion A.P A.R A.one C H f.val)
    let u := A.ofName ⟨ν, forcingLocalCanonicalName_isName _ _ _ _ _ _⟩
    u ∈ woodinCollapse κ (A.check δ) ∧ ∀ i ∈ α,
      ⟨u, (compose (compose (A.ofName f) (A.check H)) (A.evaluationGraph C hC)) ‘ i⟩ₖ ∈
        woodinCollapseOrder κ (A.check δ) := by
  dsimp only
  have hu := A.forcingSelectedUnion_collapse_directed_bound hC hH f hf hκ hα hDC hs
  have hr := woodinCollapse_condition_mem_hierarchy
    (A.check_inaccessible_of_small hδ hP).regular hκδ hu.1
  rw [A.localCanonicalName_value hδ hP hp
    ⟨forcingSelectedUnion A.P A.R A.one C H f.val, forcingSelectedUnion_isName _ _ _ _ _ _⟩ hr]
  exact hu

end ForcingContext
end ZFVP
