import ZFVP.SetTheory.ForcingIterationCode
import ZFVP.ModelTheory.ForcingIsomorphismFormula

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingRecodedProjections (θ s m : V) : V :=
  definableGraph (θ ×ˢ θ) (fun z ↦ compose
    (compose (converseGraph (m ‘ (kpair.π₂ z))) ((forcingCodeπ s) ‘ z))
    (m ‘ (kpair.π₁ z))) (by definability)

noncomputable def forcingRecodedSections (θ s m : V) : V :=
  definableGraph (θ ×ˢ θ) (fun z ↦ compose
    (compose (converseGraph (m ‘ (kpair.π₁ z))) ((forcingCodeE s) ‘ z))
    (m ‘ (kpair.π₂ z))) (by definability)

noncomputable def forcingRecodedLiftMap (Q L m z : V) : V :=
  definableGraph ((Q ‘ (kpair.π₂ z)) ×ˢ (Q ‘ (kpair.π₁ z)))
    (fun w ↦ (m ‘ (kpair.π₂ z)) ‘ ((L ‘ z) ‘
      ⟨(converseGraph (m ‘ (kpair.π₂ z))) ‘ (kpair.π₁ w),
        (converseGraph (m ‘ (kpair.π₁ z))) ‘ (kpair.π₂ w)⟩ₖ)) (by definability)

instance forcingRecodedLiftMap_definable : ℒₛₑₜ-function₄[V] forcingRecodedLiftMap := by
  have h : ℒₛₑₜ-relation₅[V] (fun g Q L m z ↦ ∀ u, u ∈ g ↔
      ∃ w ∈ ((Q ‘ (kpair.π₂ z)) ×ˢ (Q ‘ (kpair.π₁ z))),
        u = ⟨w, (m ‘ (kpair.π₂ z)) ‘ ((L ‘ z) ‘
          ⟨(converseGraph (m ‘ (kpair.π₂ z))) ‘ (kpair.π₁ w),
            (converseGraph (m ‘ (kpair.π₁ z))) ‘ (kpair.π₂ w)⟩ₖ)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingRecodedLiftMap (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [forcingRecodedLiftMap, mem_definableGraph_iff]

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def forcingRecodedLifts (θ s Q m : V) : V :=
  definableGraph (θ ×ˢ θ) (forcingRecodedLiftMap Q (forcingCodeL s) m) (by definability)

noncomputable def forcingRecodedTops (θ s m : V) : V :=
  definableGraph θ (fun i ↦ (m ‘ i) ‘ ((forcingCodet s) ‘ i)) (by definability)

instance forcingRecodedProjections_definable : ℒₛₑₜ-function₃[V] forcingRecodedProjections := by
  have h : ℒₛₑₜ-relation₄[V] (fun g θ s m ↦ ∀ w, w ∈ g ↔ ∃ z ∈ θ ×ˢ θ,
    w = ⟨z, compose (compose (converseGraph (m ‘ (kpair.π₂ z))) ((forcingCodeπ s) ‘ z))
      (m ‘ (kpair.π₁ z))⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingRecodedProjections (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingRecodedProjections, mem_definableGraph_iff]

instance forcingRecodedSections_definable : ℒₛₑₜ-function₃[V] forcingRecodedSections := by
  have h : ℒₛₑₜ-relation₄[V] (fun g θ s m ↦ ∀ w, w ∈ g ↔ ∃ z ∈ θ ×ˢ θ,
    w = ⟨z, compose (compose (converseGraph (m ‘ (kpair.π₁ z))) ((forcingCodeE s) ‘ z))
      (m ‘ (kpair.π₂ z))⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingRecodedSections (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingRecodedSections, mem_definableGraph_iff]

instance forcingRecodedLifts_definable : ℒₛₑₜ-function₄[V] forcingRecodedLifts := by
  have h : ℒₛₑₜ-relation₅[V] (fun g θ s Q m ↦ ∀ w, w ∈ g ↔ ∃ z ∈ θ ×ˢ θ,
    w = ⟨z, forcingRecodedLiftMap Q (forcingCodeL s) m z⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingRecodedLifts (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [forcingRecodedLifts, mem_definableGraph_iff]

instance forcingRecodedTops_definable : ℒₛₑₜ-function₃[V] forcingRecodedTops := by
  have h : ℒₛₑₜ-relation₄[V] (fun g θ s m ↦ ∀ w, w ∈ g ↔ ∃ i ∈ θ,
    w = ⟨i, (m ‘ i) ‘ ((forcingCodet s) ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingRecodedTops (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingRecodedTops, mem_definableGraph_iff]

/-- Recode all maps using the supplied coordinate isomorphisms. -/
noncomputable def forcingRecodedCode (θ s Q T m : V) : V :=
  forcingIterationCode Q T (forcingRecodedProjections θ s m) (forcingRecodedSections θ s m)
    (forcingRecodedLifts θ s Q m) (forcingRecodedTops θ s m)

instance forcingRecodedCode_definable : Language.DefinableFunction₅ ℒₛₑₜ (forcingRecodedCode (V := V)) := by
  unfold forcingRecodedCode forcingIterationCode
  definability

variable {θ s Q T m i j : V}
variable (hs : IsForcingIterationCode θ s)
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
  (Q ‘ i) (T ‘ i) (m ‘ i))

theorem forcingRecodedProjections_value (hi : i ∈ θ) (hj : j ∈ θ) :
    (forcingRecodedProjections θ s m) ‘ ⟨i, j⟩ₖ =
      compose (compose (converseGraph (m ‘ j)) ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ)) (m ‘ i) := by
  rw [forcingRecodedProjections, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hi, hj⟩),
    kpair.π₁_kpair, kpair.π₂_kpair]

theorem forcingRecodedSections_value (hi : i ∈ θ) (hj : j ∈ θ) :
    (forcingRecodedSections θ s m) ‘ ⟨i, j⟩ₖ =
      compose (compose (converseGraph (m ‘ i)) ((forcingCodeE s) ‘ ⟨i, j⟩ₖ)) (m ‘ j) := by
  rw [forcingRecodedSections, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hi, hj⟩),
    kpair.π₁_kpair, kpair.π₂_kpair]

include hs hm in
theorem forcingRecodedProjections_function (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j) :
    (forcingRecodedProjections θ s m) ‘ ⟨i, j⟩ₖ ∈ (Q ‘ i) ^ (Q ‘ j) := by
  rw [forcingRecodedProjections_value hi hj]
  exact compose_function (compose_function (hm j hj).inverse_maps
    (hs.system.functions.projection i hi j hj hij)) (hm i hi).1

include hs hm in
theorem forcingRecodedSections_function (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j) :
    (forcingRecodedSections θ s m) ‘ ⟨i, j⟩ₖ ∈ (Q ‘ j) ^ (Q ‘ i) := by
  rw [forcingRecodedSections_value hi hj]
  exact compose_function (compose_function (hm i hi).inverse_maps
    (hs.system.functions.sectionMap i hi j hj hij)) (hm j hj).1

include hs hm in
theorem forcingRecodedProjections_image (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    {p : V} (hp : p ∈ (forcingCodeP s) ‘ j) :
    ((forcingRecodedProjections θ s m) ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ j) ‘ p) =
      (m ‘ i) ‘ (((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ p) := by
  have he := hs.system.functions.projection i hi j hj hij
  have hp' := function_value_mem (hm j hj).1 hp
  rw [forcingRecodedProjections_value hi hj,
    value_compose_of_mem_function (compose_function (hm j hj).inverse_maps he) (hm i hi).1 hp',
    value_compose_of_mem_function (hm j hj).inverse_maps he hp', (hm j hj).inverse_value hp]

include hs hm in
theorem forcingRecodedSections_image (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    {p : V} (hp : p ∈ (forcingCodeP s) ‘ i) :
    ((forcingRecodedSections θ s m) ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ i) ‘ p) =
      (m ‘ j) ‘ (((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ‘ p) := by
  have he := hs.system.functions.sectionMap i hi j hj hij
  have hp' := function_value_mem (hm i hi).1 hp
  rw [forcingRecodedSections_value hi hj,
    value_compose_of_mem_function (compose_function (hm i hi).inverse_maps he) (hm j hj).1 hp',
    value_compose_of_mem_function (hm i hi).inverse_maps he hp', (hm i hi).inverse_value hp]

include hm in
theorem forcingRecodedLifts_image (hi : i ∈ θ) (hj : j ∈ θ)
    {a b : V} (ha : a ∈ (forcingCodeP s) ‘ j) (hb : b ∈ (forcingCodeP s) ‘ i) :
    ((forcingRecodedLifts θ s Q m) ‘ ⟨i, j⟩ₖ) ‘ ⟨(m ‘ j) ‘ a, (m ‘ i) ‘ b⟩ₖ =
      (m ‘ j) ‘ (((forcingCodeL s) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ) := by
  rw [forcingRecodedLifts, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hi, hj⟩)]
  simp only [forcingRecodedLiftMap, kpair.π₁_kpair, kpair.π₂_kpair]
  rw [value_definableGraph _ _ _ (kpair_mem_iff.mpr
    ⟨function_value_mem (hm j hj).1 ha, function_value_mem (hm i hi).1 hb⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair, (hm j hj).inverse_value ha, (hm i hi).inverse_value hb]

include hs hm in
theorem forcingRecodedProjections_inverse (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    {q : V} (hq : q ∈ Q ‘ j) :
    (converseGraph (m ‘ i)) ‘ (((forcingRecodedProjections θ s m) ‘ ⟨i, j⟩ₖ) ‘ q) =
      ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ ((converseGraph (m ‘ j)) ‘ q) := by
  obtain ⟨p, hp, rfl⟩ := (hm j hj).surjective q hq
  rw [forcingRecodedProjections_image hs hm hi hj hij hp,
    (hm i hi).inverse_value (hs.system.split.projMaps i hi j hj hij p hp), (hm j hj).inverse_value hp]

include hs hm in
theorem forcingRecodedSections_inverse (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    {q : V} (hq : q ∈ Q ‘ i) :
    (converseGraph (m ‘ j)) ‘ (((forcingRecodedSections θ s m) ‘ ⟨i, j⟩ₖ) ‘ q) =
      ((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ‘ ((converseGraph (m ‘ i)) ‘ q) := by
  obtain ⟨p, hp, rfl⟩ := (hm i hi).surjective q hq
  rw [forcingRecodedSections_image hs hm hi hj hij hp,
    (hm j hj).inverse_value (hs.system.split.secMaps i hi j hj hij p hp), (hm i hi).inverse_value hp]

theorem forcingRecodedTops_value (hi : i ∈ θ) :
    (forcingRecodedTops θ s m) ‘ i = (m ‘ i) ‘ ((forcingCodet s) ‘ i) :=
  value_definableGraph _ _ _ hi

end ZFVP
