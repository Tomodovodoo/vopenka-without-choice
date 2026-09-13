import ZFVP.ModelTheory.ForcingNormalizationFamily
import ZFVP.ModelTheory.ForcingThreadRetraction
import ZFVP.ModelTheory.LimitCodeDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingNormalizationDirectMap (θ s m : V) : V :=
  forcingThreadActionMap θ m ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)

/-- The raw inverse thread map, before the appended Hartogs collapse. -/
noncomputable def forcingNormalizationInverseMap (θ s m : V) : V :=
  forcingThreadActionMap θ m ((forcingCodeP (forcingInverseCode θ s)) ‘ θ)

noncomputable def forcingNormalizationDirect (θ s m : V) : V :=
  forcingFamilyNext θ m (forcingNormalizationDirectMap θ s m)

noncomputable def forcingNormalizationInverse (θ s m : V) : V :=
  forcingFamilyNext θ m (forcingNormalizationInverseMap θ s m)

instance forcingNormalizationDirectMap_definable : ℒₛₑₜ-function₃[V] forcingNormalizationDirectMap := by
  unfold forcingNormalizationDirectMap
  apply Language.DefinableFunction₃.comp <;> definability

instance forcingNormalizationInverseMap_definable : ℒₛₑₜ-function₃[V] forcingNormalizationInverseMap := by
  unfold forcingNormalizationInverseMap
  apply Language.DefinableFunction₃.comp <;> definability

instance forcingNormalizationDirect_definable : ℒₛₑₜ-function₃[V] forcingNormalizationDirect := by
  unfold forcingNormalizationDirect
  apply Language.DefinableFunction₃.comp <;> definability

instance forcingNormalizationInverse_definable : ℒₛₑₜ-function₃[V] forcingNormalizationInverse := by
  unfold forcingNormalizationInverse
  apply Language.DefinableFunction₃.comp <;> definability

variable {θ s m : V}
local notation "N" => forcingNormalizationCarriers θ s m
local notation "U" => forcingCodeUniverse s
local notation "D" => forcingDirectLimit θ N (forcingCodeπ s) (forcingCodeE s) U
local notation "I" => forcingInverseLimit θ N (forcingCodeπ s) U

theorem forcingNormalizationDirect_retraction (hs : IsForcingIterationCode θ s)
    (h : IsForcingNormalizationFamily θ s m) :
    IsForcingRetraction D (forcingThreadOrder θ (forcingCodeR s) D)
      ((forcingCodeP (forcingDirectCode θ s)) ‘ θ) ((forcingCodeR (forcingDirectCode θ s)) ‘ θ)
      (forcingNormalizationDirectMap θ s m) := by
  simpa only [forcingNormalizationDirectMap, forcingDirectCode, forcingThreadCode_poset,
    forcingThreadCode_order] using forcingDirectLimit_retraction hs.system.order.preorder
      hs.subset_universe h.inclusion h.maps h.fixes h.equivalent h.projection h.sectionCoherent

theorem forcingNormalizationInverse_retraction (hs : IsForcingIterationCode θ s)
    (h : IsForcingNormalizationFamily θ s m) :
    IsForcingRetraction I (forcingThreadOrder θ (forcingCodeR s) I)
      ((forcingCodeP (forcingInverseCode θ s)) ‘ θ) ((forcingCodeR (forcingInverseCode θ s)) ‘ θ)
      (forcingNormalizationInverseMap θ s m) := by
  simpa only [forcingNormalizationInverseMap, forcingInverseCode, forcingThreadCode_poset,
    forcingThreadCode_order] using forcingInverseLimit_retraction hs.system.order.preorder
      hs.subset_universe h.inclusion h.maps h.fixes h.equivalent h.projection

theorem forcingNormalizationDirect_coordinate {f i : V} (hi : i ∈ θ)
    (hf : f ∈ (forcingCodeP (forcingDirectCode θ s)) ‘ θ) :
    ((forcingNormalizationDirectMap θ s m) ‘ f) ‘ i = (m ‘ i) ‘ (f ‘ i) := by
  rw [forcingNormalizationDirectMap, forcingThreadActionMap_value hf, forcingThreadAction_value hi]

theorem forcingNormalizationInverse_coordinate {f i : V} (hi : i ∈ θ)
    (hf : f ∈ (forcingCodeP (forcingInverseCode θ s)) ‘ θ) :
    ((forcingNormalizationInverseMap θ s m) ‘ f) ‘ i = (m ‘ i) ‘ (f ‘ i) := by
  rw [forcingNormalizationInverseMap, forcingThreadActionMap_value hf, forcingThreadAction_value hi]

theorem forcingNormalizationDirect_old {i : V} (hi : i ∈ θ) :
    (forcingNormalizationDirect θ s m) ‘ i = m ‘ i := forcingFamilyNext_old hi

theorem forcingNormalizationInverse_old {i : V} (hi : i ∈ θ) :
    (forcingNormalizationInverse θ s m) ‘ i = m ‘ i := forcingFamilyNext_old hi

theorem forcingNormalizationDirect_new :
    (forcingNormalizationDirect θ s m) ‘ θ = forcingNormalizationDirectMap θ s m := forcingFamilyNext_new _ _ _

theorem forcingNormalizationInverse_new :
    (forcingNormalizationInverse θ s m) ‘ θ = forcingNormalizationInverseMap θ s m := forcingFamilyNext_new _ _ _

theorem forcingNormalizationDirect_table : IsIterationTable (succ θ) (forcingNormalizationDirect θ s m) :=
  forcingFamilyNext_table _ _ _

theorem forcingNormalizationInverse_table : IsIterationTable (succ θ) (forcingNormalizationInverse θ s m) :=
  forcingFamilyNext_table _ _ _

theorem IsForcingNormalizationFamily.thread_section [IsOrdinal θ]
    (h : IsForcingNormalizationFamily θ s m) {k p : V} (hk : k ∈ θ)
    (hp : p ∈ (forcingCodeP s) ‘ k) :
    forcingThreadAction θ m (forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) k p) =
      forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) k ((m ‘ k) ‘ p) := by
  unfold forcingThreadAction forcingSectionThread
  apply functions_eq_of_domain_values
  · rw [domain_definableGraph, domain_definableGraph]
  intro i hi
  rw [domain_definableGraph] at hi
  rw [value_definableGraph _ _ _ hi, value_definableGraph _ _ _ hi,
    value_definableGraph _ _ _ hi]
  classical
  unfold forcingSectionValue
  by_cases hik : i ∈ k
  · simp only [hik, ↓reduceIte]
    exact (h.projection k hk i hik hi p hp).symm
  · simp only [hik, ↓reduceIte]
    let := IsOrdinal.of_mem hk
    let := IsOrdinal.of_mem hi
    have hki : k ⊆ i := by
      rcases IsOrdinal.mem_trichotomy i k with hh | rfl | hh
      · exact (hik hh).elim
      · exact subset_refl _
      · exact IsOrdinal.toIsTransitive.transitive _ hh
    exact h.sectionCoherent k hk i hi hki p hp

theorem forcingNormalizationDirect_top [IsOrdinal θ] (hs : IsForcingIterationCode θ s)
    (h : IsForcingNormalizationFamily θ s m) (h0 : ∅ ∈ θ) :
    (forcingNormalizationDirectMap θ s m) ‘ ((forcingCodet (forcingDirectCode θ s)) ‘ θ) =
      (forcingCodet (forcingDirectCode θ s)) ‘ θ := by
  have ht := (forcingDirectCode_valid hs h0).system.tops.top θ (mem_succ_self θ)
  rw [forcingNormalizationDirectMap, forcingThreadActionMap_value ht.1]
  simp only [forcingDirectCode, forcingThreadCode_top]
  rw [h.thread_section h0 (hs.system.tops.top ∅ h0).1, h.fixesTop ∅ h0]

theorem forcingNormalizationInverse_top [IsOrdinal θ] (hs : IsForcingIterationCode θ s)
    (h : IsForcingNormalizationFamily θ s m) (h0 : ∅ ∈ θ) :
    (forcingNormalizationInverseMap θ s m) ‘ ((forcingCodet (forcingInverseCode θ s)) ‘ θ) =
      (forcingCodet (forcingInverseCode θ s)) ‘ θ := by
  have ht := (forcingInverseCode_valid hs h0).system.tops.top θ (mem_succ_self θ)
  rw [forcingNormalizationInverseMap, forcingThreadActionMap_value ht.1]
  simp only [forcingInverseCode, forcingThreadCode_top]
  rw [h.thread_section h0 (hs.system.tops.top ∅ h0).1, h.fixesTop ∅ h0]

theorem forcingNormalizationDirect_equivalent (hs : IsForcingIterationCode θ s)
    (h : IsForcingNormalizationFamily θ s m) {f : V}
    (hf : f ∈ (forcingCodeP (forcingDirectCode θ s)) ‘ θ) :
    ⟨(forcingNormalizationDirectMap θ s m) ‘ f, f⟩ₖ ∈ (forcingCodeR (forcingDirectCode θ s)) ‘ θ ∧
      ⟨f, (forcingNormalizationDirectMap θ s m) ‘ f⟩ₖ ∈ (forcingCodeR (forcingDirectCode θ s)) ‘ θ := by
  simp only [forcingDirectCode, forcingThreadCode_poset] at hf
  simp only [forcingNormalizationDirectMap, forcingDirectCode, forcingThreadCode_poset, forcingThreadCode_order]
  exact forcingThreadActionMap_equivalent
    (fun _ hg ↦ ((mem_forcingInverseLimit_iff _ _ _ _ _).mp
      (forcingDirectLimit_subset _ _ _ _ _ _ hg)).2.1)
    (forcingDirectLimit_mono_coordinates h.inclusion)
    (fun _ hg ↦ forcingThreadAction_mem_direct h.maps
      (fun i hi p hp ↦ hs.subset_universe i hi p (h.inclusion i hi p hp)) h.projection h.sectionCoherent hg)
    h.equivalent hf

theorem forcingNormalizationInverse_equivalent (hs : IsForcingIterationCode θ s)
    (h : IsForcingNormalizationFamily θ s m) {f : V}
    (hf : f ∈ (forcingCodeP (forcingInverseCode θ s)) ‘ θ) :
    ⟨(forcingNormalizationInverseMap θ s m) ‘ f, f⟩ₖ ∈ (forcingCodeR (forcingInverseCode θ s)) ‘ θ ∧
      ⟨f, (forcingNormalizationInverseMap θ s m) ‘ f⟩ₖ ∈ (forcingCodeR (forcingInverseCode θ s)) ‘ θ := by
  simp only [forcingInverseCode, forcingThreadCode_poset] at hf
  simp only [forcingNormalizationInverseMap, forcingInverseCode, forcingThreadCode_poset, forcingThreadCode_order]
  exact forcingThreadActionMap_equivalent
    (fun _ hg ↦ ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hg).2.1)
    (forcingInverseLimit_mono_coordinates h.inclusion)
    (fun _ hg ↦ forcingThreadAction_mem_inverse h.maps
      (fun i hi p hp ↦ hs.subset_universe i hi p (h.inclusion i hi p hp)) h.projection hg)
    h.equivalent hf

end ZFVP
