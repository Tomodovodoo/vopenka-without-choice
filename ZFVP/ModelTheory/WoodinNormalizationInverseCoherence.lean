import ZFVP.ModelTheory.WoodinNormalizationInverse

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s K m : V}
local notation "P" => forcingInverseCodePoset θ s
local notation "R" => forcingInverseCodeOrder θ s
local notation "o" => forcingInverseCodeTop θ s
local notation "γ" => woodinLimitCardinal K
local notation "c" => forcingInverseSourceCutoff θ s γ
local notation "Q" => saturatedHartogsPosetName P R o γ c
local notation "S" => saturatedHartogsOrderName P R o γ c
local notation "r" => forcingNormalizationInverseMap θ s m
local notation "N" => forcingMapFixedPoints P r
local notation "T" => forcingOrderRestriction N R
local notation "z'" => woodinInverseSourceCode θ s K

theorem woodinInverseSourceCode_twoStepColumn :
    z' = forcingTwoStepColumnCode θ s P R (forcingLimitProjectionColumn θ P)
      (forcingLimitSectionColumn θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s))
      (forcingLimitLiftColumn P θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeL s)) o Q S ∅ := rfl

theorem woodinInverseSourceCode_projection_value [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R o) (hI : IsForcingIterand P R Q S ∅)
    {i z : V} (hi : i ∈ θ) (hz : z ∈ (forcingCodeP z') ‘ θ) :
    ((forcingCodeπ z') ‘ ⟨i, θ⟩ₖ) ‘ z = (kpair.π₁ z) ‘ i := by
  rw [woodinInverseSourceCode_poset] at hz
  have hfirst : kpair.π₁ z ∈ P := by
    obtain ⟨p, hp, τ, _, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hz
    simpa using hp
  have col := hs.system.inverseColumn h0 hs.subset_universe
  have hm : (forcingLimitProjectionColumn θ P) ‘ i ∈ ((forcingCodeP s) ‘ i) ^ P :=
    col.functions.projection i hi
  simp only [woodinInverseSourceCode_twoStepColumn, forcingTwoStepColumnCode, forcingIterationCodeNext,
    forcingCodeπ_code, forcingMatrixNext_column hi]
  rw [forcingComposeProjectionColumn_twoStep_value hi hm hR ht hI hz,
    forcingLimitProjectionColumn_value hi, forcingThreadCoordinate_value hfirst]

theorem woodinInverseSourceCode_section_value [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R o) (hI : IsForcingIterand P R Q S ∅)
    {i p : V} (hi : i ∈ θ) (hp : p ∈ (forcingCodeP s) ‘ i) :
    ((forcingCodeE z') ‘ ⟨i, θ⟩ₖ) ‘ p =
      ⟨forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) i p, ∅⟩ₖ := by
  have col := hs.system.inverseColumn h0 hs.subset_universe
  have hm : (forcingLimitSectionColumn θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s)) ‘ i ∈
      P ^ ((forcingCodeP s) ‘ i) := col.functions.sectionMap i hi
  simp only [woodinInverseSourceCode_twoStepColumn, forcingTwoStepColumnCode, forcingIterationCodeNext,
    forcingCodeE_code, forcingMatrixNext_column hi]
  rw [forcingComposeSectionColumn_value hi,
    value_compose_of_mem_function hm (twoStep_splitProjection hR ht hI).maps hp,
    twoStepSection_value (function_value_mem hm hp), forcingLimitSectionColumn_value hi,
    forcingThreadSection_value hp]

theorem woodinNormalizationInverse_projection_coherent [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ)
    (hr : IsForcingRetraction N T P R r) (hR : IsForcingPreorder P R) (ht : IsForcingTop P R o)
    (hc : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c) (hI : IsForcingIterand P R Q S ∅)
    (ho : r ‘ o = o) (he : ∀ p ∈ P, ⟨r ‘ p, p⟩ₖ ∈ R ∧ ⟨p, r ‘ p⟩ₖ ∈ R)
    {i z : V} (hi : i ∈ θ) (hz : z ∈ (forcingCodeP z') ‘ θ) :
    ((forcingCodeπ z') ‘ ⟨i, θ⟩ₖ) ‘ ((woodinNormalizationInverseMap θ s K m) ‘ z) =
      (m ‘ i) ‘ (((forcingCodeπ z') ‘ ⟨i, θ⟩ₖ) ‘ z) := by
  have hn := woodinNormalizationInverseMap_retraction hr hR ht hc hP hI ho he
  have hm := hn.inclusion _ (function_value_mem hn.maps hz)
  have hfirst : kpair.π₁ z ∈ (forcingCodeP (forcingInverseCode θ s)) ‘ θ := by
    rw [woodinInverseSourceCode_poset] at hz
    obtain ⟨p, hp, τ, _, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hz
    simpa only [kpair.π₁_kpair, forcingInverseCode, forcingThreadCode_poset, forcingInverseCodePoset] using hp
  rw [woodinInverseSourceCode_projection_value hs h0 hR ht hI hi hm,
    woodinInverseSourceCode_projection_value hs h0 hR ht hI hi hz,
    woodinNormalizationInverseMap_prefix hr hR ht hc hP hI ho he hz,
    forcingNormalizationInverse_coordinate hi hfirst]

theorem woodinNormalizationInverse_section_coherent [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (h : IsForcingNormalizationFamily θ s m) (h0 : ∅ ∈ θ)
    (hr : IsForcingRetraction N T P R r) (hR : IsForcingPreorder P R) (ht : IsForcingTop P R o)
    (hc : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c) (hI : IsForcingIterand P R Q S ∅)
    (ho : r ‘ o = o) (he : ∀ p ∈ P, ⟨r ‘ p, p⟩ₖ ∈ R ∧ ⟨p, r ‘ p⟩ₖ ∈ R)
    {i p : V} (hi : i ∈ θ) (hp : p ∈ (forcingCodeP s) ‘ i) :
    (woodinNormalizationInverseMap θ s K m) ‘ (((forcingCodeE z') ‘ ⟨i, θ⟩ₖ) ‘ p) =
      ((forcingCodeE z') ‘ ⟨i, θ⟩ₖ) ‘ ((m ‘ i) ‘ p) := by
  have hmp := (h.retraction i hi).inclusion _ (function_value_mem (h.retraction i hi).maps hp)
  have hsec : forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) i p ∈ P :=
    forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem hs.system.split hi hp hs.subset_universe)
  have hsec' : forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) i p ∈
      (forcingCodeP (forcingInverseCode θ s)) ‘ θ := by
    simpa only [forcingInverseCode, forcingThreadCode_poset, forcingInverseCodePoset] using hsec
  rw [woodinInverseSourceCode_section_value hs h0 hR ht hI hi hp,
    woodinInverseSourceCode_section_value hs h0 hR ht hI hi hmp,
    woodinNormalizationInverseMap_empty_tail hr hR ht hc hP hI ho he hsec,
    forcingNormalizationInverseMap, forcingThreadActionMap_value hsec', h.thread_section hi hp]

end ZFVP
