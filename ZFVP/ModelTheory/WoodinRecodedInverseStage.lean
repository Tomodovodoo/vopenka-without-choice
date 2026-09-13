import ZFVP.ModelTheory.WoodinRecodedInverse
import ZFVP.ModelTheory.WoodinNormalizedInverseCutoff
import ZFVP.ModelTheory.NormalizedHartogsIsomorphism
import ZFVP.ModelTheory.NormalizedIsomorphismDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinRecodedInverseMap (θ c m : V) : V :=
  let P := woodinNormalizedInverseBase θ
  let R := woodinNormalizedInverseOrder θ
  let one := forcingInverseCodeTop θ (woodinIterationPrefix θ)
  let δ := woodinNormalizedInverseCutoff θ
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
  normalizedTwoStepIsoMap P R one δ (saturatedHartogsPosetName P R one γ δ)
    (forcingInverseCodePoset θ c) (forcingInverseCodeOrder θ c) (forcingInverseCodeTop θ c)
    (woodinRecodedInverseBaseMap θ m)

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance woodinRecodedInverseMap_definable : ℒₛₑₜ-function₃[V] woodinRecodedInverseMap := by
  unfold woodinRecodedInverseMap
  dsimp only
  apply normalizedTwoStepIsoMap_comp <;> definability

variable {Ω θ Q T m : V} [IsOrdinal θ]
local notation "N" => woodinNormalizedPrefixCode θ
local notation "c" => forcingRecodedCode θ N Q T m
local notation "A" => forcingInverseCodePoset θ c
local notation "B" => forcingInverseCodeOrder θ c
local notation "top" => forcingInverseCodeTop θ c
local notation "γ" => woodinLimitCardinal (woodinIterationCardinalPrefix θ)
local notation "δ" => woodinNormalizedInverseCutoff θ

theorem woodinRecodedInverseMap_isomorphism
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ)
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP N) ‘ i) ((forcingCodeR N) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
    (hQrank : ∀ i ∈ θ, Q ‘ i ∈ hierarchy δ) :
    let ε := woodinNamedPrefixCutoff A B top γ (hartogsNumberName A B (checkName top γ))
    let iter := saturatedHartogsPosetName A B top γ ε
    IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinNormalizedStageCode θ)) ‘ θ)
      (normalizedNameTwoStep A B top ε iter)
      (nameTwoStepOrderOn A B (saturatedHartogsOrderName A B top γ ε)
        (normalizedNameTwoStep A B top ε iter)) (woodinRecodedInverseMap θ c m) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hsub) hm hT hQt hTt
  have col := hc.system.inverseColumn hz hc.subset_universe
  have ht : IsForcingTop A B top := col.tops.top
  have hb := woodinNormalized_inverse_base_laws hΩ hAC hsub hz
  have hf := woodinRecodedInverseBaseMap_isomorphism hΩ hAC hsub hm hT hQt hTt
  have hft := woodinRecodedInverseBaseMap_top hΩ hAC hsub hm hT hQt hTt hz
  obtain ⟨_, hd, hθd, hP⟩ := woodinNormalizedInverseCutoff_bounds hΩ hAC hθ h0 hlim hn
  let := hd.1
  have hA : A ∈ hierarchy δ := by
    have hh := (forcingInverseLimit_small_family (R := T) (π := forcingRecodedProjections θ N m)
      hd (ordinal_mem_hierarchy_iff.mpr hθd) (hQt.mem_function hQrank)).1
    simpa only [forcingInverseCodePoset, forcingCodeUniverse, forcingRecodedCode, forcingCodeP_code,
      forcingCodeπ_code] using hh
  obtain ⟨hp, hr⟩ := woodinNormalized_inverse_dictionary hΩ hAC hθ h0 hlim hn
  dsimp only at hp hr ⊢
  rw [hp, hr]
  exact normalizedHartogsSuccessor_isomorphism hf hb.1 col.order.preorder hb.2 ht hft hd hP hA

theorem woodinRecodedInverseMap_value {z : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ)
    (hz : z ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ) :
    (woodinRecodedInverseMap θ c m) ‘ z =
      normalizedTwoStepIsoValue A B top (woodinRecodedInverseBaseMap θ m) z := by
  rw [(woodinNormalized_inverse_dictionary hΩ hAC hθ h0 hlim hn).1] at hz
  rw [woodinRecodedInverseMap, woodinNormalizedInverseCutoff, normalizedTwoStepIsoMap_value hz]

theorem woodinRecodedInverseMap_coordinate {z i : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ)
    (hz : z ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ) (hi : i ∈ θ) :
    (kpair.π₁ ((woodinRecodedInverseMap θ c m) ‘ z)) ‘ i = (m ‘ i) ‘ ((kpair.π₁ z) ‘ i) := by
  rw [woodinRecodedInverseMap_value hΩ hAC hθ h0 hlim hn hz, normalizedTwoStepIsoValue_prefix]
  rw [(woodinNormalized_inverse_dictionary hΩ hAC hθ h0 hlim hn).1] at hz
  obtain ⟨p, hp, τ, _, rfl⟩ := mem_prod_iff.mp hz
  simp only [kpair.π₁_kpair]
  exact woodinRecodedInverseBaseMap_coordinate hp hi

theorem woodinRecodedInverseMap_empty_tail {p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ)
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP N) ‘ i) ((forcingCodeR N) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
    (hp : ⟨p, ∅⟩ₖ ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ) :
    (woodinRecodedInverseMap θ c m) ‘ ⟨p, ∅⟩ₖ = ⟨(woodinRecodedInverseBaseMap θ m) ‘ p, ∅⟩ₖ := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hsub) hm hT hQt hTt
  have col := hc.system.inverseColumn hz hc.subset_universe
  rw [woodinRecodedInverseMap_value hΩ hAC hθ h0 hlim hn hp]
  exact normalizedTwoStepIsoValue_empty_tail col.order.preorder col.tops.top.1

end ZFVP
