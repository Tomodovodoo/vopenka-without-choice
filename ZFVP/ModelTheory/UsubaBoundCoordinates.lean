import ZFVP.ModelTheory.UsubaBoundInvariant
import ZFVP.ModelTheory.QuotientSequenceProjection
import ZFVP.ModelTheory.IdentityQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

theorem usubaBoundCoordinate_value {θ i j : V} [IsOrdinal i]
    {G : Set V} (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G)
    (f : ForcingName ((T).P i)) :
    let A := usubaStageContext i hG
    A.ofName ⟨usubaBoundCoordinateName θ i f.val j, usubaBoundCoordinateName_isName _ _ _ _⟩ =
      compose (A.ofName f) (A.check ((T).projection j θ)) :=
  (usubaStageContext i hG).forcingCompositionName_value f
    ⟨checkName ((T).top i) ((T).projection j θ), checkName_isName ((T).top_spec i inferInstance).1 _⟩

theorem usubaBoundCoordinate_descending {θ i j : V} [IsOrdinal θ] [IsOrdinal i] [IsOrdinal j]
    (hij : i ⊆ j) (hjθ : j ⊆ θ)
    {G : Set V} (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G)
    (f : ForcingName ((T).P i)) {α : (usubaStageContext i hG).Model} [IsOrdinal α]
    (hf : let A := usubaStageContext i hG
      IsForcingDescending (A.projectionQuotient ((T).P θ) ((T).projection i θ))
        (forcingSeparativeOrder (A.projectionQuotient ((T).P θ) ((T).projection i θ))
          (A.projectionQuotientOrder ((T).P θ) ((T).R θ) ((T).projection i θ))) α (A.ofName f)) :
    let A := usubaStageContext i hG
    IsForcingDescending (A.projectionQuotient ((T).P j) ((T).projection i j))
      (forcingSeparativeOrder (A.projectionQuotient ((T).P j) ((T).projection i j))
        (A.projectionQuotientOrder ((T).P j) ((T).R j) ((T).projection i j))) α
      (A.ofName ⟨usubaBoundCoordinateName θ i f.val j, usubaBoundCoordinateName_isName _ _ _ _⟩) := by
  exact (usubaStageContext i hG).projectionQuotient_name_descending
    ((T).projection_function i θ inferInstance inferInstance (subset_trans hij hjθ))
    ((T).projection_function i j inferInstance inferInstance hij)
    ((T).splitProjection hjθ).projection
    ((T).projection_comp i j θ inferInstance inferInstance inferInstance hij hjθ) f hf

theorem usubaBoundCoordinate_self {θ i : V} [IsOrdinal θ] [IsOrdinal i]
    {G : Set V} (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G)
    (f : ForcingName ((T).P i)) {α : (usubaStageContext i hG).Model}
    (hf : (usubaStageContext i hG).ofName f ∈ (usubaStageContext i hG).check ((T).P θ) ^ α) :
    let A := usubaStageContext i hG
    A.ofName ⟨usubaBoundCoordinateName θ i f.val θ, usubaBoundCoordinateName_isName _ _ _ _⟩ =
      A.ofName f := by
  let A := usubaStageContext i hG
  have hm := (T).projection_function θ θ inferInstance inferInstance (subset_refl θ)
  let := IsFunction.of_mem hm
  dsimp only
  rw [usubaBoundCoordinate_value (θ := θ) (j := θ) hG f]
  apply function_eq_of_values (compose_function hf ((A.check_function_iff _ _ _).mpr hm)) hf
  intro a ha
  obtain ⟨d, hd, had⟩ := (A.mem_check_iff _ _).mp (function_value_mem hf ha)
  rw [value_compose_of_mem_function hf ((A.check_function_iff _ _ _).mpr hm) ha, had,
    A.check_value ((domain_eq_of_mem_function hm).symm ▸ hd), (T).projection_self θ inferInstance d hd]

theorem usubaBoundCoordinate_at {θ i j d : V} [IsOrdinal θ] [IsOrdinal i] [IsOrdinal j]
    (hjθ : j ⊆ θ) {G : Set V} (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G)
    (f : ForcingName ((T).P i)) {α a : (usubaStageContext i hG).Model}
    (hf : (usubaStageContext i hG).ofName f ∈ (usubaStageContext i hG).check ((T).P θ) ^ α)
    (ha : a ∈ α) (hd : d ∈ (T).P θ)
    (had : ((usubaStageContext i hG).ofName f) ‘ a = (usubaStageContext i hG).check d) :
    let A := usubaStageContext i hG
    (A.ofName ⟨usubaBoundCoordinateName θ i f.val j, usubaBoundCoordinateName_isName _ _ _ _⟩) ‘ a =
      A.check (((T).projection j θ) ‘ d) := by
  let A := usubaStageContext i hG
  have hm := (T).projection_function j θ inferInstance inferInstance hjθ
  let := IsFunction.of_mem hm
  dsimp only
  rw [usubaBoundCoordinate_value (θ := θ) (j := j) hG f,
    value_compose_of_mem_function hf ((A.check_function_iff _ _ _).mpr hm) ha, had,
    A.check_value ((domain_eq_of_mem_function hm).symm ▸ hd)]

theorem usubaQuotientBoundAt_before_base {θ i p f α j : V} [IsOrdinal i]
    (hji : j ∈ i) (hp : p ∈ (T).P i) : IsUsubaQuotientBoundAt θ i p f α j := by
  let := IsOrdinal.of_mem hji
  refine ⟨?_, fun hij ↦ False.elim (mem_irrefl j (hij j hji))⟩
  rw [usubaQuotientBoundRec_before hji]
  exact (T).projection_mem (IsOrdinal.toIsTransitive.transitive _ hji) hp

theorem usubaBoundCoordinate_successor_first {θ i k : V}
    [IsOrdinal θ] [IsOrdinal i] [IsOrdinal k] (hkθ : succ k ⊆ θ)
    {G : Set V} (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G)
    (f : ForcingName ((T).P i)) {α : (usubaStageContext i hG).Model}
    (hf : (usubaStageContext i hG).ofName f ∈ (usubaStageContext i hG).check ((T).P θ) ^ α) :
    let A := usubaStageContext i hG
    compose (A.ofName ⟨usubaBoundCoordinateName θ i f.val (succ k), usubaBoundCoordinateName_isName _ _ _ _⟩)
      (A.check (twoStepProjection ((T).P k) ((T).R k) (usubaSaturatedPosetName ((T).P k) ((T).R k)) ∅)) =
    A.ofName ⟨usubaBoundCoordinateName θ i f.val k, usubaBoundCoordinateName_isName _ _ _ _⟩ := by
  let A := usubaStageContext i hG
  let ρ := twoStepProjection ((T).P k) ((T).R k) (usubaSaturatedPosetName ((T).P k) ((T).R k)) ∅
  have hρ : ρ ∈ (T).P k ^ (T).P (succ k) := by
    rw [usubaTower_P_succ]
    exact twoStepProjection_maps _ _ _ _
  have hπ := (T).projection_function (succ k) θ inferInstance inferInstance hkθ
  have hkθ' : k ⊆ θ := subset_trans (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k)) hkθ
  have hτ := (T).projection_function k θ inferInstance inferInstance hkθ'
  have hnew := compose_function hf ((A.check_function_iff _ _ _).mpr hπ)
  have hold := compose_function hf ((A.check_function_iff _ _ _).mpr hτ)
  have hleft := compose_function hnew ((A.check_function_iff _ _ _).mpr hρ)
  dsimp only
  rw [usubaBoundCoordinate_value (θ := θ) (j := succ k) hG f,
    usubaBoundCoordinate_value (θ := θ) (j := k) hG f]
  apply function_eq_of_values hleft hold
  intro a ha
  have haθ := function_value_mem hf ha
  obtain ⟨d, hd, had⟩ := (A.mem_check_iff _ _).mp haθ
  have hpd := (T).projection_mem hkθ hd
  have hpd' := hpd
  rw [usubaTower_P_succ] at hpd'
  let := IsFunction.of_mem hπ
  let := IsFunction.of_mem hτ
  let := IsFunction.of_mem hρ
  rw [value_compose_of_mem_function hnew ((A.check_function_iff _ _ _).mpr hρ) ha,
    value_compose_of_mem_function hf ((A.check_function_iff _ _ _).mpr hπ) ha,
    value_compose_of_mem_function hf ((A.check_function_iff _ _ _).mpr hτ) ha,
    had, A.check_value (f := (T).projection (succ k) θ) ((domain_eq_of_mem_function hπ).symm ▸ hd),
    A.check_value (f := (T).projection k θ) ((domain_eq_of_mem_function hτ).symm ▸ hd),
    A.check_value (f := ρ) ((domain_eq_of_mem_function hρ).symm ▸ hpd)]
  apply congrArg A.check
  rw [twoStepProjection_value hpd', ← usubaTower_projection_first hpd]
  exact (T).projection_comp k (succ k) θ inferInstance inferInstance inferInstance
    (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k)) hkθ d hd

theorem usubaQuotientBoundAt_base [Countable V] {θ i p α : V}
    [IsOrdinal θ] [IsOrdinal i] [IsOrdinal α] (hiθ : i ⊆ θ)
    (hp : p ∈ (T).P i) (f : ForcingName ((T).P i))
    (hf : ForcesUsubaQuotientSequence θ i p f.val α) :
    IsUsubaNormalizedQuotientBoundAt θ i p f.val α i := by
  refine ⟨?_, fun hii ↦ False.elim (mem_irrefl _ hii)⟩
  apply (usubaQuotientBoundAt_iff_generics (subset_refl i) hp f).mpr
  refine ⟨?_, ?_⟩
  · rwa [usubaQuotientBoundRec_base]
  · intro G hG hpG
    let A := usubaStageContext i hG
    have hdesc := usubaQuotientSequence_semantics hiθ f hf hG hpG
    have hd := usubaBoundCoordinate_descending (subset_refl i) hiθ hG f hdesc
    have hm := (T).projection_function i i inferInstance inferInstance (subset_refl i)
    have he := (T).projection_self i inferInstance
    have hpQ : A.check p ∈ A.projectionQuotient ((T).P i) ((T).projection i i) :=
      (A.check_mem_projectionQuotient_iff hm).mpr ⟨hp, (he p hp).symm ▸ hpG⟩
    dsimp only
    rw [usubaQuotientBoundRec_base]
    exact ⟨hpQ, fun a ha ↦ A.identityQuotient_separative hm he hpQ (function_value_mem hd.1 ha)⟩

end ZFVP
