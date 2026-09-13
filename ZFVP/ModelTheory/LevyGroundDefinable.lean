import ZFVP.ModelTheory.CheckedSetCodes
import ZFVP.ModelTheory.LevyGroundStageChoice
import ZFVP.ModelTheory.LevyExtensionHartogs
import ZFVP.SetTheory.GroundPredicate

/-! Laver's theorem for the Levy collapse: the ground model is definable from one parameter.

`IsGround x r` is the parameter-free predicate of `ZFVP.GroundPredicate`, read with the parameter
`r = ⟨(κ⁺)ˇ, ⟨(℘ (κ⁺ ×ˢ κ⁺))ˇ, (℘ κ⁺)ˇ⟩⟩`. In the Levy extension it picks out exactly the checks.

One direction is recognition: a ground set has a set code whose collapse data are all checks, and
a closed rank stage of the ground holds that code, so the check of the stage witnesses `IsGround`.
The other is uniqueness: any witness `M` of `IsGround x r` is ground-like over `(κ⁺)ˇ` and agrees
with the check of a closed stage on subsets of `(κ⁺)ˇ` and of `(κ⁺)ˇ ×ˢ (κ⁺)ˇ`, so by Laver's
uniqueness lemma the two hold the same subsets of the ordinal `Θ`. The set of Gödel codes of the
coding relation is such a subset, hence a check, hence the relation itself is a check, and the
collapse of checked data takes checked values. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The parameter: the check of the triple naming `κ⁺`, the ground's subsets of `κ⁺ × κ⁺` and
the ground's subsets of `κ⁺`. -/
noncomputable def levyGroundParameter (κ : V) {G : Set V}
    (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G) :
    (levyContext κ hG).Model :=
  (levyContext κ hG).check
    ⟨hartogsNumber κ, ⟨℘ (hartogsNumber κ ×ˢ hartogsNumber κ), ℘ (hartogsNumber κ)⟩ₖ⟩ₖ

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-! ### The three components of the parameter -/

omit [IsOrdinal κ] in
theorem levyGroundParameter_fst :
    kpair.π₁ (levyGroundParameter κ hG) = (levyContext κ hG).check (hartogsNumber κ) := by
  unfold levyGroundParameter
  rw [(levyContext κ hG).check_kpair, kpair.π₁_kpair]

omit [IsOrdinal κ] in
theorem levyGroundParameter_snd_fst :
    kpair.π₁ (kpair.π₂ (levyGroundParameter κ hG)) =
      (levyContext κ hG).check (℘ (hartogsNumber κ ×ˢ hartogsNumber κ)) := by
  unfold levyGroundParameter
  rw [(levyContext κ hG).check_kpair, kpair.π₂_kpair, (levyContext κ hG).check_kpair,
    kpair.π₁_kpair]

omit [IsOrdinal κ] in
theorem levyGroundParameter_snd_snd :
    kpair.π₂ (kpair.π₂ (levyGroundParameter κ hG)) =
      (levyContext κ hG).check (℘ (hartogsNumber κ)) := by
  unfold levyGroundParameter
  rw [(levyContext κ hG).check_kpair, kpair.π₂_kpair, (levyContext κ hG).check_kpair,
    kpair.π₂_kpair]

/-! ### Recognition: every check is in the ground -/

include hAC hU hc hω hκ in
/-- The check of a ground set satisfies the ground predicate at the Levy parameter. -/
theorem levy_isGround_check (a : V) :
    IsGround ((levyContext κ hG).check a) (levyGroundParameter κ hG) := by
  obtain ⟨β₀, E₀, t₀, hβ₀, hEsub, ht₀, hcol, hval⟩ :=
    (levyContext κ hG).exists_checked_code hAC a
  have : IsOrdinal β₀ := hβ₀
  obtain ⟨p₀, hp₀⟩ := exists_godelPairing β₀
  have hΘ₀ : IsOrdinal (range p₀) := hp₀.2.2.1
  obtain ⟨lam, hlamO, hsucc, hclosed, hmem, hκlam, hHlam, hpow2, hpow1⟩ :=
    exists_levy_good_stage (κ := κ) ({E₀, β₀, p₀, mostowskiMap E₀ β₀, range p₀} : V)
  have : IsOrdinal lam := hlamO
  have hE₀M : E₀ ∈ hierarchy lam := hmem _ (by simp)
  have hp₀M : p₀ ∈ hierarchy lam := hmem _ (by simp)
  have hΘM : range p₀ ∈ hierarchy lam := hmem _ (by simp)
  have hprod : (levyContext κ hG).check (β₀ ×ˢ β₀) =
      (levyContext κ hG).check β₀ ×ˢ (levyContext κ hG).check β₀ :=
    (levyContext κ hG).checkEmbedding.map_prod β₀ β₀
  have hrng : (levyContext κ hG).check (range p₀) = range ((levyContext κ hG).check p₀) :=
    (levyContext κ hG).checkEmbedding.map_range p₀
  refine isGround_of _ _ ((levyContext κ hG).check (range p₀))
    ((levyContext κ hG).check (hierarchy lam)) ((levyContext κ hG).check β₀)
    ((levyContext κ hG).check p₀) ((levyContext κ hG).check E₀)
    (imageSet ((levyContext κ hG).check p₀) ((levyContext κ hG).check E₀))
    ((levyContext κ hG).check β₀) ((levyContext κ hG).check t₀)
    ((levyContext κ hG).check (range (mostowskiMap E₀ β₀)))
    ((levyContext κ hG).check (mostowskiMap E₀ β₀))
    inferInstance ?_ ?_ ?_ inferInstance ?_ ?_ ?_ ?_ ?_ ?_ inferInstance ?_ hcol hval
  · rw [levyGroundParameter_fst]
    exact levy_stage_isGroundLike hAC hU hc hω hκ hG hsucc hclosed hΘM hHlam hκlam
  · rw [levyGroundParameter_fst, levyGroundParameter_snd_fst]
    exact fun X hX ↦ levy_stage_param_prod hG hsucc hpow2 X hX
  · rw [levyGroundParameter_fst, levyGroundParameter_snd_snd]
    exact fun X hX ↦ levy_stage_param_single hG hsucc hpow1 X hX
  · exact ((levyContext κ hG).check_mem_iff p₀ (hierarchy lam)).mpr hp₀M
  · exact (levyContext κ hG).checkEmbedding.isGodelPairing_map hp₀
  · rw [hrng]
  · exact ((levyContext κ hG).check_mem_iff E₀ (hierarchy lam)).mpr hE₀M
  · rw [← hprod]
    exact ((levyContext κ hG).checkEmbedding.subset_iff E₀ (β₀ ×ˢ β₀)).mpr hEsub
  · exact fun z ↦ mem_imageSet_iff_kpair _ _ z
  · exact ((levyContext κ hG).check_mem_iff t₀ β₀).mpr ht₀

/-! ### Uniqueness: everything in the ground is a check -/

include hAC hU hc hω hκ in
/-- A set of the Levy extension that satisfies the ground predicate at the Levy parameter is the
check of a ground set. -/
theorem levy_check_of_isGround {x : (levyContext κ hG).Model}
    (h : IsGround x (levyGroundParameter κ hG)) : ∃ a : V, x = (levyContext κ hG).check a := by
  obtain ⟨Θ, M, Λ, p, E, Sim, β, t, C, f, hΘ, hM, hpar, hpar1, hΛ, hpM, hp, hrange,
    hEM, hE, -, hβ, ht, hcol, hx⟩ := h.exists
  have := hΘ
  have := hΛ
  have := hβ
  rw [levyGroundParameter_fst] at hM hpar hpar1
  rw [levyGroundParameter_snd_fst] at hpar
  rw [levyGroundParameter_snd_snd] at hpar1
  -- the three ordinals and the point are checks
  obtain ⟨θ₀, hθ₀O, rfl⟩ := ForcingContext.ordinal_eq_check (levyContext κ hG) Θ
  obtain ⟨lm₀, hlm₀O, rfl⟩ := ForcingContext.ordinal_eq_check (levyContext κ hG) Λ
  obtain ⟨β₀, hβ₀O, rfl⟩ := ForcingContext.ordinal_eq_check (levyContext κ hG) β
  have : IsOrdinal θ₀ := hθ₀O
  have : IsOrdinal lm₀ := hlm₀O
  have : IsOrdinal β₀ := hβ₀O
  obtain ⟨t₀, ht₀, rfl⟩ := ((levyContext κ hG).mem_check_iff β₀ t).mp ht
  obtain ⟨p₀, hp₀, rfl⟩ := (levyContext κ hG).godelPairing_eq_check hp
  -- a closed stage holding `θ₀` and `lm₀`
  obtain ⟨lam, hlamO, hsucc, hclosed, hmem, hκlam, hHlam, hpow2, hpow1⟩ :=
    exists_levy_good_stage (κ := κ) ({θ₀, lm₀} : V)
  have : IsOrdinal lam := hlamO
  have hθlam : θ₀ ∈ hierarchy lam := hmem _ (by simp)
  have hM'gl : GroundLike ((levyContext κ hG).check (hierarchy lam))
      ((levyContext κ hG).check (hartogsNumber κ)) ((levyContext κ hG).check θ₀) :=
    levy_stage_groundLike hAC hU hc hω hκ hG hsucc hclosed hθlam hHlam hκlam
  have hMgl : GroundLike M ((levyContext κ hG).check (hartogsNumber κ))
      ((levyContext κ hG).check θ₀) := (isGroundLike_iff _ _ _).mp hM
  -- `M` and the checked stage agree on the two parameter families
  have hagree : ∀ X : (levyContext κ hG).Model,
      X ⊆ (levyContext κ hG).check (hartogsNumber κ) ×ˢ
        (levyContext κ hG).check (hartogsNumber κ) →
      (X ∈ M ↔ X ∈ (levyContext κ hG).check (hierarchy lam)) :=
    fun X hX ↦ (hpar X hX).trans (levy_stage_param_prod hG hsucc hpow2 X hX).symm
  have hagree1 : ∀ X : (levyContext κ hG).Model,
      X ⊆ (levyContext κ hG).check (hartogsNumber κ) →
      (X ∈ M ↔ X ∈ (levyContext κ hG).check (hierarchy lam)) :=
    fun X hX ↦ (hpar1 X hX).trans (levy_stage_param_single hG hsucc hpow1 X hX).symm
  have huniq := ground_uniqueness (levy_model_internalChoice hAC hG)
    (levy_check_hartogs_regular hAC hU hc hω hκ hG) (levy_omega_mem_check_hartogs hω hG)
    hMgl hM'gl hagree hagree1
  -- the set of Gödel codes of the coding relation
  have hAM : imageSet ((levyContext κ hG).check p₀) E ∈ M :=
    hM.2.2.2.2.2.1 _ hpM E hEM _ (mem_imageSet_iff_kpair _ _)
  have hAΘ : imageSet ((levyContext κ hG).check p₀) E ⊆ (levyContext κ hG).check θ₀ := by
    intro z hz
    obtain ⟨q, -, hqz⟩ := (mem_imageSet_iff_kpair _ _ z).mp hz
    exact hrange z (mem_range_of_kpair_mem hqz)
  obtain ⟨A₀, -, hAeq⟩ :=
    ((levyContext κ hG).mem_check_iff (hierarchy lam) _).mp ((huniq _ hAΘ).mp hAM)
  -- so the coding relation is the pairing preimage of a checked set
  have hpfun : IsFunction ((levyContext κ hG).check p₀) := hp.1
  have hEchar : ∀ q : (levyContext κ hG).Model, q ∈ E ↔
      (q ∈ (levyContext κ hG).check lm₀ ×ˢ (levyContext κ hG).check lm₀ ∧
        ((levyContext κ hG).check p₀) ‘ q ∈ (levyContext κ hG).check A₀) := by
    intro q
    constructor
    · intro hq
      refine ⟨hE q hq, ?_⟩
      have hqdom : q ∈ domain ((levyContext κ hG).check p₀) := by rw [hp.2.1]; exact hE q hq
      have hmemA : ((levyContext κ hG).check p₀) ‘ q ∈
          imageSet ((levyContext κ hG).check p₀) E :=
        (mem_imageSet_iff_kpair _ _ _).mpr ⟨q, hq, kpair_value_mem hqdom⟩
      rwa [hAeq] at hmemA
    · rintro ⟨hqprod, hqA⟩
      have hmemA : ((levyContext κ hG).check p₀) ‘ q ∈
          imageSet ((levyContext κ hG).check p₀) E := by rw [hAeq]; exact hqA
      obtain ⟨q', hq'E, hq'p⟩ := (mem_imageSet_iff_kpair _ _ _).mp hmemA
      have hqdom : q ∈ domain ((levyContext κ hG).check p₀) := by rw [hp.2.1]; exact hqprod
      have hqq' : q' = q :=
        godelPairing_injective hp q' q _ hq'p (kpair_value_mem hqdom)
      exact hqq' ▸ hq'E
  have hEeq := (levyContext κ hG).check_of_pairingPreimage hp₀ hEchar
  rw [hEeq] at hcol
  obtain ⟨a, ha⟩ := (levyContext κ hG).check_of_collapse hcol ht
  exact ⟨a, hx.trans ha⟩

/-! ### The theorem -/

include hAC hU hc hω hκ in
/-- Laver's theorem for the Levy collapse: the ground predicate at the Levy parameter holds of
exactly the checks. -/
theorem levy_isGround_iff (x : (levyContext κ hG).Model) :
    IsGround x (levyGroundParameter κ hG) ↔ ∃ a : V, x = (levyContext κ hG).check a := by
  constructor
  · exact levy_check_of_isGround hAC hU hc hω hκ hG
  · rintro ⟨a, rfl⟩
    exact levy_isGround_check hAC hU hc hω hκ hG a

include hAC hU hc hω hκ in
/-- The ground model is a definable class of the Levy extension from one parameter. -/
theorem levy_ground_definable :
    ∃ (φ : SetTheorySemisentence 2) (r : (levyContext κ hG).Model),
      ∀ x : (levyContext κ hG).Model,
        φ.Evalb ![x, r] ↔ ∃ a : V, x = (levyContext κ hG).check a := by
  refine ⟨groundFormula, levyGroundParameter κ hG, fun x ↦ ?_⟩
  rw [eval_groundFormula]
  exact levy_isGround_iff hAC hU hc hω hκ hG x

end

end ZFVP
