import ZFVP.ModelTheory.LevyCollapseReals
import ZFVP.ModelTheory.LevyCollapseLocalization
import ZFVP.ModelTheory.GroundRealsHOD
import ZFVP.ModelTheory.ForcingModelRank

/-! Lemma Solovay-localization (first clause): every set of ordinals of the extension that is
definable from ground sets, reals and ordinals lies in some bounded-stage extension `V[G_ξ]`,
`ξ < κ`. The parameters are localized one by one and the definable set is named over the
subcollapse by the localized name. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ : V} [IsOrdinal κ] {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- The bounded-stage extensions grow with the stage. -/
theorem inLevySubmodel_mono {β β' : V} [IsOrdinal β] [IsOrdinal β'] (hβ : β ⊆ κ) (hβ' : β' ⊆ κ)
    (h : β ⊆ β') {x : (levyContext κ hG).Model} (hx : InLevySubmodel β hβ hG x) :
    InLevySubmodel β' hβ' hG x := by
  obtain ⟨τ, rfl⟩ := (inLevySubmodel_iff β hβ hG x).mp hx
  exact (inLevySubmodel_iff β' hβ' hG _).mpr ⟨⟨τ.val, τ.property.mono (levyCollapse_mono h)⟩, rfl⟩

/-- `x` lies in some bounded-stage extension `V[G_ξ]` with `ξ < κ`. -/
def IsLocalized (x : (levyContext κ hG).Model) : Prop :=
  ∃ ξ : V, ∃ hξ : ξ ∈ κ,
    haveI : IsOrdinal ξ := IsOrdinal.of_mem hξ
    InLevySubmodel ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG x

theorem exists_stage_ge {ξ₁ ξ₂ : V} (h₁ : ξ₁ ∈ κ) (h₂ : ξ₂ ∈ κ) :
    ∃ ξ ∈ κ, ξ₁ ⊆ ξ ∧ ξ₂ ⊆ ξ := by
  haveI := IsOrdinal.of_mem h₁
  haveI := IsOrdinal.of_mem h₂
  rcases IsOrdinal.subset_or_supset (α := ξ₁) (β := ξ₂) with h | h
  · exact ⟨ξ₂, h₂, h, fun x hx ↦ hx⟩
  · exact ⟨ξ₁, h₁, fun x hx ↦ hx, h⟩

theorem isLocalized_check (hω : (ω : V) ∈ κ) (a : V) : IsLocalized hG ((levyContext κ hG).check a) :=
  ⟨∅, IsOrdinal.toIsTransitive.mem_trans empty_mem_ω hω, inLevySubmodel_check _ _ hG a⟩

/-- Finitely many localized elements are localized at a common stage. -/
theorem isLocalized_tuple (hω : (ω : V) ∈ κ) {n : ℕ} (v : Fin n → (levyContext κ hG).Model)
    (hv : ∀ i, IsLocalized hG (v i)) :
    ∃ ξ : V, ∃ hξ : ξ ∈ κ,
      haveI : IsOrdinal ξ := IsOrdinal.of_mem hξ
      ∀ i, InLevySubmodel ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG (v i) := by
  induction n with
  | zero => exact ⟨∅, IsOrdinal.toIsTransitive.mem_trans empty_mem_ω hω, fun i ↦ i.elim0⟩
  | succ n ih =>
    obtain ⟨ξ₀, hξ₀, h₀⟩ := ih (fun i ↦ v i.succ) (fun i ↦ hv i.succ)
    obtain ⟨ξ₁, hξ₁, h₁⟩ := hv 0
    obtain ⟨ξ, hξ, hs₀, hs₁⟩ := exists_stage_ge hξ₀ hξ₁
    haveI := IsOrdinal.of_mem hξ₀
    haveI := IsOrdinal.of_mem hξ₁
    haveI := IsOrdinal.of_mem hξ
    refine ⟨ξ, hξ, fun i ↦ ?_⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact inLevySubmodel_mono hG _ _ hs₁ h₁
    · exact inLevySubmodel_mono hG _ _ hs₀ (h₀ j)

end

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- Every allowed parameter (ground set, real, ordinal) is localized. -/
theorem isLocalized_parameter {x : (levyContext κ hG).Model}
    (hx : (levyContext κ hG).IsSolovayParameter x) : IsLocalized hG x := by
  rcases hx with ⟨a, rfl⟩ | hx | hx
  · exact isLocalized_check hG hω a
  · exact levy_real_localized hAC hU hc hω hκ hG x hx
  · haveI := hx
    obtain ⟨β, _, rfl⟩ := (levyContext κ hG).ordinal_eq_check x
    exact isLocalized_check hG hω β

include hAC hU hc hω hκ in
/-- Lemma Solovay-localization, first clause: a set of ordinals of `V[G]` definable from ground
sets, reals and ordinals lies in some `V[G_ξ]`, `ξ < κ`. -/
theorem groundRealDefinable_localized {x : (levyContext κ hG).Model}
    (hx : (levyContext κ hG).IsGroundRealDefinable x) {θ : V}
    (hxθ : x ⊆ (levyContext κ hG).check θ) : IsLocalized hG x := by
  obtain ⟨n, φ, v, hv, hdef⟩ := hx
  obtain ⟨ξ, hξ, hall⟩ := isLocalized_tuple hG hω v (fun i ↦ isLocalized_parameter hAC hU hc hω hκ hG (hv i))
  haveI : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hξsub : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξ
  have hnames : ∀ i, ∃ τ : ForcingName (levySubContext ξ hξsub hG).P,
      v i = (levyContext κ hG).ofName ⟨τ.val, τ.property.mono (levyCollapse_mono hξsub)⟩ :=
    fun i ↦ (inLevySubmodel_iff ξ hξsub hG (v i)).mp (hall i)
  choose τ hτ using hnames
  have hveq : (fun i ↦ (levyContext κ hG).ofName
      ⟨(τ i).val, (τ i).property.mono (levyCollapse_mono hξsub)⟩) = v :=
    funext (fun i ↦ (hτ i).symm)
  refine ⟨ξ, hξ, ?_⟩
  have hx_eq : x = (levyContext κ hG).ofName ⟨localizedName κ ξ θ φ (fun i ↦ (τ i).val),
      (localizedName_isName κ ξ θ φ _).mono (levyCollapse_mono hξsub)⟩ := by
    apply mem_ext
    intro b
    rw [mem_ofName_localizedName_iff ξ hξsub hG θ φ τ b, hveq]
    constructor
    · intro hb
      obtain ⟨α, hα, rfl⟩ := ((levyContext κ hG).mem_check_iff θ b).mp (hxθ b hb)
      exact ⟨α, hα, rfl, (hdef _).mp hb⟩
    · rintro ⟨α, hα, rfl, hφ⟩
      exact (hdef _).mpr hφ
  rw [hx_eq]
  exact inLevySubmodel_localized ξ hξsub hG θ φ τ

end

end ZFVP
