import ZFVP.ModelTheory.SolovayHODBridge
import ZFVP.ModelTheory.SolovayOmegaOne
import ZFVP.SetTheory.HODOmegaOne

/-! `κ` is the first uncountable ordinal of the HOD class model built inside the Levy extension
(lem:Solovay-regularity, clause `κ = ω₁^{Sol}`).

The ground sets of the extension all lie in the class model `HODDom Pf p`, every ordinal below `κ`
is countable there, and `κ̌` is not. Hence the Hartogs number of `ω` computed inside the class model
is `κ̌`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Ordinalhood transfers from `V` to the HOD class model: `IsOrdinal` is bounded, so it is
absolute along the inclusion. This is the converse of `hod_isOrdinal_val`. -/
theorem hod_isOrdinal_of_val (Pf : SetTheorySemisentence 2) (p : V)
    [Nonempty (HODDom Pf p)] [(HODDom Pf p)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (x : HODDom Pf p) (hx : IsOrdinal x.val) : IsOrdinal x := by
  have h := (hodInclusion Pf p).bounded_defined isOrdinalFormula_bounded
    (fun v ↦ IsOrdinal (v 0)) (fun v ↦ IsOrdinal (v 0)) ![x]
  simp only [Matrix.cons_val_zero] at h
  exact h.mpr hx

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
  (Pf : SetTheorySemisentence 2) {p : (levyContext κ hG).Model}
  (hPf_check : ∀ a : V, Pf.Evalb ![(levyContext κ hG).check a, p])
  (hPf_real : ∀ c : (levyContext κ hG).Model,
    c ⊆ (levyContext κ hG).check (ω : V) → Pf.Evalb ![c, p])
  [Nonempty (HODDom Pf p)] [(HODDom Pf p)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

include hPf_check hPf_real in
/-- Every ground set is hereditarily ordinal definable in the Levy extension from the parameter
class given by `Pf`, so it belongs to the class model. -/
theorem hod_check_isHOD (a : V) : IsHOD Pf ((levyContext κ hG).check a) p :=
  ForcingContext.isHOD_of_hereditarilyGroundRealDefinable (levyContext κ hG) Pf hPf_check hPf_real
    (ForcingContext.hereditarily_check a)

/-- Every ordinal below `κ` is countable in the class model: the collapsing injection of the
extension is itself in the class model. -/
theorem hod_check_countable {β : V} (hβ : β ∈ κ) :
    IsInternallyCountable
      (toHOD Pf p (hod_check_isHOD hG Pf hPf_check hPf_real β) : HODDom Pf p) := by
  obtain ⟨e, he, heinj⟩ := levy_solovay_countable hG hβ
  have hE : IsHOD Pf e.val p :=
    ForcingContext.isHOD_of_hereditarilyGroundRealDefinable (levyContext κ hG) Pf hPf_check
      hPf_real e.property
  refine ⟨toHOD Pf p hE, ?_, ?_⟩
  · rw [mem_function_val Pf p, val_omega Pf p]
    exact he
  · rw [← injective_val Pf p]
    exact heinj

include hAC hU hc hω hκ in
/-- `κ̌` is uncountable in the class model, because it is uncountable in the whole extension. -/
theorem hod_check_kappa_not_countable :
    ¬ IsInternallyCountable
      (toHOD Pf p (hod_check_isHOD hG Pf hPf_check hPf_real κ) : HODDom Pf p) := by
  intro h
  have h2 := hod_cardLE_omega_of_val Pf p h
  exact ((hartogsNumber_eq_iff _ _).mp (levy_check_hartogs hAC hU hc hω hκ hG)).2.1 h2

include hAC hU hc hω hκ in
/-- `κ̌` is the first uncountable ordinal of the class model. -/
theorem hod_hartogsNumber_omega_eq_check_kappa :
    hartogsNumber (ω : HODDom Pf p) =
      toHOD Pf p (hod_check_isHOD hG Pf hPf_check hPf_real κ) := by
  have hKord : IsOrdinal (toHOD Pf p (hod_check_isHOD hG Pf hPf_check hPf_real κ) : HODDom Pf p) :=
    hod_isOrdinal_of_val Pf p _ (((levyContext κ hG).check_ordinal_iff κ).mpr inferInstance)
  refine hod_hartogs_eq Pf p _ ?_
    (hod_check_kappa_not_countable hAC hU hc hω hκ hG Pf hPf_check hPf_real)
  intro a ha
  obtain ⟨β, hβ, hβv⟩ :=
    ((levyContext κ hG).mem_check_iff κ a.val).mp ((mem_val_iff Pf p a _).mpr ha)
  have hae : a = toHOD Pf p (hod_check_isHOD hG Pf hPf_check hPf_real β) := Subtype.ext hβv
  rw [hae]
  exact hod_check_countable hG Pf hPf_check hPf_real hβ

end

end ZFVP
