import ZFVP.ModelTheory.SolovayHODOmegaOne
import ZFVP.ModelTheory.LevyRealsInjection
import ZFVP.ModelTheory.LevyODParameterTree

/-! Choice fails in the HOD class model `HOD_{V ∪ R}^{V[G]}` built inside the Levy collapse
extension (lem:Solovay-choice-failure).

If the Cantor space of the class model injected into an ordinal of the class model, then the
Cantor space of the class model would be well orderable there, so the first uncountable ordinal
of the class model would inject into it. That first uncountable ordinal is `κ̌`, and the injection
lies in the class model, hence is ordinal definable in the extension, hence is definable from
ground sets, reals and ordinals by `hconv`. No such injection of `κ̌` into the reals exists
(`no_groundRealDefinable_injection`).

Choice in the class model gives such an injection into an ordinal, so the class model does not
satisfy Choice. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- `b ∈ D` and `b` is a pair whose second component lies in the value of `g` at its first
component: the membership condition of `realsCode D g`. -/
def realsCodeFormula : SetTheorySemisentence 3 :=
  f“b D g. b ∈ D ∧ !kpair.π₂.dfn b ∈ !value.dfn g (!kpair.π₁.dfn b)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_realsCodeFormula (v : Fin 3 → V) :
    realsCodeFormula.Evalb v ↔ v 0 ∈ v 1 ∧ kpair.π₂ (v 0) ∈ (v 2) ‘ (kpair.π₁ (v 0)) := by
  simp [realsCodeFormula]

/-- The Cantor space of a model of `ZF` that is well orderable there has the Hartogs number of `ω`
injected into it. This is `hartogs_omega_cardLE_cantorSpace` with Choice weakened to well
orderability of the Cantor space alone. -/
theorem hartogs_omega_cardLE_cantorSpace_of_wellOrderable
    (hwo : IsWellOrderable (cantorSpace V)) : hartogsNumber (ω : V) ≤# cantorSpace V := by
  have heq : wellOrderedCardinal (cantorSpace V) ≋ cantorSpace V := wellOrderedCardinal_cardEQ hwo
  have hord : IsOrdinal (wellOrderedCardinal (cantorSpace V)) := (wellOrderedCardinal_initial hwo).1
  have hnot : ¬wellOrderedCardinal (cantorSpace V) ≤# (ω : V) := fun h ↦
    cantorSpace_not_countable (heq.2.trans h)
  exact (cardLE_of_subset (hartogsNumber_minimal hnot)).trans heq.1

namespace ForcingContext

variable {A : ForcingContext V}

/-- The code of a function into the reals is definable from ground sets, reals and ordinals as
soon as the function is: the code is defined from the function and a checked set. -/
theorem groundRealDefinable_realsCode (a : V) {f : A.Model}
    (hf : A.IsGroundRealDefinable f) :
    A.IsGroundRealDefinable (realsCode (A.check a) f) := by
  refine groundRealDefinable_of_definable_from_definables ![A.check a, f] ?_ realsCodeFormula ?_
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact groundRealDefinable_of_parameter (Or.inl ⟨a, rfl⟩)
    · rw [Fin.fin_one_eq_zero j]
      exact hf
  · intro b
    rw [mem_realsCode_iff, eval_realsCodeFormula]
    simp

end ForcingContext

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
  (hconv : ∀ x : (levyContext κ hG).Model, IsOD Pf x p →
    (levyContext κ hG).IsGroundRealDefinable x)

include hAC hU hc hω hκ hPf_check hPf_real hconv in
/-- The Cantor space of the class model is not well orderable there: a well ordering would produce
an injection of `κ̌`, the first uncountable ordinal of the class model, into the reals of the
extension, and that injection would be definable from ground sets, reals and ordinals. -/
theorem hod_cantorSpace_not_wellOrderable :
    ¬ IsWellOrderable (cantorSpace (HODDom Pf p)) := by
  intro hwo
  obtain ⟨g, hg, hginj⟩ := hartogs_omega_cardLE_cantorSpace_of_wellOrderable hwo
  rw [hod_hartogsNumber_omega_eq_check_kappa hAC hU hc hω hκ hG Pf hPf_check hPf_real] at hg
  -- the injection, read in the extension
  have hsub : (cantorSpace (HODDom Pf p)).val ⊆ cantorSpace (levyContext κ hG).Model := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := exists_val_of_mem Pf p hy
    exact (mem_cantorSpace_val Pf p z).mp hz
  have hgv := (mem_function_val Pf p g _ (cantorSpace (HODDom Pf p))).mp hg
  have hg2 := mem_function_of_mem_function_of_subset hgv hsub
  have hginj2 : Injective g.val := (injective_val Pf p g).mpr hginj
  -- it lies in the class model, hence is definable from ground sets, reals and ordinals
  have hdef : (levyContext κ hG).IsGroundRealDefinable g.val :=
    hconv g.val (IsHOD.od Pf (hod_val_isHOD Pf p g))
  exact no_groundRealDefinable_injection hAC hU hc hω hκ hG hg2 hginj2
    (ForcingContext.groundRealDefinable_realsCode _ hdef)

include hAC hU hc hω hκ hPf_check hPf_real hconv in
/-- No injection of the Cantor space of the class model into an ordinal of the class model. -/
theorem hod_no_injection_cantorSpace_ordinal {β f : HODDom Pf p} [IsOrdinal β]
    (hf : f ∈ β ^ cantorSpace (HODDom Pf p)) : ¬ Injective f := by
  intro hinj
  exact hod_cantorSpace_not_wellOrderable hAC hU hc hω hκ hG Pf hPf_check hPf_real hconv
    ((wellOrderable_iff_cardLE_ordinal _).mpr ⟨β, inferInstance, f, hf, hinj⟩)

include hAC hU hc hω hκ hPf_check hPf_real hconv in
/-- Choice fails in the class model. -/
theorem hod_not_internalChoice : ¬ InternalChoice (HODDom Pf p) := by
  intro hch
  exact hod_cantorSpace_not_wellOrderable hAC hU hc hω hκ hG Pf hPf_check hPf_real hconv
    (wellOrderable_of_internalChoice hch _)

end

end ZFVP
