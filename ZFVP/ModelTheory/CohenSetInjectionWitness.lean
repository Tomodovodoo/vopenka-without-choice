import ZFVP.ModelTheory.CohenSetInjection
import ZFVP.SetTheory.HODOmegaOne
import ZFVP.SetTheory.AbsorptionInfinite

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)

/-- The subset-bijection form of the Cohen injection theorem, with Cantor-space real codes
and the finite-sequence coordinate first. -/
theorem set_injection_finiteSequences_cantor_ordinal (hAC : InternalChoice V)
    (x : (cohenContext (ω : V) G hG).Model) :
    ∃ γ A f : (cohenContext (ω : V) G hG).Model,
      IsOrdinal γ ∧
        A ⊆ finiteSequences (cantorSpace (cohenContext (ω : V) G hG).Model) ×ˢ γ ∧
        f ∈ A ^ x ∧ Injective f ∧ range f = A := by
  let S := cohenContext (ω : V) G hG
  obtain ⟨γ, hγ, hx⟩ := set_injection_ordinal_finiteSequences hG hAC x
  have hReals : reals hG ≤# cantorSpace S.Model :=
    (cardLE_of_subset (reals_subset_power_omega hG)).trans power_omega_cardLE_cantorSpace
  have hseq := finiteSequences_cardLE_of_cardLE hReals
  have hx' : x ≤# finiteSequences (cantorSpace S.Model) ×ˢ γ :=
    (hx.trans (prod_comm_cardLE _ _)).trans (prod_cardLE_prod hseq (CardLE.refl γ))
  obtain ⟨f, hf, hfi⟩ := hx'
  have : IsFunction f := IsFunction.of_mem hf
  refine ⟨γ, range f, f, hγ, range_subset_of_mem_function hf, ?_, hfi, rfl⟩
  simpa only [domain_eq_of_mem_function hf] using IsFunction.mem_function f

end CohenModel

/-- The subset-bijection interface used by the positive rigid-relation application. -/
def CohenSetInjectionInput : Prop :=
  ∀ (V : Type) (_ : SetStructure V) (_ : Nonempty V) (hZF : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙) (_ : Countable V),
    letI := hZF
    InternalChoice V →
    ∀ (G : Set V)
      (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)
      (x : (cohenContext (ω : V) G hG).Model),
      ∃ γ A f : (cohenContext (ω : V) G hG).Model,
        IsOrdinal γ ∧
          A ⊆ finiteSequences (cantorSpace (cohenContext (ω : V) G hG).Model) ×ˢ γ ∧
          f ∈ A ^ x ∧ Injective f ∧ range f = A

/-- The Cohen injection input is a theorem, discharged by the constructed internal graph. -/
theorem cohenSetInjectionInput : CohenSetInjectionInput := by
  intro V hstr hne hZF _
  let := hZF
  intro hAC G hG x
  exact CohenModel.set_injection_finiteSequences_cantor_ordinal hG hAC x

end ZFVP
