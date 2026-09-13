import ZFVP.SetTheory.SameLevelForcing
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

/-- One finite forcing formula works in every ZF membership structure in the
specified ambient universe. Its syntax is chosen before the structure. -/
def IsUniformForcingTranslation (symmetric : Bool) {n : ℕ}
    (φ : SetTheorySemisentence n) (θ : SetTheorySemisentence (n + 5)) : Prop :=
  ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
    IsForcingTranslation (V := V) symmetric φ θ

theorem IsBoundedSetFormula.forcing_translation_uniform {n k : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (symmetric : Bool) (pol : LevyPolarity) (hk : 0 < k) :
    ∃ θ : SetTheorySemisentence (n + 5), IsLevyFormula pol k θ ∧
      IsUniformForcingTranslation.{u} symmetric φ θ := by
  obtain ⟨t, rfl⟩ := boundedFormulaTree_exists hφ
  refine ⟨t.levyForcingBase pol, t.levyForcingBase_levy pol hk, ?_⟩
  intro V _ _ _
  exact t.levyForcingBase_translation symmetric pol

theorem IsLevyFormula.forcing_translation_uniform {n k : ℕ} {pol : LevyPolarity}
    {φ : SetTheorySemisentence n} (hφ : IsLevyFormula pol k φ) (symmetric : Bool) (hk : 0 < k) :
    ∃ θ : SetTheorySemisentence (n + 5), IsLevyFormula pol k θ ∧
      IsUniformForcingTranslation.{u} symmetric φ θ := by
  induction hφ with
  | bounded hφ => exact hφ.forcing_translation_uniform symmetric _ hk
  | @raise p q k n φ hφ ih =>
    cases k with
    | zero => exact (hφ.zero_bounded rfl).forcing_translation_uniform symmetric q hk
    | succ k =>
      obtain ⟨θ, hθ, he⟩ := ih (by omega)
      exact ⟨θ, .raise hθ, he⟩
  | and hφ hψ ihφ ihψ =>
    obtain ⟨θ, hθ, heθ⟩ := ihφ hk
    obtain ⟨η, hη, heη⟩ := ihψ hk
    refine ⟨θ.and η, .and hθ hη, ?_⟩
    intro V _ _ _
    exact (heθ V).and (heη V)
  | or hφ hψ ihφ ihψ =>
    obtain ⟨θ, hθ, heθ⟩ := ihφ hk
    obtain ⟨η, hη, heη⟩ := ihψ hk
    refine ⟨levyForcingOrStep θ η, levyForcingOrStep_levy hθ hη, ?_⟩
    intro V _ _ _
    exact (heθ V).or (heη V)
  | boundedAll t hφ ih =>
    obtain ⟨θ, hθ, heθ⟩ := ih hk
    refine ⟨forcingTransitiveBind _ (levyForcingBoundedAllBody t θ),
      forcingTransitiveBind_levy hk (levyForcingBoundedAllBody_levy t hθ), ?_⟩
    intro V _ _ _
    exact (heθ V).boundedAll t _
  | boundedExs t hφ ih =>
    obtain ⟨θ, hθ, heθ⟩ := ih hk
    refine ⟨forcingTransitiveBind _ (levyForcingBoundedExsBody t θ),
      forcingTransitiveBind_levy hk (levyForcingBoundedExsBody_levy t hθ), ?_⟩
    intro V _ _ _
    exact (heθ V).boundedExs t _
  | exs hφ ih =>
    obtain ⟨θ, hθ, heθ⟩ := ih hk
    refine ⟨levyForcingExsStep symmetric θ, levyForcingExsStep_sigma symmetric hθ, ?_⟩
    intro V _ _ _
    exact (heθ V).exs
  | all hφ ih =>
    obtain ⟨θ, hθ, heθ⟩ := ih hk
    refine ⟨levyForcingAllStep symmetric θ, levyForcingAllStep_pi symmetric hθ, ?_⟩
    intro V _ _ _
    exact (heθ V).all

theorem IsLevyFormula.ordinaryForcing_definition_uniform {n k : ℕ} {pol : LevyPolarity}
    {φ : SetTheorySemisentence n} (hφ : IsLevyFormula pol k φ) (hk : 0 < k) :
    ∃ θ : SetTheorySemisentence (n + 3), IsLevyFormula pol k θ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ P R : V, IsForcingPreorder P R → ∀ v : Fin n → V,
          (∀ i, IsForcingName P (v i)) → ∀ p,
            θ.Evalb (P :> R :> p :> v) ↔ p ∈ forcingFormula P R φ (standardTuple v) := by
  obtain ⟨θ, hθ, he⟩ := IsLevyFormula.forcing_translation_uniform.{u} hφ false hk
  refine ⟨ordinaryForcingSpecialization pol θ, ordinaryForcingSpecialization_levy hk hθ, ?_⟩
  intro V _ _ _ P R hR v hv p
  exact ordinaryForcingSpecialization_meaning (he V) pol hR v hv p
end ZFVP
