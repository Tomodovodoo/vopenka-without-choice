import ZFVP.Syntax.LevyForcingStepSemantics

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsForcingTranslation (symmetric : Bool) {n : ℕ} (φ : SetTheorySemisentence n)
    (θ : SetTheorySemisentence (n + 5)) : Prop :=
  ∀ (P R Γ F : V), IsForcingPreorder P R → (∀ π ∈ Γ, π ∈ P ^ P) →
    ∀ (v : Fin n → V), (∀ i, forcingNameClass symmetric P Γ F (v i)) → ∀ p,
      θ.Evalb (P :> R :> Γ :> F :> p :> v) ↔
        p ∈ classForcingFormula P R (forcingNameClass symmetric P Γ F) (by definability) φ (standardTuple v)

theorem BoundedFormulaTree.levyForcingBase_translation {n : ℕ} (φ : BoundedFormulaTree n)
    (symmetric : Bool) (pol : LevyPolarity) : IsForcingTranslation (V := V) symmetric φ.formula (φ.levyForcingBase pol) := by
  intro P R Γ F hR _ v hv p
  exact φ.levyForcingBase_meaning hR symmetric Γ F pol v hv p

theorem IsForcingTranslation.and {symmetric : Bool} {n : ℕ} {φ ψ : SetTheorySemisentence n}
    {θ η : SetTheorySemisentence (n + 5)} (hφ : IsForcingTranslation (V := V) symmetric φ θ)
    (hψ : IsForcingTranslation (V := V) symmetric ψ η) :
    IsForcingTranslation (V := V) symmetric (φ.and ψ) (θ.and η) := by
  intro P R Γ F hR hΓ v hv p
  change (θ.Evalb _ ∧ η.Evalb _) ↔ _
  rw [hφ P R Γ F hR hΓ v hv p, hψ P R Γ F hR hΓ v hv p, classForcingFormula_and, mem_inter_iff]

theorem IsForcingTranslation.or {symmetric : Bool} {n : ℕ} {φ ψ : SetTheorySemisentence n}
    {θ η : SetTheorySemisentence (n + 5)} (hφ : IsForcingTranslation (V := V) symmetric φ θ)
    (hψ : IsForcingTranslation (V := V) symmetric ψ η) :
    IsForcingTranslation (V := V) symmetric (φ.or ψ) (levyForcingOrStep θ η) := by
  intro P R Γ F hR hΓ v hv p
  let N := forcingNameClass symmetric P Γ F
  have hN : ℒₛₑₜ-predicate N := by definability
  have hφP := (classForcingFormula_regular N hN hR φ (standardTuple v)).1
  have hψP := (classForcingFormula_regular N hN hR ψ (standardTuple v)).1
  rw [eval_levyForcingOrStep, classForcingFormula_or, mem_forcingClosure_iff]
  simp only [hφ P R Γ F hR hΓ v hv, hψ P R Γ F hR hΓ v hv, mem_union_iff]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro q
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  constructor
  · rintro ⟨r, _, hrq, hr⟩
    exact ⟨r, hr, hrq⟩
  · rintro ⟨r, hr, hrq⟩
    exact ⟨r, hr.elim (hφP r) (hψP r), hrq, hr⟩

theorem IsForcingTranslation.all {symmetric : Bool} {n : ℕ} {φ : SetTheorySemisentence (n + 1)}
    {θ : SetTheorySemisentence (n + 1 + 5)} (hφ : IsForcingTranslation (V := V) symmetric φ θ) :
    IsForcingTranslation (V := V) symmetric φ.all (levyForcingAllStep symmetric θ) := by
  intro P R Γ F hR hΓ v hv p
  rw [eval_levyForcingAllStep hΓ, classForcingFormula_all, mem_forcingClassIntersection_iff]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro u
  apply imp_congr_right
  intro hu
  exact hφ P R Γ F hR hΓ (u :> v) (fun i ↦ Fin.cases hu hv i) p

theorem IsForcingTranslation.exs {symmetric : Bool} {n : ℕ} {φ : SetTheorySemisentence (n + 1)}
    {θ : SetTheorySemisentence (n + 1 + 5)} (hφ : IsForcingTranslation (V := V) symmetric φ θ) :
    IsForcingTranslation (V := V) symmetric φ.exs (levyForcingExsStep symmetric θ) := by
  intro P R Γ F hR hΓ v hv p
  rw [eval_levyForcingExsStep hΓ, classForcingFormula_exs_dense_iff]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro q
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  apply exists_congr
  intro r
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply exists_congr
  intro u
  apply and_congr_right
  intro hu
  exact hφ P R Γ F hR hΓ (u :> v) (fun i ↦ Fin.cases hu hv i) r

theorem IsForcingTranslation.boundedAll {symmetric : Bool} {n : ℕ} (t : SetTheorySemiterm Empty n)
    {φ : SetTheorySemisentence (n + 1)} {θ : SetTheorySemisentence (n + 1 + 5)}
    (hφ : IsForcingTranslation (V := V) symmetric φ θ) (pol : LevyPolarity) :
    IsForcingTranslation (V := V) symmetric (boundedSetAll t φ)
      (forcingTransitiveBind pol (levyForcingBoundedAllBody t θ)) := by
  intro P R Γ F hR hΓ v hv p
  apply eval_forcingTransitiveBind
  intro T hT hvT
  let := hT
  have htN := forcingTermValue_standard_property t v (forcingNameClass symmetric P Γ F) hv
  have htT := forcingTermValue_standard_property t v (fun x ↦ x ∈ T) hvT
  have hs : ∀ u s, ⟨u, s⟩ₖ ∈ forcingTermValue t (standardTuple v) → forcingNameClass symmetric P Γ F u :=
    fun _ _ hus ↦ forcingNameClass_subname htN hus
  rw [eval_levyForcingBoundedAllBody, ← forcingTermValue_standard,
    classForcingFormula_boundedAll_iff hR _ _ t φ v (forcingNameClass_isName htN) hs]
  apply and_congr Iff.rfl
  apply bounded_pair_forall_congr htT
  intro u s hus
  simp only [hφ P R Γ F hR hΓ (u :> v) (fun i ↦ Fin.cases (hs u s hus) hv i)]

theorem IsForcingTranslation.boundedExs {symmetric : Bool} {n : ℕ} (t : SetTheorySemiterm Empty n)
    {φ : SetTheorySemisentence (n + 1)} {θ : SetTheorySemisentence (n + 1 + 5)}
    (hφ : IsForcingTranslation (V := V) symmetric φ θ) (pol : LevyPolarity) :
    IsForcingTranslation (V := V) symmetric (boundedSetExs t φ)
      (forcingTransitiveBind pol (levyForcingBoundedExsBody t θ)) := by
  intro P R Γ F hR hΓ v hv p
  apply eval_forcingTransitiveBind
  intro T hT hvT
  let := hT
  have htN := forcingTermValue_standard_property t v (forcingNameClass symmetric P Γ F) hv
  have htT := forcingTermValue_standard_property t v (fun x ↦ x ∈ T) hvT
  have hs : ∀ u s, ⟨u, s⟩ₖ ∈ forcingTermValue t (standardTuple v) → forcingNameClass symmetric P Γ F u :=
    fun _ _ hus ↦ forcingNameClass_subname htN hus
  rw [eval_levyForcingBoundedExsBody, ← forcingTermValue_standard,
    classForcingFormula_boundedExs_iff hR _ _ t φ v (forcingNameClass_isName htN) hs]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro q
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  apply exists_congr
  intro r
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply bounded_pair_exists_congr htT
  intro u s hus
  simp only [hφ P R Γ F hR hΓ (u :> v) (fun i ↦ Fin.cases (hs u s hus) hv i)]

theorem IsBoundedSetFormula.forcing_translation {n k : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (symmetric : Bool) (pol : LevyPolarity) (hk : 0 < k) :
    ∃ θ : SetTheorySemisentence (n + 5), IsLevyFormula pol k θ ∧ IsForcingTranslation (V := V) symmetric φ θ := by
  obtain ⟨t, rfl⟩ := boundedFormulaTree_exists hφ
  exact ⟨t.levyForcingBase pol, t.levyForcingBase_levy pol hk, t.levyForcingBase_translation symmetric pol⟩

theorem IsLevyFormula.forcing_translation {n k : ℕ} {pol : LevyPolarity} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula pol k φ) (symmetric : Bool) (hk : 0 < k) :
    ∃ θ : SetTheorySemisentence (n + 5), IsLevyFormula pol k θ ∧ IsForcingTranslation (V := V) symmetric φ θ := by
  induction hφ with
  | bounded hφ => exact hφ.forcing_translation symmetric _ hk
  | @raise p q k n φ hφ ih =>
    cases k with
    | zero => exact (hφ.zero_bounded rfl).forcing_translation symmetric q hk
    | succ k =>
      obtain ⟨θ, hθ, he⟩ := ih (by omega)
      exact ⟨θ, .raise hθ, he⟩
  | and hφ hψ ihφ ihψ =>
    obtain ⟨θ, hθ, heθ⟩ := ihφ hk
    obtain ⟨η, hη, heη⟩ := ihψ hk
    exact ⟨θ.and η, .and hθ hη, heθ.and heη⟩
  | or hφ hψ ihφ ihψ =>
    obtain ⟨θ, hθ, heθ⟩ := ihφ hk
    obtain ⟨η, hη, heη⟩ := ihψ hk
    exact ⟨levyForcingOrStep θ η, levyForcingOrStep_levy hθ hη, heθ.or heη⟩
  | boundedAll t hφ ih =>
    obtain ⟨θ, hθ, heθ⟩ := ih hk
    exact ⟨forcingTransitiveBind _ (levyForcingBoundedAllBody t θ),
      forcingTransitiveBind_levy hk (levyForcingBoundedAllBody_levy t hθ), heθ.boundedAll t _⟩
  | boundedExs t hφ ih =>
    obtain ⟨θ, hθ, heθ⟩ := ih hk
    exact ⟨forcingTransitiveBind _ (levyForcingBoundedExsBody t θ),
      forcingTransitiveBind_levy hk (levyForcingBoundedExsBody_levy t hθ), heθ.boundedExs t _⟩
  | exs hφ ih =>
    obtain ⟨θ, hθ, heθ⟩ := ih hk
    exact ⟨levyForcingExsStep symmetric θ, levyForcingExsStep_sigma symmetric hθ, heθ.exs⟩
  | all hφ ih =>
    obtain ⟨θ, hθ, heθ⟩ := ih hk
    exact ⟨levyForcingAllStep symmetric θ, levyForcingAllStep_pi symmetric hθ, heθ.all⟩

end ZFVP
