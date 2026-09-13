import ZFVP.SetTheory.SigmaThreeLeastPrefixCutoff
import ZFVP.SetTheory.WoodinNamedPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def namedCheckedLevyForcingFormula (θ : SetTheorySemisentence 5) : SetTheorySemisentence 6 :=
  “P R one p τ δ. ∀ υ, !(sigmaOneCheckNameFormula true) one δ υ → !θ P R p τ υ”

theorem namedCheckedLevyForcingFormula_piTwo {θ : SetTheorySemisentence 5}
    (hθ : IsPiFormula 2 θ) : IsPiFormula 2 (namedCheckedLevyForcingFormula θ) :=
  .all (.or (.raise ((sigmaOneCheckNameFormula_sigmaOne true).subst _).neg) (hθ.subst _))

def piTwoNamedPrefixCutoffBody (Ψ : SetTheorySemisentence 6) : SetTheorySemisentence 6 :=
  “P R one γ τ δ. γ ∈ δ ∧ !rankCriterionFormula δ ∧ ∀ p ∈ P, !Ψ P R one p τ δ”

theorem piTwoNamedPrefixCutoffBody_piTwo {Ψ : SetTheorySemisentence 6} (hΨ : IsPiFormula 2 Ψ) :
    IsPiFormula 2 (piTwoNamedPrefixCutoffBody Ψ) :=
  .and (.bounded (.rel _ _)) (.and (.raise (rankCriterionFormula_piOne.subst _))
    (.boundedAll (.bvar 0) (hΨ.subst _)))

def leastNamedPrefixCutoffBody (Ξ : SetTheorySemisentence 6) : SetTheorySemisentence 6 :=
  “P R one γ τ δ. !IsOrdinal.dfn δ ∧ !Ξ P R one γ τ δ ∧
    ∀ β ∈ δ, ¬!Ξ P R one γ τ β”

theorem leastNamedPrefixCutoffBody_levy {Ξ : SetTheorySemisentence 6} (hΞ : IsPiFormula 2 Ξ)
    (pol : LevyPolarity) : IsLevyFormula pol 3 (leastNamedPrefixCutoffBody Ξ) :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.and (.raise (hΞ.subst _)) (.raise (.boundedAll (.bvar 5) (hΞ.subst _).neg)))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_namedCheckedLevyForcingFormula (θ : SetTheorySemisentence 5) (P R one p τ δ : V) :
    (namedCheckedLevyForcingFormula θ).Evalb ![P, R, one, p, τ, δ] ↔
      θ.Evalb ![P, R, p, τ, checkName one δ] := by
  simp [namedCheckedLevyForcingFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, eval_sigmaOneCheckNameFormula, TruthAnswer]

theorem forcing_namedLocalRestoration_piTwo_uniform :
    ∃ Ψ : SetTheorySemisentence 6, IsPiFormula 2 Ψ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ P R one p τ δ : V, IsForcingPreorder P R → IsForcingTop P R one →
          p ∈ P → IsForcingName P τ → p ∈ forcingFormula P R boundedZeroMemberFormula (standardTuple ![τ]) →
          (Ψ.Evalb ![P, R, one, p, τ, δ] ↔
            p ∈ forcingFormula P R woodinLocalRestorationFormula (standardTuple ![τ, checkName one δ])) := by
  obtain ⟨Φ, hΦ, hlocal⟩ := woodinLocalRestoration_piTwo_uniform.{u}
  obtain ⟨θ, hθ, he⟩ := IsLevyFormula.ordinaryForcing_definition_uniform.{u} hΦ (by omega)
  refine ⟨namedCheckedLevyForcingFormula θ, namedCheckedLevyForcingFormula_piTwo hθ, ?_⟩
  intro V _ _ _ P R one p τ δ hR ht hp hτ hz
  rw [eval_namedCheckedLevyForcingFormula]
  have hnames : ∀ i : Fin 2, IsForcingName P (![τ, checkName one δ] i) := by
    intro i
    exact Fin.cases hτ (fun j ↦ Fin.cases (checkName_isName ht.1 δ) (fun k ↦ Fin.elim0 k) j) i
  apply (he V P R hR ![τ, checkName one δ] hnames p).trans
  let guard : SetTheorySemisentence 2 := boundedZeroMemberFormula.subst
    (fun i ↦ .bvar ((![0] : Fin 1 → Fin 2) i))
  let c : Fin 2 → ForcingName P := fun i ↦ ⟨![τ, checkName one δ] i, hnames i⟩
  have hg : p ∈ forcingFormula P R guard (standardTuple ![τ, checkName one δ]) := by
    unfold guard
    rw [forcingFormula_rename]
    exact hz
  apply forcingFormula_iff_under guard Φ woodinLocalRestorationFormula
    (fun W _ _ _ v hv ↦ ?_) hR ht hp c hg
  have hk : (∅ : W) ∈ v 0 := by
    simpa [guard, boundedZeroMemberFormula, Semiformula.eval_substs] using hv
  have hv' : ![v 0, v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [← hv']
  exact (hlocal W (v 0) (v 1) hk).trans
    (woodinLocalRestorationFormula_defined.iff ![v 0, v 1]).symm

theorem woodinNamedPrefixCutoff_piTwo_uniform :
    ∃ Ξ : SetTheorySemisentence 6, IsPiFormula 2 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ P R one γ τ δ : V, IsForcingPreorder P R → IsForcingTop P R one → IsForcingName P τ →
          (∀ p ∈ P, p ∈ forcingFormula P R boundedZeroMemberFormula (standardTuple ![τ])) →
          (Ξ.Evalb ![P, R, one, γ, τ, δ] ↔ IsWoodinNamedPrefixCutoff P R one γ τ δ) := by
  obtain ⟨Ψ, hΨ, he⟩ := forcing_namedLocalRestoration_piTwo_uniform.{u}
  refine ⟨piTwoNamedPrefixCutoffBody Ψ, piTwoNamedPrefixCutoffBody_piTwo hΨ, ?_⟩
  intro V _ _ _ P R one γ τ δ hR ht hτ hz
  have hb : (piTwoNamedPrefixCutoffBody Ψ).Evalb ![P, R, one, γ, τ, δ] ↔
      γ ∈ δ ∧ IsChoicelessInaccessible δ ∧ ∀ p ∈ P, Ψ.Evalb ![P, R, one, p, τ, δ] := by
    simp [piTwoNamedPrefixCutoffBody, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb,
      rankCriterionHeight_iff_choicelessInaccessible]
  rw [hb]
  unfold IsWoodinNamedPrefixCutoff
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  exact forall_congr' fun p ↦ forall_congr' fun hp ↦ he V P R one p τ δ hR ht hp hτ (hz p hp)

theorem leastWoodinNamedPrefixCutoff_deltaThree_uniform :
    ∃ Λ : SetTheorySemisentence 6, (∀ pol, IsLevyFormula pol 3 Λ) ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ P R one γ τ δ : V, IsForcingPreorder P R → IsForcingTop P R one → IsForcingName P τ →
          (∀ p ∈ P, p ∈ forcingFormula P R boundedZeroMemberFormula (standardTuple ![τ])) →
          (Λ.Evalb ![P, R, one, γ, τ, δ] ↔
            IsLeastOrdinal (IsWoodinNamedPrefixCutoff P R one γ τ) δ) := by
  obtain ⟨Ξ, hΞ, he⟩ := woodinNamedPrefixCutoff_piTwo_uniform.{u}
  refine ⟨leastNamedPrefixCutoffBody Ξ, leastNamedPrefixCutoffBody_levy hΞ, ?_⟩
  intro V _ _ _ P R one γ τ δ hR ht hτ hz
  have hb : (leastNamedPrefixCutoffBody Ξ).Evalb ![P, R, one, γ, τ, δ] ↔
      IsOrdinal δ ∧ Ξ.Evalb ![P, R, one, γ, τ, δ] ∧ ∀ β ∈ δ, ¬Ξ.Evalb ![P, R, one, γ, τ, β] := by
    simp [leastNamedPrefixCutoffBody, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb, isLeastOrdinal_iff_no_smaller]
  simp only [he V P R one γ τ _ hR ht hτ hz]

theorem forces_zeroMember_of_regular {P R one p : V} (hR : IsForcingPreorder P R)
    (ht : IsForcingTop P R one) (hp : p ∈ P) (τ : ForcingName P)
    (hreg : p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![τ.val])) :
    p ∈ forcingFormula P R boundedZeroMemberFormula (standardTuple ![τ.val]) := by
  apply forcingFormula_entailment regularCardinalFormula boundedZeroMemberFormula
    (fun W _ _ _ v hv ↦ ?_) hR ht hp ![τ] hreg
  have hκ : IsRegularCardinal (v 0) := (regularCardinalFormula_defined.iff v).mp hv
  have hz : (∅ : W) ∈ v 0 := hκ.2.1 ∅ (by simp)
  simpa [boundedZeroMemberFormula] using hz

theorem woodinNamedPrefixCutoff_eq_iff_least_of_exists {P R one γ τ δ : V}
    (hex : ∃ η, IsWoodinNamedPrefixCutoff P R one γ τ η) :
    δ = woodinNamedPrefixCutoff P R one γ τ ↔
      IsLeastOrdinal (IsWoodinNamedPrefixCutoff P R one γ τ) δ := by
  obtain ⟨η, hη⟩ := hex
  have hs := woodinNamedPrefixCutoff_spec hη
  constructor
  · rintro rfl
    exact hs
  · intro hd
    exact subset_antisymm (hd.2.2 _ hs.1 hs.2.1) (hs.2.2 _ hd.1 hd.2.1)

end ZFVP
