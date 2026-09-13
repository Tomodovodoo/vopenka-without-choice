import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.ModelTheory.ForcingModelChecks

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def checkedValueDecisionDensityFormula : SetTheorySemisentence 8 :=
  f“P R o t p A X a. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingNameFormula P t ∧ a ∈ A ∧
    !(checkedTripleForcingFormula boundedFunctionFormula) P R o t p A X →
      ∀ q ∈ P, !kpair.dfn q p ∈ R →
        ∃ r ∈ P, !kpair.dfn r q ∈ R ∧ ∃ x ∈ X,
          !checkedFunctionValueDecisionFormula P R o t r a x”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def checkedValueDecisions (P R one τ X a : V) : V :=
  {q ∈ P ; ∃ x ∈ X, ForcesCheckedFunctionValue P R one τ q a x}

instance checkedValueDecisions_definable (P R one τ X : V) :
    ℒₛₑₜ-function₁[V] (checkedValueDecisions P R one τ X) := by
  have h : ℒₛₑₜ-relation[V] (fun D a ↦ ∀ q, q ∈ D ↔
      q ∈ P ∧ ∃ x ∈ X, ForcesCheckedFunctionValue P R one τ q a x) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = checkedValueDecisions P R one τ X (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [checkedValueDecisions, mem_sep_iff]

theorem checkedValueDecisions_downward {P R one τ X a : V} (hR : IsForcingPreorder P R) :
    IsForcingDownwardClosed P R (checkedValueDecisions P R one τ X a) := by
  intro p hp q hq hqp
  obtain ⟨_, x, hx, hpx⟩ := mem_sep_iff.mp hp
  exact mem_sep_iff.mpr ⟨hq, x, hx,
    (forcingFormula_regular hR functionValueFormula _).2.1 p hpx q hq hqp⟩

theorem checkedValueDecisions_denseBelow_countable [Countable V]
    {P R one τ p A X a : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (ha : a ∈ A)
    (hf : p ∈ forcingFormula P R boundedFunctionFormula
      (standardTuple ![τ, checkName one A, checkName one X])) :
    ForcingDenseBelow P R (checkedValueDecisions P R one τ X a) p := by
  refine ⟨fun q hq ↦ (mem_sep_iff.mp hq).1, fun q hq hqp ↦ ?_⟩
  have hqf := (forcingFormula_regular hR boundedFunctionFormula _).2.1 p hf q hq hqp
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hR hq
  let S : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  let t : ForcingName P := ⟨τ, hτ⟩
  let u : ForcingName P := ⟨checkName one A, checkName_isName htop.1 A⟩
  let v : ForcingName P := ⟨checkName one X, checkName_isName htop.1 X⟩
  have he := (S.formula_truth boundedFunctionFormula ![t, u, v]).mpr ⟨q, hqG, hqf⟩
  have hfun : S.ofName t ∈ S.check X ^ S.check A := (Defined.eval_iff _).mp he
  have : IsFunction (S.ofName t) := IsFunction.of_mem hfun
  obtain ⟨x, hx, hv⟩ := (S.mem_check_iff X _).mp
    (function_value_mem hfun ((S.check_mem_iff a A).mpr ha))
  obtain ⟨r, hrG, hrx⟩ := (S.checkedFunctionValue_truth t a x).mpr ⟨inferInstance, hv⟩
  obtain ⟨s, hsG, hsr, hsq⟩ := hG.1.2.2.2 r hrG q hqG
  have hsP := hG.1.1 s hsG
  exact ⟨s, mem_sep_iff.mpr ⟨hsP, x, hx,
    (forcingFormula_regular hR functionValueFormula _).2.1 r hrx s hsP hsr⟩, hsq⟩

theorem eval_checkedValueDecisionDensityFormula (v : Fin 8 → V) :
    checkedValueDecisionDensityFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsForcingName (v 0) (v 3) → v 7 ∈ v 5 →
      v 4 ∈ forcingFormula (v 0) (v 1) boundedFunctionFormula
        (standardTuple ![v 3, checkName (v 2) (v 5), checkName (v 2) (v 6)]) →
      ∀ q ∈ v 0, ⟨q, v 4⟩ₖ ∈ v 1 →
        ∃ r ∈ v 0, ⟨r, q⟩ₖ ∈ v 1 ∧ ∃ x ∈ v 6,
          ForcesCheckedFunctionValue (v 0) (v 1) (v 2) (v 3) r (v 7) x) := by
  simp [checkedValueDecisionDensityFormula]

theorem checkedValueDecisions_denseBelow
    {P R one τ p A X a : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (ha : a ∈ A)
    (hf : p ∈ forcingFormula P R boundedFunctionFormula
      (standardTuple ![τ, checkName one A, checkName one X])) :
    ForcingDenseBelow P R (checkedValueDecisions P R one τ X a) p := by
  have hh := eval_of_countable_zf checkedValueDecisionDensityFormula (by
    intro W _ _ _ _ v
    apply (eval_checkedValueDecisionDensityFormula v).mpr
    intro hR htop hτ ha hf q hq hqp
    obtain ⟨r, hr, hrq⟩ := (checkedValueDecisions_denseBelow_countable hR htop hτ ha hf).2 q hq hqp
    obtain ⟨hrP, x, hx, hrx⟩ := mem_sep_iff.mp hr
    exact ⟨r, hrP, hrq, x, hx, hrx⟩) ![P, R, one, τ, p, A, X, a]
  have h := (eval_checkedValueDecisionDensityFormula _).mp hh hR htop hτ ha hf
  refine ⟨fun q hq ↦ (mem_sep_iff.mp hq).1, fun q hq hqp ↦ ?_⟩
  obtain ⟨r, hr, hrq, hx⟩ := h q hq hqp
  exact ⟨r, mem_sep_iff.mpr ⟨hr, hx⟩, hrq⟩

end ZFVP
