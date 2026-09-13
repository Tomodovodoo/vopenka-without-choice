import ZFVP.ModelTheory.ForcingFunctionValues

/-! Initial and successor witnesses can be chosen among subnames of the
named domain after strengthening a condition. Generic filters are used only
externally to prove these statements about internal forcing sets. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def serialHullPremiseFormula : SetTheorySemisentence 2 :=
  f“A R. (∃ x, x ∈ A) ∧ ∀ x ∈ A, ∃ y ∈ A, !kpair.dfn x y ∈ R”

def serialHullInitialFormula : SetTheorySemisentence 2 :=
  “A y. y ∈ A”

def serialHullNextFormula : SetTheorySemisentence 4 :=
  f“A R x y. y ∈ A ∧ !kpair.dfn x y ∈ R”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_serialHullPremiseFormula (v : Fin 2 → V) :
    serialHullPremiseFormula.Evalb v ↔
      IsNonempty (v 0) ∧ ∀ x ∈ v 0, ∃ y ∈ v 0, ⟨x, y⟩ₖ ∈ v 1 := by
  simp [serialHullPremiseFormula, isNonempty_def]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_serialHullInitialFormula (v : Fin 2 → V) :
    serialHullInitialFormula.Evalb v ↔ v 1 ∈ v 0 := by
  simp [serialHullInitialFormula]

theorem eval_serialHullNextFormula (v : Fin 4 → V) :
    serialHullNextFormula.Evalb v ↔ v 3 ∈ v 0 ∧ ⟨v 2, v 3⟩ₖ ∈ v 1 := by
  simp [serialHullNextFormula]

theorem serialHull_initial_candidate_countable [Countable V] {P R one p q : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (A S : ForcingName P)
    (hp : p ∈ forcingFormula P R serialHullPremiseFormula (standardTuple ![A.val, S.val]))
    (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R) :
    ∃ r ∈ P, ∃ ν ∈ domain A.val, IsForcingName P ν ∧ ⟨r, q⟩ₖ ∈ R ∧
      r ∈ forcingFormula P R serialHullInitialFormula (standardTuple ![A.val, ν]) := by
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hR hq
  let M : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  have hqpre := (forcingFormula_regular hR serialHullPremiseFormula _).2.1 p hp q hq hqp
  have hpre := (eval_serialHullPremiseFormula _).mp
    ((M.formula_truth serialHullPremiseFormula ![A, S]).mpr ⟨q, hqG, hqpre⟩)
  obtain ⟨x, hx⟩ := hpre.1.nonempty
  obtain ⟨ν, t, htG, hνt, rfl⟩ := (M.mem_ofName_iff A x).mp hx
  have he : serialHullInitialFormula.Evalb (fun i ↦ M.ofName (![A, ν] i)) :=
    (eval_serialHullInitialFormula _).mpr hx
  obtain ⟨u, huG, hu⟩ := (M.formula_truth serialHullInitialFormula ![A, ν]).mp he
  obtain ⟨r, hrG, hrq, hru⟩ := hG.1.2.2.2 q hqG u huG
  have hr := hG.1.1 r hrG
  exact ⟨r, hr, ν.val, mem_domain_of_kpair_mem hνt, ν.property, hrq,
    (forcingFormula_regular hR serialHullInitialFormula _).2.1 u hu r hr hru⟩

theorem serialHull_next_candidate_countable [Countable V] {P R one p q : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (A S τ : ForcingName P)
    (hp : p ∈ forcingFormula P R serialHullPremiseFormula (standardTuple ![A.val, S.val]))
    (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R)
    (hτ : q ∈ forcingFormula P R serialHullInitialFormula (standardTuple ![A.val, τ.val])) :
    ∃ r ∈ P, ∃ ν ∈ domain A.val, IsForcingName P ν ∧ ⟨r, q⟩ₖ ∈ R ∧
      r ∈ forcingFormula P R serialHullNextFormula (standardTuple ![A.val, S.val, τ.val, ν]) := by
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hR hq
  let M : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  have hqpre := (forcingFormula_regular hR serialHullPremiseFormula _).2.1 p hp q hq hqp
  have hpre := (eval_serialHullPremiseFormula _).mp
    ((M.formula_truth serialHullPremiseFormula ![A, S]).mpr ⟨q, hqG, hqpre⟩)
  have hτA := (eval_serialHullInitialFormula _).mp
    ((M.formula_truth serialHullInitialFormula ![A, τ]).mpr ⟨q, hqG, hτ⟩)
  obtain ⟨y, hy, hτy⟩ := hpre.2 (M.ofName τ) hτA
  obtain ⟨ν, t, htG, hνt, rfl⟩ := (M.mem_ofName_iff A y).mp hy
  have he : serialHullNextFormula.Evalb (fun i ↦ M.ofName (![A, S, τ, ν] i)) :=
    (eval_serialHullNextFormula _).mpr ⟨hy, hτy⟩
  obtain ⟨u, huG, hu⟩ := (M.formula_truth serialHullNextFormula ![A, S, τ, ν]).mp he
  obtain ⟨r, hrG, hrq, hru⟩ := hG.1.2.2.2 q hqG u huG
  have hr := hG.1.1 r hrG
  exact ⟨r, hr, ν.val, mem_domain_of_kpair_mem hνt, ν.property, hrq,
    (forcingFormula_regular hR serialHullNextFormula _).2.1 u hu r hr hru⟩

end ZFVP
