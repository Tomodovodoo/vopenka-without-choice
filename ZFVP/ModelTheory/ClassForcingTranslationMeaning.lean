import ZFVP.Syntax.ClassForcingTranslation
import ZFVP.ModelTheory.ForcingRankTruth

set_option maxHeartbeats 800000
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Higher-quantifier forcing semantics derived solely from the carrier/order/name
readouts and bounded atomic clauses. No endpoint carrier is a rank parameter. -/
theorem ClassForcingDictionary.translation_meaning (d : ClassForcingDictionary)
    (U P R : V) (hR : IsForcingPreorder P R) (hPU : P ⊆ U)
    (hc : ∀ p : SetDomain U, d.carrier.Evalb ![p] ↔ p.val ∈ P)
    (ho : ∀ p q : SetDomain U, d.order.Evalb ![p, q] ↔ ⟨p.val, q.val⟩ₖ ∈ R)
    (hn : ∀ u : SetDomain U, d.names.Evalb ![u] ↔ IsForcingName P u.val)
    (hb : ∀ {n : ℕ} (φ : BoundedFormulaTree n) (v : Fin n → SetDomain U),
      (∀ i, IsForcingName P (v i).val) → ∀ p : SetDomain U,
        (d.base φ).Evalb (p :> v) ↔
          p.val ∈ classForcingFormula P R (fun x ↦ x ∈ U ∧ IsForcingName P x)
            (by definability) φ.formula (standardTuple (fun i ↦ (v i).val)))
    {n : ℕ} (φ : SetTheorySemisentence n) :
    ∀ (v : Fin n → SetDomain U), (∀ i, IsForcingName P (v i).val) → ∀ p : SetDomain U,
      (d.translation φ).Evalb (p :> v) ↔
        p.val ∈ classForcingFormula P R (fun x ↦ x ∈ U ∧ IsForcingName P x)
          (by definability) φ (standardTuple (fun i ↦ (v i).val)) := by
  induction φ with
  | verum =>
    intro v hv p
    change (d.carrier.subst ![.bvar 0]).Evalb (p :> v) ↔ p.val ∈ P
    simpa [Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def] using hc p
  | falsum => intro v hv p; change False ↔ p.val ∈ (∅ : V); simp
  | rel r ts => intro v hv p; exact hb (.rel r ts) v hv p
  | nrel r ts => intro v hv p; exact hb (.nrel r ts) v hv p
  | and φ ψ ihφ ihψ =>
    intro v hv p
    change ((d.translation φ).Evalb (p :> v) ∧ (d.translation ψ).Evalb (p :> v)) ↔ _
    rw [ihφ v hv p, ihψ v hv p, classForcingFormula_and, mem_inter_iff]
  | or φ ψ ihφ ihψ =>
    intro v hv p
    rw [ClassForcingDictionary.translation, d.eval_orStep, classForcingFormula_or, mem_forcingClosure_iff]
    simp only [hc, ho, ihφ v hv, ihψ v hv, mem_union_iff]
    apply and_congr_right
    intro hp
    constructor
    · intro h q hq hqp
      obtain ⟨r, hr, hrq, hf⟩ := h ⟨q, hPU q hq⟩ hq hqp
      exact ⟨r.val, hf, hrq⟩
    · intro h q hq hqp
      obtain ⟨r, hr, hrq⟩ := h q.val hq hqp
      have hrP : r ∈ P := hr.elim
        ((classForcingFormula_regular _ (by definability) hR φ _).1 r)
        ((classForcingFormula_regular _ (by definability) hR ψ _).1 r)
      exact ⟨⟨r, hPU r hrP⟩, hrP, hrq, hr⟩
  | all φ ih =>
    intro v hv p
    rw [ClassForcingDictionary.translation, d.eval_allStep,
      classForcingFormula_all, mem_forcingClassIntersection_iff]
    simp only [hc, hn]
    apply and_congr Iff.rfl
    constructor
    · intro h u hu
      exact (ih (⟨u, hu.1⟩ :> v) (fun i ↦ Fin.cases hu.2 hv i) p).mp (h ⟨u, hu.1⟩ hu.2)
    · intro h u hu
      exact (ih (u :> v) (fun i ↦ Fin.cases hu hv i) p).mpr (h u.val ⟨u.property, hu⟩)
  | exs φ ih =>
    intro v hv p
    rw [ClassForcingDictionary.translation, d.eval_exsStep, classForcingFormula_exs_dense_iff]
    simp only [hc, ho, hn]
    apply and_congr Iff.rfl
    constructor
    · intro h q hq hqp
      obtain ⟨r, hr, hrq, u, hu, hf⟩ := h ⟨q, hPU q hq⟩ hq hqp
      exact ⟨r.val, hr, hrq, u.val, ⟨u.property, hu⟩,
        (ih (u :> v) (fun i ↦ Fin.cases hu hv i) r).mp hf⟩
    · intro h q hq hqp
      obtain ⟨r, hr, hrq, u, hu, hf⟩ := h q.val hq hqp
      exact ⟨⟨r, hPU r hr⟩, hr, hrq, ⟨u, hu.1⟩, hu.2,
        (ih (⟨u, hu.1⟩ :> v) (fun i ↦ Fin.cases hu.2 hv i) ⟨r, hPU r hr⟩).mpr hf⟩

end ZFVP

