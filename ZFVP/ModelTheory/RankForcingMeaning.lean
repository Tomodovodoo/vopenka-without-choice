import ZFVP.Syntax.RankForcingTranslation
import ZFVP.ModelTheory.ForcingRankTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ : V} (hδ : Cn 1 δ)

include hδ in
private theorem rank_base_meaning (P R Γ F : SetDomain (hierarchy δ))
    (hR : IsForcingPreorder P.val R.val) {n : ℕ} (φ : BoundedFormulaTree n)
    (v : Fin n → SetDomain (hierarchy δ)) (hv : ∀ i, IsForcingName P.val (v i).val)
    (p : SetDomain (hierarchy δ)) :
    (φ.levyForcingBase .sigma).Evalb (P :> R :> Γ :> F :> p :> v) ↔
      p.val ∈ classForcingFormula P.val R.val (IsLowRankForcingName P.val δ)
        (by definability) φ.formula (standardTuple (fun i ↦ (v i).val)) := by
  let := hδ.ordinal
  have he := hδ.sigma_correct (φ.levyForcingBase_levy .sigma (by decide : 0 < 1))
    (P :> R :> Γ :> F :> p :> v)
  have hm := φ.forcingCertificate_meaning hR (IsLowRankForcingName P.val δ)
    (by definability) (fun _ h ↦ h.2) (fun _ h _ _ hu ↦ lowRankForcingName_subname h hu)
    (fun i ↦ (v i).val) (fun i ↦ ⟨(v i).property, hv i⟩) true p.val
  apply he.trans
  simpa [BoundedFormulaTree.levyForcingBase, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, forcingParameterTerms, Semiformula.Evalb, TruthAnswer] using hm

include hδ in
theorem rankForcingTranslation_meaning (P R Γ F : SetDomain (hierarchy δ))
    (hR : IsForcingPreorder P.val R.val) {n : ℕ} (φ : SetTheorySemisentence n) :
    ∀ (v : Fin n → SetDomain (hierarchy δ)), (∀ i, IsForcingName P.val (v i).val) →
      ∀ p : SetDomain (hierarchy δ),
        (rankForcingTranslation φ).Evalb (P :> R :> Γ :> F :> p :> v) ↔
          p.val ∈ classForcingFormula P.val R.val (IsLowRankForcingName P.val δ)
            (by definability) φ (standardTuple (fun i ↦ (v i).val)) := by
  let := hδ.ordinal
  have hmem {p : V} (hp : p ∈ P.val) : p ∈ hierarchy δ :=
    (hierarchy_transitive δ).mem_trans hp P.property
  induction φ with
  | verum => intro v hv p; rfl
  | falsum => intro v hv p; change False ↔ p.val ∈ (∅ : V); simp
  | rel r ts => intro v hv p; exact rank_base_meaning hδ P R Γ F hR (.rel r ts) v hv p
  | nrel r ts => intro v hv p; exact rank_base_meaning hδ P R Γ F hR (.nrel r ts) v hv p
  | and φ ψ ihφ ihψ =>
    intro v hv p
    change ((rankForcingTranslation φ).Evalb (P :> R :> Γ :> F :> p :> v) ∧
      (rankForcingTranslation ψ).Evalb (P :> R :> Γ :> F :> p :> v)) ↔ _
    rw [ihφ v hv p, ihψ v hv p, classForcingFormula_and, mem_inter_iff]
  | or φ ψ ihφ ihψ =>
    intro v hv p
    rw [rankForcingTranslation, eval_rankForcingOrStep hδ, classForcingFormula_or, mem_forcingClosure_iff]
    simp only [ihφ v hv, ihψ v hv, mem_union_iff]
    apply and_congr_right
    intro hp
    constructor
    · intro h q hq hqp
      obtain ⟨r, hr, hrq, hf⟩ := h ⟨q, hmem hq⟩ hq hqp
      exact ⟨r.val, hf, hrq⟩
    · intro h q hq hqp
      obtain ⟨r, hr, hrq⟩ := h q.val hq hqp
      have hrP : r ∈ P.val := hr.elim
        ((classForcingFormula_regular _ (by definability) hR φ _).1 r)
        ((classForcingFormula_regular _ (by definability) hR ψ _).1 r)
      exact ⟨⟨r, hmem hrP⟩, hrP, hrq, hr⟩
  | all φ ih =>
    intro v hv p
    rw [rankForcingTranslation, eval_rankForcingAllStep hδ,
      classForcingFormula_all, mem_forcingClassIntersection_iff]
    apply and_congr Iff.rfl
    constructor
    · intro h u hu
      exact (ih (⟨u, hu.1⟩ :> v) (fun i ↦ Fin.cases hu.2 hv i) p).mp (h ⟨u, hu.1⟩ hu.2)
    · intro h u hu
      exact (ih (u :> v) (fun i ↦ Fin.cases hu hv i) p).mpr (h u.val ⟨u.property, hu⟩)
  | exs φ ih =>
    intro v hv p
    rw [rankForcingTranslation, eval_rankForcingExsStep hδ, classForcingFormula_exs_dense_iff]
    apply and_congr Iff.rfl
    constructor
    · intro h q hq hqp
      obtain ⟨r, hr, hrq, u, hu, hf⟩ := h ⟨q, hmem hq⟩ hq hqp
      exact ⟨r.val, hr, hrq, u.val, ⟨u.property, hu⟩,
        (ih (u :> v) (fun i ↦ Fin.cases hu hv i) r).mp hf⟩
    · intro h q hq hqp
      obtain ⟨r, hr, hrq, u, hu, hf⟩ := h q.val hq hqp
      exact ⟨⟨r, hmem hr⟩, hr, hrq, ⟨u, hu.1⟩, hu.2,
        (ih (⟨u, hu.1⟩ :> v) (fun i ↦ Fin.cases hu.2 hv i) ⟨r, hmem hr⟩).mpr hf⟩

end ZFVP
