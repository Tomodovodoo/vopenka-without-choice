import ZFVP.SetTheory.DeltaOneForcingNames
import ZFVP.ModelTheory.TransitiveZFNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Name validity using a condition predicate, with no forcing-set parameter. -/
def classCarrierNameFormula (φ : SetTheorySemisentence 1) : SetTheorySemisentence 1 :=
  “τ. ∃ C, !sigmaOneNameClosureFormula C τ ∧
    ∀ σ ∈ C, ∀ z ∈ σ, ∃ u, ∃ p, !φ p ∧ !boundedKpairFormula z u p”

theorem classCarrierNameFormula_sigma {k : ℕ} {φ : SetTheorySemisentence 1}
    (hφ : IsSigmaFormula (k + 1) φ) :
    IsSigmaFormula (k + 1) (classCarrierNameFormula φ) :=
  .exs (.and ((sigmaOneNameClosureFormula_sigmaOne.mono (by omega)).subst _)
    (.boundedAll _ (.boundedAll _ (.exs (.exs
      (.and (hφ.subst _) (.bounded (boundedKpairFormula_bounded.subst _))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_classCarrierNameFormula (φ : SetTheorySemisentence 1) (τ : V) :
    (classCarrierNameFormula φ).Evalb ![τ] ↔
      ∀ σ ∈ nameClosure τ, ∀ z ∈ σ, ∃ u p : V, φ.Evalb ![p] ∧ z = ⟨u, p⟩ₖ := by
  simp [classCarrierNameFormula]

theorem eval_classCarrierNameFormula_of_carrier (φ : SetTheorySemisentence 1) (P τ : V)
    (hφ : ∀ p : V, φ.Evalb ![p] ↔ p ∈ P) :
    (classCarrierNameFormula φ).Evalb ![τ] ↔ IsForcingName P τ := by
  rw [eval_classCarrierNameFormula]
  simp only [hφ, IsForcingName]

/-- The carrier set is external to the transitive model. Only the formula is
used internally; even its name-closure witnesses are computed internally. -/
theorem eval_classCarrierNameFormula_transitive (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (φ : SetTheorySemisentence 1) (P : V)
    (hφ : ∀ p : SetDomain U, φ.Evalb ![p] ↔ p.val ∈ P)
    (τ : SetDomain U) :
    (classCarrierNameFormula φ).Evalb ![τ] ↔ IsForcingName P τ.val := by
  rw [eval_classCarrierNameFormula]
  constructor
  · intro h σ hσ z hz
    have hσ' : σ ∈ (nameClosure τ).val := TransitiveZF.nameClosure_val U τ ▸ hσ
    let σ' : SetDomain U := ⟨σ, (inferInstance : IsTransitive U).mem_trans hσ' (nameClosure τ).property⟩
    let z' : SetDomain U := ⟨z, (inferInstance : IsTransitive U).mem_trans hz σ'.property⟩
    obtain ⟨u, p, hp, he⟩ := h σ' hσ' z' hz
    refine ⟨u.val, p.val, (hφ p).mp hp, ?_⟩
    simpa only [TransitiveZF.kpair_val U] using congrArg Subtype.val he
  · intro h σ hσ z hz
    have hσ' : σ.val ∈ nameClosure τ.val := TransitiveZF.nameClosure_val U τ ▸ hσ
    obtain ⟨u, p, hp, he⟩ := h σ.val hσ' z.val hz
    have hup := kpair_components_mem_transitive (he ▸ z.property)
    let u' : SetDomain U := ⟨u, hup.1⟩
    let p' : SetDomain U := ⟨p, hup.2⟩
    refine ⟨u', p', (hφ p').mpr hp, ?_⟩
    apply Subtype.ext
    simpa only [TransitiveZF.kpair_val U] using he

end ZFVP
