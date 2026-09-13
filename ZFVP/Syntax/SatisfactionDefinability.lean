import ZFVP.Syntax.SatisfactionEquations

/-! A definable graph characterization for satisfaction with all inputs varying. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem termEvaluation_comp {k : ℕ} {L Γ n M b e : (Fin k → V) → V}
    (hL : Language.DefinableFunction ℒₛₑₜ L) (hΓ : Language.DefinableFunction ℒₛₑₜ Γ)
    (hn : Language.DefinableFunction ℒₛₑₜ n) (hM : Language.DefinableFunction ℒₛₑₜ M)
    (hb : Language.DefinableFunction ℒₛₑₜ b) (he : Language.DefinableFunction ℒₛₑₜ e) :
    Language.DefinableFunction ℒₛₑₜ (fun v ↦ termEvaluation (L v) (Γ v) (n v) (M v) (b v) (e v)) :=
  Language.DefinableFunction.substitution (f := ![L, Γ, n, M, b, e]) termEvaluation_definable
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hL, hΓ, hn, hM, hb, he])

def IsSatisfactionGraph (L Γ M e g : V) : Prop :=
  IsFunction g ∧ domain g = formulaFamily L Γ ∧
  ∀ p ∈ formulaFamily L Γ, ∀ b, b ∈ g ‘ p ↔ b ∈ structureDomain M ^ (kpair.π₁ p) ∧
    SatisfactionStepHolds L Γ M e p
      (g ↾ (predecessors (subformulaRelation (formulaFamily L Γ)) (formulaFamily L Γ) p)) b

theorem satisfactionGraph_eq_iff (L Γ M e g : V) :
    satisfactionGraph L Γ M e = g ↔ IsSatisfactionGraph L Γ M e g := by
  constructor
  · rintro rfl
    refine ⟨inferInstance, domain_satisfactionGraph _ _ _ _, ?_⟩
    intro p hp b
    have h := formulaRecursion_value L Γ (satisfactionStep L Γ M e) inferInstance hp
    change b ∈ (formulaRecursion L Γ (satisfactionStep L Γ M e) inferInstance) ‘ p ↔ _
    rw [h, mem_satisfactionStep_iff]
    rfl
  · rintro ⟨hg, hd, hrec⟩
    apply (formulaRecursion_eq_iff L Γ (satisfactionStep L Γ M e) inferInstance g).mpr
    refine ⟨⟨hg, ⟨?_, ?_⟩, ?_⟩, hd⟩
    · rw [hd]
    · intro p hp q hq
      rw [hd]
      exact (mem_predecessors_iff _ _ _ _).mp hq |>.1
    · intro p hp
      apply mem_ext
      intro b
      rw [mem_satisfactionStep_iff]
      exact hrec p (hd ▸ hp) b

theorem satisfactionGraph_existsUnique (L Γ M e : V) : ∃! g, IsSatisfactionGraph L Γ M e g := by
  refine ⟨satisfactionGraph L Γ M e, (satisfactionGraph_eq_iff _ _ _ _ _).mp rfl, ?_⟩
  intro g hg
  exact ((satisfactionGraph_eq_iff _ _ _ _ _).mpr hg).symm

theorem satisfies_formula_mem {L Γ M e n φ b : V} (h : Satisfies L Γ M e n φ b) :
    φ ∈ formulaSet L Γ n := by
  by_contra hφ
  have hp : ⟨n, φ⟩ₖ ∉ domain (satisfactionGraph L Γ M e) := by
    simpa only [domain_satisfactionGraph, ← mem_formulaSet_iff] using hφ
  unfold Satisfies at h
  rw [value_eq_empty_of_not_mem_domain hp] at h
  exact not_mem_empty h

end ZFVP
