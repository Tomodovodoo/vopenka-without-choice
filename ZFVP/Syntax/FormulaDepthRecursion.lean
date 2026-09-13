import ZFVP.Syntax.FormulaRecursion

/-! Formula recursion carrying an internal natural-number depth. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def formulaDepthDomain (L Γ : V) : V := formulaFamily L Γ ×ˢ (ω : V)

noncomputable def formulaDepthRelation (D : V) : V :=
  {p ∈ D ×ˢ D ; IsImmediateSubformula (kpair.π₁ (kpair.π₁ p)) (kpair.π₁ (kpair.π₂ p))}

instance formulaDepthDomain_definable : ℒₛₑₜ-function₂[V] formulaDepthDomain := by
  unfold formulaDepthDomain
  definability

theorem kpair_mem_formulaDepthRelation_iff (D x y : V) :
    ⟨x, y⟩ₖ ∈ formulaDepthRelation D ↔ x ∈ D ∧ y ∈ D ∧
      IsImmediateSubformula (kpair.π₁ x) (kpair.π₁ y) := by
  simp [formulaDepthRelation, and_assoc]

instance formulaDepthRelation_definable : ℒₛₑₜ-function₁[V] formulaDepthRelation := by
  have h : ℒₛₑₜ-relation (fun R D : V ↦ ∀ p, p ∈ R ↔ p ∈ D ×ˢ D ∧
      IsImmediateSubformula (kpair.π₁ (kpair.π₁ p)) (kpair.π₁ (kpair.π₂ p))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = formulaDepthRelation (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [formulaDepthRelation, mem_sep_iff]

theorem formulaDepthRelation_wellFounded (D : V) :
    IsInternallyWellFounded (formulaDepthRelation D) D := by
  apply projectedRank_internallyWellFounded _ _ (fun x ↦ kpair.π₂ (kpair.π₁ x)) (by definability)
  intro x _ y _ hxy
  exact immediateSubformula_rank ((kpair_mem_formulaDepthRelation_iff D x y).mp hxy).2.2

@[simp] theorem pair_mem_formulaDepthDomain (L Γ p k : V) :
    ⟨p, k⟩ₖ ∈ formulaDepthDomain L Γ ↔ p ∈ formulaFamily L Γ ∧ k ∈ (ω : V) := by
  simp [formulaDepthDomain]

noncomputable def formulaDepthRecursion (L Γ : V) (F : V → V → V)
    (hF : ℒₛₑₜ-function₂ F) : V :=
  wellFoundedRecursion (formulaDepthRelation_wellFounded (formulaDepthDomain L Γ)) F hF

instance formulaDepthRecursion_isFunction (L Γ : V) (F : V → V → V)
    (hF : ℒₛₑₜ-function₂ F) : IsFunction (formulaDepthRecursion L Γ F hF) :=
  wellFoundedRecursion_isFunction _ _ _

@[simp] theorem domain_formulaDepthRecursion (L Γ : V) (F : V → V → V)
    (hF : ℒₛₑₜ-function₂ F) : domain (formulaDepthRecursion L Γ F hF) = formulaDepthDomain L Γ :=
  domain_wellFoundedRecursion _ _ _

theorem formulaDepthRecursion_value (L Γ : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F)
    {q : V} (hq : q ∈ formulaDepthDomain L Γ) :
    (formulaDepthRecursion L Γ F hF) ‘ q = F q ((formulaDepthRecursion L Γ F hF) ↾
      (predecessors (formulaDepthRelation (formulaDepthDomain L Γ)) (formulaDepthDomain L Γ) q)) :=
  wellFoundedRecursion_value _ _ _ hq

theorem formulaDepthRecursion_previous {L Γ p q i j : V} (hL : IsLanguageCode L)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (hq : q ∈ formulaFamily L Γ)
    (hi : i ∈ (ω : V)) (hj : j ∈ (ω : V)) (hpq : IsImmediateSubformula p q) :
    ((formulaDepthRecursion L Γ F hF) ↾
      (predecessors (formulaDepthRelation (formulaDepthDomain L Γ)) (formulaDepthDomain L Γ)
        ⟨q, j⟩ₖ)) ‘ ⟨p, i⟩ₖ = (formulaDepthRecursion L Γ F hF) ‘ ⟨p, i⟩ₖ := by
  have hp := immediateSubformula_mem_family hL hq hpq
  have hpi : ⟨p, i⟩ₖ ∈ formulaDepthDomain L Γ := (pair_mem_formulaDepthDomain _ _ _ _).mpr ⟨hp, hi⟩
  have hqj : ⟨q, j⟩ₖ ∈ formulaDepthDomain L Γ := (pair_mem_formulaDepthDomain _ _ _ _).mpr ⟨hq, hj⟩
  apply value_restrict (by simpa using hpi)
  apply (mem_predecessors_iff _ _ _ _).mpr
  refine ⟨hpi, (kpair_mem_formulaDepthRelation_iff _ _ _).mpr ⟨hpi, hqj, ?_⟩⟩
  simpa using hpq

end ZFVP
