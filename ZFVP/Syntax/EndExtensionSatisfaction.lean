import ZFVP.Syntax.EndExtensionAtomicTruth
import ZFVP.Syntax.EndExtensionAssignments
import ZFVP.Syntax.EndExtensionSubformulas
import ZFVP.Syntax.SatisfactionStepEquations

/-! Full arbitrary-language satisfaction is absolute under ZF membership end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem satisfactionStepHolds_iff (j : MembershipEndExtension V W) {L Γ n φ : V}
    (hL : IsLanguageCode L) (hφ : φ ∈ formulaSet L Γ n) (M e previous b : V) :
    SatisfactionStepHolds (j L) (j Γ) (j M) (j e) (j ⟨n, φ⟩ₖ) (j previous) (j b) ↔
      SatisfactionStepHolds L Γ M e ⟨n, φ⟩ₖ previous b := by
  have hn := formulaSet_context hL hφ
  rw [j.map_kpair]
  rcases formulaSet_cases hL hφ with rfl | rfl | ⟨r, args, _, he⟩ | ⟨ψ, χ, _, _, he⟩ | ⟨ψ, _, he⟩
  · rw [j.map_truthCode, satisfactionStepHolds_truth, satisfactionStepHolds_truth]
  · rw [j.map_falsityCode, satisfactionStepHolds_falsity, satisfactionStepHolds_falsity]
  · rcases he with rfl | rfl
    · rw [j.map_atomCode, satisfactionStepHolds_atom, satisfactionStepHolds_atom]
      exact j.atomicHolds_iff hL hn Γ M e b r args
    · rw [j.map_negAtomCode, satisfactionStepHolds_negAtom, satisfactionStepHolds_negAtom]
      exact not_congr (j.atomicHolds_iff hL hn Γ M e b r args)
  · rcases he with rfl | rfl
    · rw [j.map_andCode, satisfactionStepHolds_and, satisfactionStepHolds_and]
      simp only [← j.map_kpair, ← j.map_value_total, j.mem_iff]
    · rw [j.map_orCode, satisfactionStepHolds_or, satisfactionStepHolds_or]
      simp only [← j.map_kpair, ← j.map_value_total, j.mem_iff]
  · rcases he with rfl | rfl
    · rw [j.map_allCode, satisfactionStepHolds_all, satisfactionStepHolds_all,
        ← j.map_structureDomain, j.forall_mem_iff]
      simp only [← j.map_assignmentPrepend, ← j.map_succ, ← j.map_kpair, ← j.map_value_total, j.mem_iff]
    · rw [j.map_existsCode, satisfactionStepHolds_exists, satisfactionStepHolds_exists,
        ← j.map_structureDomain, j.exists_mem_iff]
      simp only [← j.map_assignmentPrepend, ← j.map_succ, ← j.map_kpair, ← j.map_value_total, j.mem_iff]

theorem map_satisfactionStep (j : MembershipEndExtension V W) {L Γ p : V}
    (hL : IsLanguageCode L) (hp : p ∈ formulaFamily L Γ) (M e previous : V) :
    j (satisfactionStep L Γ M e p previous) =
      satisfactionStep (j L) (j Γ) (j M) (j e) (j p) (j previous) := by
  obtain ⟨n, hn, φ, rfl⟩ := formulaFamily_context hL Γ hp
  have hφ := (mem_formulaSet_iff _ _ _ _).mpr hp
  have he := j.map_separation (structureDomain M ^ n)
    (fun b ↦ SatisfactionStepHolds L Γ M e ⟨n, φ⟩ₖ previous b)
    (fun b ↦ SatisfactionStepHolds (j L) (j Γ) (j M) (j e) (j ⟨n, φ⟩ₖ) (j previous) b)
    (by definability) (by definability) (fun b _ ↦ (j.satisfactionStepHolds_iff hL hφ M e previous b).symm)
  simpa only [satisfactionStep, j.map_kpair, kpair.π₁_kpair,
    j.map_finiteFunctionSet _ hn, j.map_structureDomain] using he

theorem map_satisfactionGraph (j : MembershipEndExtension V W) {L : V} (hL : IsLanguageCode L)
    (Γ M e : V) : j (satisfactionGraph L Γ M e) = satisfactionGraph (j L) (j Γ) (j M) (j e) := by
  symm
  apply (formulaRecursion_eq_iff _ _ _ _ _).mpr
  rw [totalRecursionAttempt_iff]
  refine ⟨j.map_function _, ?_, ?_⟩
  · rw [← j.map_domain, domain_satisfactionGraph, j.map_formulaFamily hL Γ]
  · intro u hu
    rw [← j.map_formulaFamily hL Γ] at hu
    obtain ⟨p, hp, rfl⟩ := j.endExtension _ u hu
    rw [← j.map_value_total]
    have hrec := formulaRecursion_value L Γ (satisfactionStep L Γ M e) inferInstance hp
    change (satisfactionGraph L Γ M e) ‘ p =
      satisfactionStep L Γ M e p ((satisfactionGraph L Γ M e) ↾
        (predecessors (subformulaRelation (formulaFamily L Γ)) (formulaFamily L Γ) p)) at hrec
    rw [hrec, j.map_satisfactionStep hL hp, j.map_restrict, j.map_formulaPredecessors hL hp]

theorem satisfies_iff (j : MembershipEndExtension V W) {L : V} (hL : IsLanguageCode L)
    (Γ M e n φ b : V) :
    Satisfies (j L) (j Γ) (j M) (j e) (j n) (j φ) (j b) ↔ Satisfies L Γ M e n φ b := by
  unfold Satisfies
  rw [← j.map_satisfactionGraph hL Γ M e, ← j.map_kpair, ← j.map_value_total, j.mem_iff]

end MembershipEndExtension
end ZFVP
