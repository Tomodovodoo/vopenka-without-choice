import ZFVP.Syntax.EndExtensionSubstitutionStates
import ZFVP.Syntax.EndExtensionSubformulas
import ZFVP.Syntax.FormulaSubstitutionDefinability
import ZFVP.SetTheory.EndExtensionWellOrdering

/-! Internal first-order substitution commutes with membership end
extensions at every internal binder depth, by uniqueness of recursion. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem map_formulaDepthDomain {L : V} (hL : IsLanguageCode L) (Γ : V) :
    j (formulaDepthDomain L Γ) = formulaDepthDomain (j L) (j Γ) := by
  simp only [formulaDepthDomain, j.map_prod, j.map_formulaFamily hL Γ, j.map_omega]

theorem map_formulaDepthPredecessors {D q : V} (hq : q ∈ D) :
    j (predecessors (formulaDepthRelation D) D q) =
      predecessors (formulaDepthRelation (j D)) (j D) (j q) := by
  have hv : predecessors (formulaDepthRelation D) D q =
      {p ∈ D ; IsImmediateSubformula (kpair.π₁ p) (kpair.π₁ q)} := by
    ext p
    simp only [mem_predecessors_iff, kpair_mem_formulaDepthRelation_iff, hq, mem_sep_iff]
    tauto
  have hw : predecessors (formulaDepthRelation (j D)) (j D) (j q) =
      {p ∈ j D ; IsImmediateSubformula (kpair.π₁ p) (kpair.π₁ (j q))} := by
    ext p
    simp only [mem_predecessors_iff, kpair_mem_formulaDepthRelation_iff,
      (j.mem_iff q D).mpr hq, mem_sep_iff]
    tauto
  rw [hv, hw]
  apply j.map_separation
  intro p _
  rw [← j.map_first, ← j.map_first, j.immediateSubformula_iff]

theorem map_substitutionChild (q φ : V) : j (substitutionChild q φ) = substitutionChild (j q) (j φ) := by
  simp only [substitutionChild, j.map_kpair, j.map_first, j.map_second]

theorem map_substitutionBody (q φ : V) : j (substitutionBody q φ) = substitutionBody (j q) (j φ) := by
  simp only [substitutionBody, j.map_kpair, j.map_first, j.map_second, j.map_succ]

theorem map_substitutedArguments {L Γ G q : V} (hL : IsLanguageCode L)
    (hn : kpair.π₁ (kpair.π₁ q) ∈ (ω : V)) (args : V) :
    j (substitutedArguments L Γ G q args) = substitutedArguments (j L) (j Γ) (j G) (j q) (j args) := by
  simp only [substitutedArguments, j.map_compose, j.map_termSubstitution hL hn,
    j.map_stateBound, j.map_stateFree, j.map_value_total, j.map_first, j.map_second]

theorem map_formulaSubstitutionStep {L Γ G q : V} (hL : IsLanguageCode L)
    (hn : kpair.π₁ (kpair.π₁ q) ∈ (ω : V)) (previous : V) :
    j (formulaSubstitutionStep L Γ G q previous) =
      formulaSubstitutionStep (j L) (j Γ) (j G) (j q) (j previous) := by
  have he (k : ℕ) : kpair.π₁ (kpair.π₂ (kpair.π₁ (j q))) = (k : W) ↔
      kpair.π₁ (kpair.π₂ (kpair.π₁ q)) = (k : V) := by
    rw [← j.map_first, ← j.map_second, ← j.map_first, ← j.map_numeral k, j.injective.eq_iff]
  have h0 : kpair.π₁ (kpair.π₂ (kpair.π₁ (j q))) = (0 : W) ↔
      kpair.π₁ (kpair.π₂ (kpair.π₁ q)) = (0 : V) := he 0
  have h1 : kpair.π₁ (kpair.π₂ (kpair.π₁ (j q))) = (1 : W) ↔
      kpair.π₁ (kpair.π₂ (kpair.π₁ q)) = (1 : V) := he 1
  have h2 : kpair.π₁ (kpair.π₂ (kpair.π₁ (j q))) = (2 : W) ↔
      kpair.π₁ (kpair.π₂ (kpair.π₁ q)) = (2 : V) := he 2
  have h3 : kpair.π₁ (kpair.π₂ (kpair.π₁ (j q))) = (3 : W) ↔
      kpair.π₁ (kpair.π₂ (kpair.π₁ q)) = (3 : V) := he 3
  have h4 : kpair.π₁ (kpair.π₂ (kpair.π₁ (j q))) = (4 : W) ↔
      kpair.π₁ (kpair.π₂ (kpair.π₁ q)) = (4 : V) := he 4
  have h5 : kpair.π₁ (kpair.π₂ (kpair.π₁ (j q))) = (5 : W) ↔
      kpair.π₁ (kpair.π₂ (kpair.π₁ q)) = (5 : V) := he 5
  have h6 : kpair.π₁ (kpair.π₂ (kpair.π₁ (j q))) = (6 : W) ↔
      kpair.π₁ (kpair.π₂ (kpair.π₁ q)) = (6 : V) := he 6
  dsimp only [formulaSubstitutionStep]
  rw [h0, h1, h2, h3, h4, h5, h6]
  split_ifs <;> simp only [j.map_truthCode, j.map_falsityCode, j.map_atomCode, j.map_negAtomCode,
    j.map_andCode, j.map_orCode, j.map_allCode, j.map_existsCode,
    j.map_substitutedArguments hL hn, j.map_value_total, j.map_substitutionChild, j.map_substitutionBody,
    j.map_first, j.map_second]

theorem map_formulaSubstitutionGraph {L : V} (hL : IsLanguageCode L) (Γ G : V) :
    j (formulaSubstitutionGraph L Γ G) = formulaSubstitutionGraph (j L) (j Γ) (j G) := by
  symm
  apply (formulaSubstitutionGraph_eq_iff _ _ _ _).mpr
  rw [totalRecursionAttempt_iff]
  refine ⟨j.map_function _, ?_, ?_⟩
  · rw [← j.map_domain, domain_formulaSubstitutionGraph, j.map_formulaDepthDomain hL Γ]
  · intro u hu
    rw [← j.map_formulaDepthDomain hL Γ] at hu
    obtain ⟨q, hq, rfl⟩ := j.endExtension _ u hu
    have hn : kpair.π₁ (kpair.π₁ q) ∈ (ω : V) := by
      obtain ⟨p, hp, k, _, rfl⟩ := mem_prod_iff.mp hq
      obtain ⟨n, hn, φ, rfl⟩ := formulaFamily_context hL Γ hp
      simpa only [kpair.π₁_kpair] using hn
    rw [← j.map_value_total]
    have hrec := ((formulaSubstitutionGraph_eq_iff L Γ G _).mp rfl).1.2.2 q (by simpa using hq)
    rw [hrec, j.map_formulaSubstitutionStep hL hn, j.map_restrict,
      j.map_formulaDepthPredecessors hq, j.map_formulaDepthDomain hL Γ]

theorem map_substituteFormula {L Γ Δ s : V} (hL : IsLanguageCode L) (hs : IsSubstitutionState L Γ Δ s) (φ : V) :
    j (substituteFormula L Γ Δ s φ) = substituteFormula (j L) (j Γ) (j Δ) (j s) (j φ) := by
  simp only [substituteFormula, j.map_value_total, j.map_formulaSubstitutionGraph hL,
    j.map_substitutionStates hL hs, j.map_kpair, j.map_stateSource,
    (show j (0 : V) = (0 : W) from j.map_numeral 0)]

end MembershipEndExtension
end ZFVP
