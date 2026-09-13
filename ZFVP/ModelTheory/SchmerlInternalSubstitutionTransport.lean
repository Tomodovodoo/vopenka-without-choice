import ZFVP.Syntax.EndExtensionFormulaSubstitution
import ZFVP.SetTheory.EndExtensionReplacement
import ZFVP.ModelTheory.SchmerlInternalInfinitaryTransport
import ZFVP.ModelTheory.SchmerlInternalSwap

/-! Membership end extensions preserve the actual internal substitution
graphs and image fragments. Recursion uniqueness transports all internal
depths; no external induction on the model's natural numbers is used. -/

namespace ZFVP.Infinitary.Internal.EndExtension
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

theorem map_depthDomain (F : V) : j (depthDomain F) = depthDomain (j F) := by
  simp only [depthDomain, j.map_prod, j.map_omega]

theorem map_depthPredecessors {L F q : V} (hF : IsFragment L F) (hq : q ∈ depthDomain F) :
    j (predecessors (depthRelation (depthDomain F)) (depthDomain F) q) =
      predecessors (depthRelation (depthDomain (j F))) (depthDomain (j F)) (j q) := by
  have he (D t : W) (ht : t ∈ D) : predecessors (depthRelation D) D t =
      {p ∈ D ; IsImmediate (kpair.π₁ p) (kpair.π₁ t)} := by
    ext p
    simp only [mem_predecessors_iff, pair_mem_depthRelation, ht, mem_sep_iff]
    tauto
  have hv : predecessors (depthRelation (depthDomain F)) (depthDomain F) q =
      {p ∈ depthDomain F ; IsImmediate (kpair.π₁ p) (kpair.π₁ q)} := by
    ext p
    simp only [mem_predecessors_iff, pair_mem_depthRelation, hq, mem_sep_iff]
    tauto
  rw [hv, he _ _ (by rw [← map_depthDomain]; exact (j.mem_iff _ _).mpr hq), ← map_depthDomain]
  apply j.map_separation
  intro p _
  rw [← j.map_first, ← j.map_first]
  obtain ⟨t, ht, k, _, rfl⟩ := mem_prod_iff.mp hq
  simp only [kpair.π₁_kpair]
  have htcode := (hF.2 t ht).1
  conv_rhs => rw [htcode]
  conv_lhs => rw [htcode]
  exact (immediate_iff j (hF.2 t ht).2 _).symm

theorem map_transformConjunction (q previous f : V) :
    j (transformConjunction q previous f) = transformConjunction (j q) (j previous) (j f) := by
  have h := j.map_definableGraph (ω : V)
    (fun i ↦ previous ‘ (substitutionChild q (f ‘ i)))
    (fun i ↦ (j previous) ‘ (substitutionChild (j q) ((j f) ‘ i)))
    (by definability) (by definability) (fun i _ ↦ by
      rw [j.map_value_total, j.map_substitutionChild, j.map_value_total])
  simpa only [transformConjunction, j.map_omega] using h

theorem map_infinitarySubstitutionStep {L : V} (hL : IsLanguageCode L) (G q previous : V) :
    j (infinitarySubstitutionStep L G q previous) =
      infinitarySubstitutionStep (j L) (j G) (j q) (j previous) := by
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
  dsimp only [infinitarySubstitutionStep]
  rw [h0, h1, h2, h3]
  split_ifs <;> simp only [map_foCode, map_negCode, map_conjCode, map_exsCode, map_qCode,
    j.map_value_total, j.map_formulaSubstitutionGraph hL, j.map_empty, j.map_kpair,
    j.map_first, j.map_second, j.map_substitutionChild, j.map_substitutionBody, map_transformConjunction]

theorem map_infinitarySubstitutionGraph {L F : V} (hF : IsFragment L F) (G : V) :
    j (infinitarySubstitutionGraph L F G) = infinitarySubstitutionGraph (j L) (j F) (j G) := by
  symm
  apply (wellFoundedRecursion_eq_iff (depthRelation_wellFounded (depthDomain (j F)))
    (infinitarySubstitutionStep (j L) (j G)) (by definability) _).mpr
  rw [totalRecursionAttempt_iff]
  refine ⟨j.map_function _, ?_, ?_⟩
  · rw [← j.map_domain, domain_infinitarySubstitutionGraph, map_depthDomain]
  · intro u hu
    rw [← map_depthDomain] at hu
    obtain ⟨q, hq, rfl⟩ := j.endExtension _ u hu
    rw [← j.map_value_total]
    change j ((depthRecursion F _ _) ‘ q) = _
    rw [depthRecursion_value F _ _ hq, map_infinitarySubstitutionStep j hF.1,
      j.map_restrict, map_depthPredecessors j hF hq]
    rfl

theorem map_substitutionDepths (F G : V) :
    j (substitutionDepths F G) = substitutionDepths (j F) (j G) := by
  unfold substitutionDepths
  rw [← map_depthDomain]
  apply j.map_separation
  intro q _
  rw [← j.map_first, ← j.map_first, ← j.map_second, ← j.map_value_total,
    ← j.map_stateSource, j.injective.eq_iff]

theorem map_substitutedNode {L F : V} (hF : IsFragment L F) (G q : V) :
    j (substitutedNode L F G q) = substitutedNode (j L) (j F) (j G) (j q) := by
  simp only [substitutedNode, j.map_kpair, j.map_stateTarget, j.map_value_total,
    j.map_second, map_infinitarySubstitutionGraph j hF]

theorem map_substitutedFragment {L F : V} (hF : IsFragment L F) (G : V) :
    j (substitutedFragment L F G) = substitutedFragment (j L) (j F) (j G) := by
  unfold substitutedFragment
  rw [← map_substitutionDepths]
  exact j.map_repl _ _ _ (by definability) (by definability)
    (fun q _ ↦ map_substitutedNode j hF G q)

theorem map_substituteCode {L F s : V} (hF : IsFragment L F)
    (hs : IsSubstitutionState L ∅ ∅ s) (φ : V) :
    j (substituteCode L F s φ) = substituteCode (j L) (j F) (j s) (j φ) := by
  simp only [substituteCode, j.map_value_total, map_infinitarySubstitutionGraph j hF,
    j.map_substitutionStates hF.1 hs, j.map_empty, j.map_kpair, j.map_stateSource,
    (show j (0 : V) = (0 : W) from j.map_numeral 0)]

theorem map_substitutionFragment {L F s : V} (hF : IsFragment L F)
    (hs : IsSubstitutionState L ∅ ∅ s) :
    j (substitutionFragment L F s) = substitutionFragment (j L) (j F) (j s) := by
  simp only [substitutionFragment, map_substitutedFragment j hF,
    j.map_substitutionStates hF.1 hs, j.map_empty]

theorem map_renamingState (n m r : V) :
    j (renamingState n m r) = renamingState (j n) (j m) (j r) := by
  simp only [renamingState, j.map_substitutionState, j.map_compose,
    j.map_boundVariableAssignment, j.map_empty]

theorem map_renameCode {L F n m r : V} (hF : IsFragment L F)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n) (φ : V) :
    j (renameCode L F n m r φ) = renameCode (j L) (j F) (j n) (j m) (j r) (j φ) := by
  rw [renameCode, map_substituteCode j hF (renamingState_valid hF.1 hn hm hr), map_renamingState]
  rfl

theorem map_renamedFragment {L F n m r : V} (hF : IsFragment L F)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n) :
    j (renamedFragment L F n m r) = renamedFragment (j L) (j F) (j n) (j m) (j r) := by
  rw [renamedFragment, map_substitutionFragment j hF (renamingState_valid hF.1 hn hm hr), map_renamingState]
  rfl

theorem map_swapCode {L F n : V} (hF : IsFragment L F) (hn : n ∈ (ω : V)) (φ : V) :
    j (swapCode L F n φ) = swapCode (j L) (j F) (j n) (j φ) := by
  rw [swapCode, map_renameCode j hF (ω_succ_closed (ω_succ_closed hn))
    (ω_succ_closed (ω_succ_closed hn)) (swapFirstTwoIndices_mem hn),
    j.map_succ, j.map_succ, j.map_swapFirstTwoIndices]
  rfl

theorem map_swapFragment {L F n : V} (hF : IsFragment L F) (hn : n ∈ (ω : V)) :
    j (swapFragment L F n) = swapFragment (j L) (j F) (j n) := by
  rw [swapFragment, map_renamedFragment j hF (ω_succ_closed (ω_succ_closed hn))
    (ω_succ_closed (ω_succ_closed hn)) (swapFirstTwoIndices_mem hn),
    j.map_succ, j.map_succ, j.map_swapFirstTwoIndices]
  rfl

end ZFVP.Infinitary.Internal.EndExtension
