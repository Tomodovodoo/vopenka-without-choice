import ZFVP.ModelTheory.SchmerlInternalInfinitarySubstitutionValidity

/-! Substitution preserves internal infinitary truth, with Q interpreted by
the model's own countability predicate. No external countability is used. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def substitutedAssignment (L M G k b : V) : V :=
  compose (stateBound (G ‘ k)) (substitutionTargetEvaluation L ∅ M ∅ G k b)

instance substitutedAssignment_definable (L M G : V) :
    ℒₛₑₜ-function₂ (substitutedAssignment L M G) := by
  unfold substitutedAssignment
  definability

theorem substitutedAssignment_mem {L M G k b : V} (hM : IsStructureCode L M)
    (hs : IsSubstitutionState L ∅ ∅ (G ‘ k)) (hb : b ∈ structureDomain M ^ stateTarget (G ‘ k)) :
    substitutedAssignment L M G k b ∈ structureDomain M ^ stateSource (G ‘ k) := by
  exact compose_function hs.2.2.1
    (termEvaluation_mem_function hM hs.2.1 ∅ hb (mem_function.intro (by simp) (by simp)))

theorem substitutedAssignment_prepend {L M G k b x : V} (hM : IsStructureCode L M)
    (hs : IsSubstitutionState L ∅ ∅ (G ‘ k))
    (hstep : G ‘ (succ k) = liftSubstitutionState L ∅ (G ‘ k))
    (hb : b ∈ structureDomain M ^ stateTarget (G ‘ k)) (hx : x ∈ structureDomain M) :
    substitutedAssignment L M G (succ k) (assignmentPrepend (stateTarget (G ‘ k)) b x) =
      assignmentPrepend (stateSource (G ‘ k)) (substitutedAssignment L M G k b) x := by
  unfold substitutedAssignment substitutionTargetEvaluation evaluateWithFreeAssignment
  simp only [hstep, liftSubstitutionState, stateBound_code, stateTarget_code]
  exact evaluate_liftBoundReplacement hM hs.1 hs.2.1 hs.2.2.1 hb
    (mem_function.intro (by simp) (by simp)) hx

set_option maxHeartbeats 1000000 in
theorem holds_substitutionGraph {L F G M : V} (hF : IsFragment L F) (hM : IsStructureCode L M)
    (hG : ∀ k ∈ (ω : V), IsSubstitutionState L ∅ ∅ (G ‘ k))
    (hstep : ∀ k ∈ (ω : V), G ‘ (succ k) = liftSubstitutionState L ∅ (G ‘ k)) :
    ∀ n φ, ⟨n, φ⟩ₖ ∈ F → ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
      ∀ b ∈ structureDomain M ^ stateTarget (G ‘ k),
        Holds L (substitutedFragment L F G) M (stateTarget (G ‘ k))
          ((infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ) b ↔
        Holds L F M n φ (substitutedAssignment L M G k b) := by
  have hsource : ∀ k ∈ (ω : V), stateSource (G ‘ (succ k)) = succ (stateSource (G ‘ k)) := by
    intro k hk; simp [hstep k hk, liftSubstitutionState]
  have htarget : ∀ k ∈ (ω : V), stateTarget (G ‘ (succ k)) = succ (stateTarget (G ‘ k)) := by
    intro k hk; simp [hstep k hk, liftSubstitutionState]
  have hv := substitutedFragment_valid hF hG hsource htarget
  have hbsource {n k b : V} (hk : k ∈ (ω : V)) (hc : n = stateSource (G ‘ k))
      (hb : b ∈ structureDomain M ^ stateTarget (G ‘ k)) :
      substitutedAssignment L M G k b ∈ structureDomain M ^ n :=
    hc.symm ▸ substitutedAssignment_mem hM (hG k hk) hb
  apply fragment_induction hF (fun n φ ↦ ∀ k ∈ (ω : V), n = stateSource (G ‘ k) →
    ∀ b ∈ structureDomain M ^ stateTarget (G ‘ k),
      Holds L (substitutedFragment L F G) M (stateTarget (G ‘ k))
        ((infinitarySubstitutionGraph L F G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ) b ↔
      Holds L F M n φ (substitutedAssignment L M G k b)) (by unfold Holds; definability)
  · intro n φ ht hφ k hk hc b hb
    have hnode := substitutedNode_mem (L := L) ht hk hc
    rw [infinitarySubstitutionGraph_fo ht hk] at hnode ⊢
    rw [holds_fo hv hnode, holds_fo hF ht]
    have he : (∅ : V) ∈ structureDomain M ^ (∅ : V) := mem_function.intro (by simp) (by simp)
    have hT := termEvaluation_mem_function hM (hG k hk).2.1 ∅ hb he
    have hE : compose (stateFree (G ‘ k)) (substitutionTargetEvaluation L ∅ M ∅ G k b) = (∅ : V) := by
      apply subset_empty_iff_eq_empty.mp
      simpa [substitutionTargetEvaluation, evaluateWithFreeAssignment] using
        subset_prod_of_mem_function (compose_function (hG k hk).2.2.2 hT)
    have h := satisfies_substitutionGraph hM he hG hstep n φ hφ k hk hc b hb
    rw [hE] at h
    exact h
  · intro n φ ht _ ih k hk hc b hb
    have hnode := substitutedNode_mem (L := L) ht hk hc
    rw [infinitarySubstitutionGraph_neg hF ht hk] at hnode ⊢
    rw [holds_neg hv hnode hb, holds_neg hF ht (hbsource hk hc hb)]
    exact not_congr (ih k hk hc b hb)
  · intro n f ht _ _ _ ih k hk hc b hb
    have hnode := substitutedNode_mem (L := L) ht hk hc
    rw [infinitarySubstitutionGraph_conj hF ht hk] at hnode ⊢
    rw [holds_conj hv hnode hb, holds_conj hF ht (hbsource hk hc hb)]
    apply forall₂_congr
    intro i hi
    rw [value_transformConjunction _ _ _ hi]
    simpa only [substitutionChild, kpair.π₁_kpair, kpair.π₂_kpair] using ih i hi k hk hc b hb
  · intro n φ ht _ ih k hk hc b hb
    have hnode := substitutedNode_mem (L := L) ht hk hc
    rw [infinitarySubstitutionGraph_exs hF ht hk] at hnode ⊢
    rw [holds_exs hv hnode hb, holds_exs hF ht (hbsource hk hc hb)]
    apply exists_congr
    intro x
    apply and_congr_right
    intro hx
    have hc' : succ n = stateSource (G ‘ (succ k)) := by rw [hsource k hk, hc]
    have hb' : assignmentPrepend (stateTarget (G ‘ k)) b x ∈ structureDomain M ^ stateTarget (G ‘ (succ k)) := by
      rw [htarget k hk]
      exact assignmentPrepend_mem_function (hG k hk).2.1 hb hx
    have h := ih (succ k) (ω_succ_closed hk) hc' _ hb'
    rw [htarget k hk, substitutedAssignment_prepend hM (hG k hk) (hstep k hk) hb hx] at h
    simpa only [hc] using h
  · intro n φ ht _ ih k hk hc b hb
    have hnode := substitutedNode_mem (L := L) ht hk hc
    rw [infinitarySubstitutionGraph_q hF ht hk] at hnode ⊢
    rw [holds_q hv hnode hb, holds_q hF ht (hbsource hk hc hb)]
    have he : witnessFiber M (stateTarget (G ‘ k)) b (truthGraph L (substitutedFragment L F G) M)
        ((infinitarySubstitutionGraph L F G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ) =
        witnessFiber M n (substitutedAssignment L M G k b) (truthGraph L F M) φ := by
      apply mem_ext
      intro x
      simp only [witnessFiber, mem_sep_iff]
      apply and_congr_right
      intro hx
      have hc' : succ n = stateSource (G ‘ (succ k)) := by rw [hsource k hk, hc]
      have hb' : assignmentPrepend (stateTarget (G ‘ k)) b x ∈ structureDomain M ^ stateTarget (G ‘ (succ k)) := by
        rw [htarget k hk]
        exact assignmentPrepend_mem_function (hG k hk).2.1 hb hx
      have h := ih (succ k) (ω_succ_closed hk) hc' _ hb'
      rw [htarget k hk, substitutedAssignment_prepend hM (hG k hk) (hstep k hk) hb hx] at h
      simpa only [Holds, hc] using h
    rw [he]

end ZFVP.Infinitary.Internal
