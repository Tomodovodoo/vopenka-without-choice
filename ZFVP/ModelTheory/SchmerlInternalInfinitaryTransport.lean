import ZFVP.ModelTheory.SchmerlInternalInfinitaryTruth
import ZFVP.ModelTheory.SchmerlInternalQAbsoluteness

/-! Old internally coded infinitary models retain their full truth graph
under an omega-one-preserving membership end extension. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace EndExtension

variable (j : MembershipEndExtension V W)

@[simp] theorem map_foCode (φ : V) : j (foCode φ) = foCode (j φ) := by
  rw [foCode, j.map_kpair, foCode]
  exact congrArg (fun c ↦ ⟨c, j φ⟩ₖ) (j.map_numeral 0)
@[simp] theorem map_negCode (φ : V) : j (negCode φ) = negCode (j φ) := by
  rw [negCode, j.map_kpair, negCode]
  exact congrArg (fun c ↦ ⟨c, j φ⟩ₖ) (j.map_numeral 1)
@[simp] theorem map_conjCode (f : V) : j (conjCode f) = conjCode (j f) := by
  rw [conjCode, j.map_kpair, conjCode]
  exact congrArg (fun c ↦ ⟨c, j f⟩ₖ) (j.map_numeral 2)
@[simp] theorem map_exsCode (φ : V) : j (exsCode φ) = exsCode (j φ) := by
  rw [exsCode, j.map_kpair, exsCode]
  exact congrArg (fun c ↦ ⟨c, j φ⟩ₖ) (j.map_numeral 3)
@[simp] theorem map_qCode (φ : V) : j (qCode φ) = qCode (j φ) := by
  rw [qCode, j.map_kpair, qCode]
  exact congrArg (fun c ↦ ⟨c, j φ⟩ₖ) (j.map_numeral 4)

theorem immediate_iff {L F n φ : V} (hφ : IsNode L F n φ) (s : V) :
    IsImmediate (j s) (j ⟨n, φ⟩ₖ) ↔ IsImmediate s ⟨n, φ⟩ₖ := by
  rw [j.map_kpair]
  rcases hφ.2 with ⟨ψ, _, rfl⟩ | ⟨ψ, rfl, _⟩ | ⟨f, hf, _, rfl, _⟩ |
    ⟨ψ, rfl, _⟩ | ⟨ψ, rfl, _⟩
  · simp only [map_foCode, immediate_fo_iff]
  · rw [map_negCode, immediate_neg_iff, immediate_neg_iff, ← j.map_kpair, j.injective.eq_iff]
  · let := hf
    have hjf := j.map_function f
    rw [map_conjCode, immediate_conj_iff, immediate_conj_iff]
    simp only [hf, hjf, true_and, ← j.map_domain f, j.exists_mem_iff,
      ← j.map_value_total, ← j.map_kpair, j.injective.eq_iff]
  · rw [map_exsCode, immediate_exs_iff, immediate_exs_iff,
      ← j.map_succ, ← j.map_kpair, j.injective.eq_iff]
  · rw [map_qCode, immediate_q_iff, immediate_q_iff,
      ← j.map_succ, ← j.map_kpair, j.injective.eq_iff]

theorem predecessor_eq {F p : V} (hp : p ∈ F) :
    predecessors (immediateRelation F) F p = {s ∈ F ; IsImmediate s p} := by
  apply mem_ext
  intro s
  simp only [mem_predecessors_iff, pair_mem_immediateRelation, mem_sep_iff, hp]
  tauto

theorem map_predecessors {L F p : V} (hF : IsFragment L F) (hp : p ∈ F) :
    j (predecessors (immediateRelation F) F p) =
      predecessors (immediateRelation (j F)) (j F) (j p) := by
  have hp' := (j.mem_iff p F).mpr hp
  rw [predecessor_eq hp, predecessor_eq hp']
  apply j.map_separation F (fun s ↦ IsImmediate s p) (fun s ↦ IsImmediate s (j p))
    (by definability) (by definability)
  intro s _
  have he := (hF.2 p hp).1
  have hn := (hF.2 p hp).2
  conv_rhs => rw [he]
  conv_lhs => rw [he]
  exact (immediate_iff j hn s).symm

theorem map_witnessFiber (M n b previous φ : V) :
    j (witnessFiber M n b previous φ) =
      witnessFiber (j M) (j n) (j b) (j previous) (j φ) := by
  have he := j.map_separation (structureDomain M)
    (fun x ↦ assignmentPrepend n b x ∈ previous ‘ ⟨succ n, φ⟩ₖ)
    (fun x ↦ assignmentPrepend (j n) (j b) x ∈ (j previous) ‘ ⟨succ (j n), j φ⟩ₖ)
    (by definability) (by definability) (by
      intro x _
      simp only [← j.map_assignmentPrepend, ← j.map_succ, ← j.map_kpair,
        ← j.map_value_total, j.mem_iff])
  simpa only [witnessFiber, j.map_structureDomain] using he

theorem stepHolds_iff (hAC : InternalChoice V)
    (hω₁ : j (hartogsNumber (ω : V)) = hartogsNumber (ω : W))
    {L F n φ : V} (hL : IsLanguageCode L) (hφ : IsNode L F n φ)
    (M previous b : V) :
    StepHolds (j L) (j M) (j ⟨n, φ⟩ₖ) (j previous) (j b) ↔
      StepHolds L M ⟨n, φ⟩ₖ previous b := by
  rw [j.map_kpair]
  rcases hφ.2 with ⟨ψ, _, rfl⟩ | ⟨ψ, rfl, _⟩ | ⟨f, _, _, rfl, _⟩ |
    ⟨ψ, rfl, _⟩ | ⟨ψ, rfl, _⟩
  · rw [map_foCode, stepHolds_fo, stepHolds_fo, ← j.map_empty]
    exact j.satisfies_iff hL ∅ M ∅ n ψ b
  · rw [map_negCode, stepHolds_neg, stepHolds_neg]
    simp only [← j.map_kpair, ← j.map_value_total, j.mem_iff]
  · rw [map_conjCode, stepHolds_conj, stepHolds_conj, ← j.map_omega, j.forall_mem_iff]
    simp only [← j.map_value_total, ← j.map_kpair, j.mem_iff]
  · rw [map_exsCode, stepHolds_exs, stepHolds_exs,
      ← j.map_structureDomain, j.exists_mem_iff]
    simp only [← j.map_assignmentPrepend, ← j.map_succ, ← j.map_kpair,
      ← j.map_value_total, j.mem_iff]
  · rw [map_qCode, stepHolds_q, stepHolds_q, ← map_witnessFiber]
    exact not_congr (j.internallyCountable_iff_of_omegaOne hAC hω₁ _)

theorem map_truthStep (hAC : InternalChoice V)
    (hω₁ : j (hartogsNumber (ω : V)) = hartogsNumber (ω : W))
    {L F p : V} (hF : IsFragment L F) (hp : p ∈ F) (M previous : V) :
    j (truthStep L M p previous) = truthStep (j L) (j M) (j p) (j previous) := by
  have he := (hF.2 p hp).1
  have hn := (hF.2 p hp).2
  generalize hnp : kpair.π₁ p = n at he hn
  generalize hφp : kpair.π₂ p = φ at he hn
  subst p
  have hm := j.map_separation (structureDomain M ^ n)
    (fun b ↦ StepHolds L M ⟨n, φ⟩ₖ previous b)
    (fun b ↦ StepHolds (j L) (j M) (j ⟨n, φ⟩ₖ) (j previous) b)
    (by definability) (by definability) (fun b _ ↦ (stepHolds_iff j hAC hω₁ hF.1 hn M previous b).symm)
  simpa only [truthStep, j.map_kpair, kpair.π₁_kpair,
    j.map_finiteFunctionSet _ hn.1, j.map_structureDomain] using hm

theorem map_truthGraph (hAC : InternalChoice V)
    (hω₁ : j (hartogsNumber (ω : V)) = hartogsNumber (ω : W))
    {L F : V} (hF : IsFragment L F) (M : V) :
    j (truthGraph L F M) = truthGraph (j L) (j F) (j M) := by
  symm
  apply (wellFoundedRecursion_eq_iff (immediateRelation_wellFounded (j F))
    (truthStep (j L) (j M)) inferInstance _).mpr
  rw [totalRecursionAttempt_iff]
  refine ⟨j.map_function _, ?_, ?_⟩
  · rw [← j.map_domain, domain_truthGraph]
  · intro u hu
    obtain ⟨p, hp, rfl⟩ := j.endExtension F u hu
    rw [← j.map_value_total, truthGraph_value L F M hp,
      map_truthStep j hAC hω₁ hF hp, j.map_restrict, map_predecessors j hF hp]

theorem holds_iff (hAC : InternalChoice V)
    (hω₁ : j (hartogsNumber (ω : V)) = hartogsNumber (ω : W))
    {L F : V} (hF : IsFragment L F) (M n φ b : V) :
    Holds (j L) (j F) (j M) (j n) (j φ) (j b) ↔ Holds L F M n φ b := by
  unfold Holds
  rw [← map_truthGraph j hAC hω₁ hF M, ← j.map_kpair, ← j.map_value_total, j.mem_iff]

end EndExtension
end ZFVP.Infinitary.Internal
