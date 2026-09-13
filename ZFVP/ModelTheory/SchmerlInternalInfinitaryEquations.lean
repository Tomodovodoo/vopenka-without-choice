import ZFVP.ModelTheory.SchmerlInternalInfinitaryTruth

/-! Constructor equations and an all-parameter definability interface for
internal infinitary satisfaction. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 4 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp Language.DefinableRel₅.comp

instance stepHolds_all_definable : Language.DefinableRel₅ ℒₛₑₜ (StepHolds : V → V → V → V → V → Prop) := by
  unfold StepHolds Satisfies
  apply Language.Definable.or
  · definability
  apply Language.Definable.or
  · definability
  apply Language.Definable.or
  · definability
  apply Language.Definable.or <;> definability

def IsTruthGraph (L F M g : V) : Prop := IsFunction g ∧ domain g = F ∧
  ∀ p ∈ F, ∀ b, b ∈ g ‘ p ↔ b ∈ structureDomain M ^ (kpair.π₁ p) ∧
    StepHolds L M p (g ↾ (predecessors (immediateRelation F) F p)) b

instance isTruthGraph_definable : ℒₛₑₜ-relation₄[V] IsTruthGraph := by
  unfold IsTruthGraph
  definability

theorem truthGraph_eq_iff (L F M g : V) : truthGraph L F M = g ↔ IsTruthGraph L F M g := by
  constructor
  · rintro rfl
    refine ⟨inferInstance, domain_truthGraph _ _ _, ?_⟩
    intro p hp b
    rw [truthGraph_value L F M hp, mem_truthStep]
  · rintro ⟨hg, hd, he⟩
    apply (wellFoundedRecursion_eq_iff (immediateRelation_wellFounded F)
      (truthStep L M) inferInstance g).mpr
    rw [totalRecursionAttempt_iff]
    refine ⟨hg, hd, ?_⟩
    intro p hp
    apply mem_ext
    intro b
    rw [mem_truthStep]
    exact he p hp b

instance truthGraph_definable : ℒₛₑₜ-function₃[V] truthGraph := by
  have h : ℒₛₑₜ-relation₄[V] (fun g L F M ↦ IsTruthGraph L F M g) := by definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (truthGraph_eq_iff _ _ _ _)

instance holds_definable : Language.Definable ℒₛₑₜ
    (fun v : Fin 6 → V ↦ Holds (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := by
  unfold Holds
  definability

theorem holds_node_mem {L F M n φ b : V} (h : Holds L F M n φ b) : ⟨n, φ⟩ₖ ∈ F := by
  by_contra hn
  have hh : ⟨n, φ⟩ₖ ∉ domain (truthGraph L F M) := by simpa using hn
  unfold Holds at h
  rw [value_eq_empty_of_not_mem_domain hh] at h
  exact not_mem_empty h

theorem holds_assignment_mem {L F M n φ b : V} (h : Holds L F M n φ b) :
    b ∈ structureDomain M ^ n :=
  ((holds_iff_step L F M n φ b (holds_node_mem h)).mp h).1

theorem previous_value {L F M s t : V} (hs : s ∈ F) (ht : t ∈ F) (hst : IsImmediate s t) :
    ((truthGraph L F M) ↾ (predecessors (immediateRelation F) F t)) ‘ s =
      (truthGraph L F M) ‘ s := by
  apply value_restrict (by simpa using hs)
  exact (mem_predecessors_iff _ _ _ _).mpr
    ⟨hs, (pair_mem_immediateRelation F s t).mpr ⟨hs, ht, hst⟩⟩

theorem holds_fo {L F M n φ b : V} (hF : IsFragment L F) (hφ : ⟨n, foCode φ⟩ₖ ∈ F) :
    Holds L F M n (foCode φ) b ↔ Satisfies L ∅ M ∅ n φ b := by
  have hm : φ ∈ formulaSet L ∅ n := by
    have hn := (hF.node hφ).2
    simpa [foCode, negCode, conjCode, exsCode, qCode, OfNat.ofNat, internalNumeral_eq_iff] using hn
  rw [holds_iff_step L F M n (foCode φ) b hφ, stepHolds_fo]
  exact and_iff_right_of_imp (satisfies_assignment_mem hm)

theorem holds_neg {L F M n φ b : V} (hF : IsFragment L F) (hφ : ⟨n, negCode φ⟩ₖ ∈ F)
    (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n (negCode φ) b ↔ ¬Holds L F M n φ b := by
  have hs : ⟨n, φ⟩ₖ ∈ F := by
    have hn := (hF.node hφ).2
    simpa [foCode, negCode, conjCode, exsCode, qCode, OfNat.ofNat, internalNumeral_eq_iff] using hn
  rw [holds_iff_step L F M n (negCode φ) b hφ, stepHolds_neg,
    previous_value hs hφ ((immediate_neg_iff _ _ _).mpr rfl)]
  exact and_iff_right hb

theorem holds_conj {L F M n f b : V} (hF : IsFragment L F) (hφ : ⟨n, conjCode f⟩ₖ ∈ F)
    (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n (conjCode f) b ↔ ∀ i ∈ (ω : V), Holds L F M n (f ‘ i) b := by
  have hn : IsFunction f ∧ domain f = (ω : V) ∧ ∀ i ∈ (ω : V), ⟨n, f ‘ i⟩ₖ ∈ F := by
    have hc := (hF.node hφ).2
    simpa [foCode, negCode, conjCode, exsCode, qCode, OfNat.ofNat, internalNumeral_eq_iff] using hc
  rw [holds_iff_step L F M n (conjCode f) b hφ, stepHolds_conj, and_iff_right hb]
  apply forall₂_congr
  intro i hi
  rw [previous_value (hn.2.2 i hi) hφ
    ((immediate_conj_iff _ _ _).mpr ⟨hn.1, i, hn.2.1.symm ▸ hi, rfl⟩)]
  rfl

theorem holds_exs {L F M n φ b : V} (hF : IsFragment L F) (hφ : ⟨n, exsCode φ⟩ₖ ∈ F)
    (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n (exsCode φ) b ↔
      ∃ x ∈ structureDomain M, Holds L F M (succ n) φ (assignmentPrepend n b x) := by
  have hs : ⟨succ n, φ⟩ₖ ∈ F := by
    have hn := (hF.node hφ).2
    simpa [foCode, negCode, conjCode, exsCode, qCode, OfNat.ofNat, internalNumeral_eq_iff] using hn
  rw [holds_iff_step L F M n (exsCode φ) b hφ, stepHolds_exs, and_iff_right hb,
    previous_value hs hφ ((immediate_exs_iff _ _ _).mpr rfl)]
  rfl

theorem holds_q {L F M n φ b : V} (hF : IsFragment L F) (hφ : ⟨n, qCode φ⟩ₖ ∈ F)
    (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n (qCode φ) b ↔
      ¬IsInternallyCountable (witnessFiber M n b (truthGraph L F M) φ) := by
  have hs : ⟨succ n, φ⟩ₖ ∈ F := by
    have hn := (hF.node hφ).2
    simpa [foCode, negCode, conjCode, exsCode, qCode, OfNat.ofNat, internalNumeral_eq_iff] using hn
  rw [holds_iff_step L F M n (qCode φ) b hφ, stepHolds_q, and_iff_right hb]
  have he : witnessFiber M n b ((truthGraph L F M) ↾
      (predecessors (immediateRelation F) F ⟨n, qCode φ⟩ₖ)) φ =
      witnessFiber M n b (truthGraph L F M) φ := by
    apply mem_ext
    intro x
    simp only [witnessFiber, mem_sep_iff,
      previous_value hs hφ ((immediate_q_iff _ _ _).mpr rfl)]
  rw [he]

end ZFVP.Infinitary.Internal
