import ZFVP.ModelTheory.SchmerlInternalInfinitarySyntax
import ZFVP.Syntax.PackedSatisfaction
import ZFVP.SetTheory.CountableSets

/-! Satisfaction for an actual internal infinitary fragment. The Q clause
uses internal uncountability of its actual set of witnesses. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def witnessFiber (M n b previous φ : V) : V :=
  {x ∈ structureDomain M ; assignmentPrepend n b x ∈ previous ‘ ⟨succ n, φ⟩ₖ}

instance witnessFiber_definable : Language.DefinableFunction₅ ℒₛₑₜ (witnessFiber : V → V → V → V → V → V) := by
  have h : Language.Definable ℒₛₑₜ (fun v : Fin 6 → V ↦ ∀ x,
      x ∈ v 0 ↔ x ∈ structureDomain (v 1) ∧
        assignmentPrepend (v 2) (v 3) x ∈ (v 4) ‘ ⟨succ (v 2), v 5⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = witnessFiber (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [witnessFiber, mem_sep_iff]

attribute [local aesop 4 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

def StepHolds (L M p previous b : V) : Prop :=
  (∃ φ, kpair.π₂ p = foCode φ ∧ Satisfies L ∅ M ∅ (kpair.π₁ p) φ b) ∨
  (∃ φ, kpair.π₂ p = negCode φ ∧ b ∉ previous ‘ ⟨kpair.π₁ p, φ⟩ₖ) ∨
  (∃ f, kpair.π₂ p = conjCode f ∧ ∀ i ∈ (ω : V),
    b ∈ previous ‘ ⟨kpair.π₁ p, f ‘ i⟩ₖ) ∨
  (∃ φ, kpair.π₂ p = exsCode φ ∧ ∃ x ∈ structureDomain M,
    assignmentPrepend (kpair.π₁ p) b x ∈ previous ‘ ⟨succ (kpair.π₁ p), φ⟩ₖ) ∨
  ∃ φ, kpair.π₂ p = qCode φ ∧
    ¬IsInternallyCountable (witnessFiber M (kpair.π₁ p) b previous φ)

instance stepHolds_definable (L M : V) : ℒₛₑₜ-relation₃[V] (StepHolds L M) := by
  unfold StepHolds Satisfies
  apply Language.Definable.or
  · definability
  apply Language.Definable.or
  · definability
  apply Language.Definable.or
  · definability
  apply Language.Definable.or
  · definability
  · definability

noncomputable def truthStep (L M p previous : V) : V :=
  {b ∈ structureDomain M ^ (kpair.π₁ p) ; StepHolds L M p previous b}

@[simp] theorem mem_truthStep (L M p previous b : V) :
    b ∈ truthStep L M p previous ↔
      b ∈ structureDomain M ^ (kpair.π₁ p) ∧ StepHolds L M p previous b := by
  simp only [truthStep, mem_sep_iff]

instance truthStep_definable (L M : V) : ℒₛₑₜ-function₂[V] (truthStep L M) := by
  have h : ℒₛₑₜ-relation₃[V] (fun S p previous ↦ ∀ b,
      b ∈ S ↔ b ∈ structureDomain M ^ (kpair.π₁ p) ∧ StepHolds L M p previous b) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = truthStep L M (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_truthStep]

noncomputable def truthGraph (L F M : V) : V :=
  wellFoundedRecursion (immediateRelation_wellFounded F) (truthStep L M) inferInstance

instance truthGraph_isFunction (L F M : V) : IsFunction (truthGraph L F M) :=
  wellFoundedRecursion_isFunction _ _ _

@[simp] theorem domain_truthGraph (L F M : V) : domain (truthGraph L F M) = F :=
  domain_wellFoundedRecursion _ _ _

theorem truthGraph_value (L F M : V) {p : V} (hp : p ∈ F) :
    (truthGraph L F M) ‘ p = truthStep L M p
      ((truthGraph L F M) ↾ (predecessors (immediateRelation F) F p)) :=
  wellFoundedRecursion_value _ _ _ hp

def Holds (L F M n φ b : V) : Prop := b ∈ (truthGraph L F M) ‘ ⟨n, φ⟩ₖ

theorem holds_iff_step (L F M n φ b : V) (hφ : ⟨n, φ⟩ₖ ∈ F) :
    Holds L F M n φ b ↔ b ∈ structureDomain M ^ n ∧ StepHolds L M ⟨n, φ⟩ₖ
      ((truthGraph L F M) ↾ (predecessors (immediateRelation F) F ⟨n, φ⟩ₖ)) b := by
  unfold Holds
  rw [truthGraph_value L F M hφ, mem_truthStep, kpair.π₁_kpair]

theorem stepHolds_fo (L M n previous b φ : V) :
    StepHolds L M ⟨n, foCode φ⟩ₖ previous b ↔ Satisfies L ∅ M ∅ n φ b := by
  simp [StepHolds, foCode, negCode, conjCode, exsCode, qCode,
    OfNat.ofNat, internalNumeral_eq_iff]

theorem stepHolds_neg (L M n previous b φ : V) :
    StepHolds L M ⟨n, negCode φ⟩ₖ previous b ↔ b ∉ previous ‘ ⟨n, φ⟩ₖ := by
  simp [StepHolds, foCode, negCode, conjCode, exsCode, qCode,
    OfNat.ofNat, internalNumeral_eq_iff]

theorem stepHolds_conj (L M n previous b f : V) :
    StepHolds L M ⟨n, conjCode f⟩ₖ previous b ↔
      ∀ i ∈ (ω : V), b ∈ previous ‘ ⟨n, f ‘ i⟩ₖ := by
  simp [StepHolds, foCode, negCode, conjCode, exsCode, qCode,
    OfNat.ofNat, internalNumeral_eq_iff]

theorem stepHolds_exs (L M n previous b φ : V) :
    StepHolds L M ⟨n, exsCode φ⟩ₖ previous b ↔
      ∃ x ∈ structureDomain M, assignmentPrepend n b x ∈ previous ‘ ⟨succ n, φ⟩ₖ := by
  simp [StepHolds, foCode, negCode, conjCode, exsCode, qCode,
    OfNat.ofNat, internalNumeral_eq_iff]

theorem stepHolds_q (L M n previous b φ : V) :
    StepHolds L M ⟨n, qCode φ⟩ₖ previous b ↔
      ¬IsInternallyCountable (witnessFiber M n b previous φ) := by
  simp [StepHolds, foCode, negCode, conjCode, exsCode, qCode,
    OfNat.ofNat, internalNumeral_eq_iff]

end ZFVP.Infinitary.Internal
