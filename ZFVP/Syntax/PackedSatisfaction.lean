import ZFVP.Syntax.SatisfactionDefinability

/-! Packing the four satisfaction parameters gives short definability interfaces. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def satisfactionParameters (L Γ M e : V) : V := ⟨⟨L, Γ⟩ₖ, ⟨M, e⟩ₖ⟩ₖ

noncomputable def satLanguage (P : V) : V := kpair.π₁ (kpair.π₁ P)
instance satLanguage_definable : ℒₛₑₜ-function₁[V] satLanguage := by
  unfold satLanguage
  definability

noncomputable def satVariables (P : V) : V := kpair.π₂ (kpair.π₁ P)
instance satVariables_definable : ℒₛₑₜ-function₁[V] satVariables := by
  unfold satVariables
  definability

noncomputable def satStructure (P : V) : V := kpair.π₁ (kpair.π₂ P)
instance satStructure_definable : ℒₛₑₜ-function₁[V] satStructure := by
  unfold satStructure
  definability

noncomputable def satFreeAssignment (P : V) : V := kpair.π₂ (kpair.π₂ P)
instance satFreeAssignment_definable : ℒₛₑₜ-function₁[V] satFreeAssignment := by
  unfold satFreeAssignment
  definability

noncomputable def packedTermEvaluation (P n b : V) : V :=
  termEvaluation (satLanguage P) (satVariables P) n (satStructure P) b (satFreeAssignment P)

instance packedTermEvaluation_definable : ℒₛₑₜ-function₃[V] packedTermEvaluation := by
  unfold packedTermEvaluation
  exact termEvaluation_comp (by definability) (by definability) (by definability)
    (by definability) (by definability) (by definability)

noncomputable def packedEvaluatedArguments (P q args : V) : V :=
  compose args (packedTermEvaluation P (kpair.π₁ q) (kpair.π₂ q))

instance packedEvaluatedArguments_definable : ℒₛₑₜ-function₃[V] packedEvaluatedArguments := by
  unfold packedEvaluatedArguments
  definability

def PackedAtomicHolds (P q a : V) : Prop :=
  (kpair.π₁ a = equalityToken ∧ (packedEvaluatedArguments P q (kpair.π₂ a)) ‘ (0 : V) =
    (packedEvaluatedArguments P q (kpair.π₂ a)) ‘ (1 : V)) ∨
  ∃ s ∈ relationSymbols (satLanguage P), kpair.π₁ a = relationToken s ∧
    packedEvaluatedArguments P q (kpair.π₂ a) ∈ (structureRelations (satStructure P)) ‘ s

instance packedAtomicHolds_definable : ℒₛₑₜ-relation₃[V] PackedAtomicHolds := by
  unfold PackedAtomicHolds equalityToken
  definability

theorem packedAtomicHolds_iff (P n b r args : V) :
    PackedAtomicHolds P ⟨n, b⟩ₖ ⟨r, args⟩ₖ ↔
      AtomicHolds (satLanguage P) (satVariables P) (satStructure P) (satFreeAssignment P) n b r args := by
  simp only [PackedAtomicHolds, packedEvaluatedArguments, packedTermEvaluation,
    AtomicHolds, evaluatedArguments, evaluateWithFreeAssignment, kpair.π₁_kpair, kpair.π₂_kpair]

def PackedSatisfactionStepHolds (P p previous b : V) : Prop :=
  kpair.π₂ p = truthCode ∨
  (∃ r args, kpair.π₂ p = atomCode r args ∧ PackedAtomicHolds P ⟨kpair.π₁ p, b⟩ₖ ⟨r, args⟩ₖ) ∨
  (∃ r args, kpair.π₂ p = negAtomCode r args ∧ ¬PackedAtomicHolds P ⟨kpair.π₁ p, b⟩ₖ ⟨r, args⟩ₖ) ∨
  (∃ φ ψ, kpair.π₂ p = andCode φ ψ ∧
    b ∈ previous ‘ ⟨kpair.π₁ p, φ⟩ₖ ∧ b ∈ previous ‘ ⟨kpair.π₁ p, ψ⟩ₖ) ∨
  (∃ φ ψ, kpair.π₂ p = orCode φ ψ ∧
    (b ∈ previous ‘ ⟨kpair.π₁ p, φ⟩ₖ ∨ b ∈ previous ‘ ⟨kpair.π₁ p, ψ⟩ₖ)) ∨
  (∃ φ, kpair.π₂ p = allCode φ ∧ ∀ x ∈ structureDomain (satStructure P),
    assignmentPrepend (kpair.π₁ p) b x ∈ previous ‘ ⟨succ (kpair.π₁ p), φ⟩ₖ) ∨
  ∃ φ, kpair.π₂ p = existsCode φ ∧ ∃ x ∈ structureDomain (satStructure P),
    assignmentPrepend (kpair.π₁ p) b x ∈ previous ‘ ⟨succ (kpair.π₁ p), φ⟩ₖ

instance packedSatisfactionStepHolds_definable : ℒₛₑₜ-relation₄[V] PackedSatisfactionStepHolds := by
  unfold PackedSatisfactionStepHolds truthCode
  definability

theorem packedSatisfactionStepHolds_iff (P p previous b : V) :
    PackedSatisfactionStepHolds P p previous b ↔
      SatisfactionStepHolds (satLanguage P) (satVariables P) (satStructure P) (satFreeAssignment P)
        p previous b := by
  simp only [PackedSatisfactionStepHolds, SatisfactionStepHolds, packedAtomicHolds_iff]

def IsPackedSatisfactionGraph (P g : V) : Prop :=
  IsFunction g ∧ domain g = formulaFamily (satLanguage P) (satVariables P) ∧
  ∀ p ∈ formulaFamily (satLanguage P) (satVariables P), ∀ b, b ∈ g ‘ p ↔
    b ∈ structureDomain (satStructure P) ^ (kpair.π₁ p) ∧
    PackedSatisfactionStepHolds P p (g ↾
      (predecessors (subformulaRelation (formulaFamily (satLanguage P) (satVariables P)))
        (formulaFamily (satLanguage P) (satVariables P)) p)) b

instance isPackedSatisfactionGraph_definable : ℒₛₑₜ-relation[V] IsPackedSatisfactionGraph := by
  unfold IsPackedSatisfactionGraph
  definability

theorem isPackedSatisfactionGraph_iff (P g : V) : IsPackedSatisfactionGraph P g ↔
    IsSatisfactionGraph (satLanguage P) (satVariables P) (satStructure P) (satFreeAssignment P) g := by
  simp only [IsPackedSatisfactionGraph, IsSatisfactionGraph, packedSatisfactionStepHolds_iff]

noncomputable def packedSatisfactionGraph (P : V) : V :=
  satisfactionGraph (satLanguage P) (satVariables P) (satStructure P) (satFreeAssignment P)

instance packedSatisfactionGraph_definable : ℒₛₑₜ-function₁[V] packedSatisfactionGraph := by
  have h : ℒₛₑₜ-relation (fun g P : V ↦ IsPackedSatisfactionGraph P g) := by definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans ((satisfactionGraph_eq_iff _ _ _ _ _).trans (isPackedSatisfactionGraph_iff _ _).symm)

instance satisfactionGraph_definable : ℒₛₑₜ-function₄[V] satisfactionGraph := by
  have h : Language.DefinableFunction ℒₛₑₜ (fun v : Fin 4 → V ↦
      packedSatisfactionGraph ⟨⟨v 0, v 1⟩ₖ, ⟨v 2, v 3⟩ₖ⟩ₖ) := by definability
  simpa only [packedSatisfactionGraph, satLanguage, satVariables, satStructure, satFreeAssignment,
    kpair.π₁_kpair, kpair.π₂_kpair] using h

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

instance isSatisfactionGraph_definable : ℒₛₑₜ-relation₅[V] IsSatisfactionGraph := by
  have h : ℒₛₑₜ-relation₅ (fun L Γ M e g : V ↦ satisfactionGraph L Γ M e = g) := by definability
  apply Language.Definable.of_iff h
  intro v
  exact (satisfactionGraph_eq_iff _ _ _ _ _).symm

instance satisfies_definable : Language.Definable ℒₛₑₜ (fun v : Fin 7 → V ↦
    Satisfies (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := by
  unfold Satisfies
  definability

end ZFVP
