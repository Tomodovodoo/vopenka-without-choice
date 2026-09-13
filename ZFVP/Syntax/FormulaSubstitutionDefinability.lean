import ZFVP.Syntax.FormulaSubstitutionValidity
import ZFVP.Syntax.SubstitutionStateDefinability

/-! Definability of formula substitution with every input varying. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₅.comp

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance substitutedArguments_all_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (substitutedArguments (V := V)) := by
  unfold substitutedArguments
  exact Language.DefinableFunction₂.comp (by definability)
    (Language.DefinableFunction₅.comp (by definability) (by definability) (by definability)
      (by definability) (by definability))

instance formulaSubstitutionStep_all_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (formulaSubstitutionStep (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun z L Γ G q p : V ↦
      let φ := kpair.π₂ (kpair.π₁ q)
      let t := kpair.π₁ φ
      let d := kpair.π₂ φ
      (t = 0 ∧ z = truthCode) ∨
      (t ≠ 0 ∧ t = 1 ∧ z = falsityCode) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t = 2 ∧ z = atomCode (kpair.π₁ d) (substitutedArguments L Γ G q (kpair.π₂ d))) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 2 ∧ t = 3 ∧ z = negAtomCode (kpair.π₁ d) (substitutedArguments L Γ G q (kpair.π₂ d))) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t = 4 ∧ z =
        andCode (p ‘ (substitutionChild q (kpair.π₁ d))) (p ‘ (substitutionChild q (kpair.π₂ d)))) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ t = 5 ∧ z =
        orCode (p ‘ (substitutionChild q (kpair.π₁ d))) (p ‘ (substitutionChild q (kpair.π₂ d)))) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ t ≠ 5 ∧ t = 6 ∧ z = allCode (p ‘ (substitutionBody q d))) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ t ≠ 5 ∧ t ≠ 6 ∧ z = existsCode (p ‘ (substitutionBody q d)))) := by
    dsimp
    unfold truthCode falsityCode
    repeat' apply Language.Definable.or
    all_goals definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = formulaSubstitutionStep (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  unfold formulaSubstitutionStep
  dsimp
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

theorem formulaSubstitutionGraph_eq_iff (L Γ G g : V) :
    formulaSubstitutionGraph L Γ G = g ↔
      IsRecursionAttempt (formulaDepthRelation (formulaDepthDomain L Γ)) (formulaDepthDomain L Γ)
        (formulaSubstitutionStep L Γ G) g ∧ domain g = formulaDepthDomain L Γ :=
  wellFoundedRecursion_eq_iff (formulaDepthRelation_wellFounded (formulaDepthDomain L Γ))
    (formulaSubstitutionStep L Γ G) (by definability) g

instance formulaSubstitutionGraph_definable : ℒₛₑₜ-function₃[V] formulaSubstitutionGraph := by
  have h : ℒₛₑₜ-relation₄ (fun g L Γ G : V ↦
      IsRecursionAttempt (formulaDepthRelation (formulaDepthDomain L Γ)) (formulaDepthDomain L Γ)
        (formulaSubstitutionStep L Γ G) g ∧ domain g = formulaDepthDomain L Γ) := by
    unfold IsRecursionAttempt
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (formulaSubstitutionGraph_eq_iff (v 1) (v 2) (v 3) (v 0))

instance substituteFormula_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (substituteFormula (V := V)) := by
  unfold substituteFormula
  definability

end ZFVP
