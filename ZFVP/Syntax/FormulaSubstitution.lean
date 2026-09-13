import ZFVP.Syntax.FormulaDepthRecursion
import ZFVP.Syntax.SubstitutionStates

/-! Internal formula substitution, carrying the precomputed binder-depth states. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def substitutedArguments (L Γ G q args : V) : V :=
  compose args (termSubstitution L Γ (kpair.π₁ (kpair.π₁ q))
    (stateBound (G ‘ (kpair.π₂ q))) (stateFree (G ‘ (kpair.π₂ q))))

instance substitutedArguments_fixed_definable (L Γ G : V) :
    ℒₛₑₜ-function₂ (substitutedArguments L Γ G) := by
  have h : ℒₛₑₜ-function₁ (fun q : V ↦ termSubstitution L Γ (kpair.π₁ (kpair.π₁ q))
      (stateBound (G ‘ (kpair.π₂ q))) (stateFree (G ‘ (kpair.π₂ q)))) :=
    Language.DefinableFunction₅.comp (by definability) (by definability) (by definability)
      (by definability) (by definability)
  unfold substitutedArguments
  exact Language.DefinableFunction₂.comp (by definability)
    (Language.DefinableFunction₁.comp (F := fun q ↦ termSubstitution L Γ (kpair.π₁ (kpair.π₁ q))
      (stateBound (G ‘ (kpair.π₂ q))) (stateFree (G ‘ (kpair.π₂ q)))) (by definability))

noncomputable def substitutionChild (q φ : V) : V := ⟨⟨kpair.π₁ (kpair.π₁ q), φ⟩ₖ, kpair.π₂ q⟩ₖ
noncomputable def substitutionBody (q φ : V) : V := ⟨⟨succ (kpair.π₁ (kpair.π₁ q)), φ⟩ₖ, succ (kpair.π₂ q)⟩ₖ

instance substitutionChild_definable : ℒₛₑₜ-function₂[V] substitutionChild := by
  unfold substitutionChild
  definability
instance substitutionBody_definable : ℒₛₑₜ-function₂[V] substitutionBody := by
  unfold substitutionBody
  definability

noncomputable def formulaSubstitutionStep (L Γ G q previous : V) : V := by
  classical
  let φ := kpair.π₂ (kpair.π₁ q)
  let tag := kpair.π₁ φ
  let data := kpair.π₂ φ
  exact if tag = 0 then truthCode else if tag = 1 then falsityCode
    else if tag = 2 then atomCode (kpair.π₁ data) (substitutedArguments L Γ G q (kpair.π₂ data))
    else if tag = 3 then negAtomCode (kpair.π₁ data) (substitutedArguments L Γ G q (kpair.π₂ data))
    else if tag = 4 then andCode (previous ‘ (substitutionChild q (kpair.π₁ data)))
      (previous ‘ (substitutionChild q (kpair.π₂ data)))
    else if tag = 5 then orCode (previous ‘ (substitutionChild q (kpair.π₁ data)))
      (previous ‘ (substitutionChild q (kpair.π₂ data)))
    else if tag = 6 then allCode (previous ‘ (substitutionBody q data))
    else existsCode (previous ‘ (substitutionBody q data))

instance formulaSubstitutionStep_definable (L Γ G : V) :
    ℒₛₑₜ-function₂ (formulaSubstitutionStep L Γ G) := by
  have h : ℒₛₑₜ-relation₃ (fun z q p : V ↦
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
  change v 0 = formulaSubstitutionStep L Γ G (v 1) (v 2) ↔ _
  unfold formulaSubstitutionStep
  dsimp
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

noncomputable def formulaSubstitutionGraph (L Γ G : V) : V :=
  formulaDepthRecursion L Γ (formulaSubstitutionStep L Γ G) (by definability)

instance formulaSubstitutionGraph_isFunction (L Γ G : V) : IsFunction (formulaSubstitutionGraph L Γ G) :=
  formulaDepthRecursion_isFunction _ _ _ _

@[simp] theorem domain_formulaSubstitutionGraph (L Γ G : V) :
    domain (formulaSubstitutionGraph L Γ G) = formulaDepthDomain L Γ := domain_formulaDepthRecursion _ _ _ _

noncomputable def substituteFormula (L Γ Δ s φ : V) : V :=
  (formulaSubstitutionGraph L Γ (substitutionStates L Δ s)) ‘ ⟨⟨stateSource s, φ⟩ₖ, (0 : V)⟩ₖ

end ZFVP
