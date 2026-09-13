import ZFVP.Syntax.FormulaRecursion

/-! Internal negation in the eight-constructor formula language. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def formulaNegationStep (q previous : V) : V := by
  classical
  let n := kpair.π₁ q
  let φ := kpair.π₂ q
  let tag := kpair.π₁ φ
  let data := kpair.π₂ φ
  exact if tag = 0 then falsityCode else if tag = 1 then truthCode
    else if tag = 2 then negAtomCode (kpair.π₁ data) (kpair.π₂ data)
    else if tag = 3 then atomCode (kpair.π₁ data) (kpair.π₂ data)
    else if tag = 4 then orCode (previous ‘ ⟨n, kpair.π₁ data⟩ₖ) (previous ‘ ⟨n, kpair.π₂ data⟩ₖ)
    else if tag = 5 then andCode (previous ‘ ⟨n, kpair.π₁ data⟩ₖ) (previous ‘ ⟨n, kpair.π₂ data⟩ₖ)
    else if tag = 6 then existsCode (previous ‘ ⟨succ n, data⟩ₖ)
    else allCode (previous ‘ ⟨succ n, data⟩ₖ)

instance formulaNegationStep_definable : ℒₛₑₜ-function₂[V] formulaNegationStep := by
  have h : ℒₛₑₜ-relation₃ (fun z q p : V ↦
      let n := kpair.π₁ q
      let φ := kpair.π₂ q
      let t := kpair.π₁ φ
      let d := kpair.π₂ φ
      (t = 0 ∧ z = falsityCode) ∨
      (t ≠ 0 ∧ t = 1 ∧ z = truthCode) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t = 2 ∧ z = negAtomCode (kpair.π₁ d) (kpair.π₂ d)) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 2 ∧ t = 3 ∧ z = atomCode (kpair.π₁ d) (kpair.π₂ d)) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t = 4 ∧
        z = orCode (p ‘ ⟨n, kpair.π₁ d⟩ₖ) (p ‘ ⟨n, kpair.π₂ d⟩ₖ)) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ t = 5 ∧
        z = andCode (p ‘ ⟨n, kpair.π₁ d⟩ₖ) (p ‘ ⟨n, kpair.π₂ d⟩ₖ)) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ t ≠ 5 ∧ t = 6 ∧
        z = existsCode (p ‘ ⟨succ n, d⟩ₖ)) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ t ≠ 5 ∧ t ≠ 6 ∧
        z = allCode (p ‘ ⟨succ n, d⟩ₖ))) := by
    dsimp
    unfold truthCode falsityCode
    repeat' apply Language.Definable.or
    all_goals definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = formulaNegationStep (v 1) (v 2) ↔ _
  unfold formulaNegationStep
  dsimp
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

noncomputable def formulaNegationGraph (L Γ : V) : V :=
  formulaRecursion L Γ formulaNegationStep (by definability)

instance formulaNegationGraph_isFunction (L Γ : V) : IsFunction (formulaNegationGraph L Γ) :=
  formulaRecursion_isFunction _ _ _ _

@[simp] theorem domain_formulaNegationGraph (L Γ : V) :
    domain (formulaNegationGraph L Γ) = formulaFamily L Γ := domain_formulaRecursion _ _ _ _

noncomputable def negateFormula (L Γ n φ : V) : V := (formulaNegationGraph L Γ) ‘ ⟨n, φ⟩ₖ

theorem formulaNegationGraph_eq_iff (L Γ g : V) : formulaNegationGraph L Γ = g ↔
    IsRecursionAttempt (subformulaRelation (formulaFamily L Γ)) (formulaFamily L Γ) formulaNegationStep g ∧
      domain g = formulaFamily L Γ := formulaRecursion_eq_iff _ _ _ _ _

instance formulaNegationGraph_definable : ℒₛₑₜ-function₂[V] formulaNegationGraph := by
  have h : ℒₛₑₜ-relation₃ (fun g L Γ : V ↦
      IsRecursionAttempt (subformulaRelation (formulaFamily L Γ)) (formulaFamily L Γ) formulaNegationStep g ∧
        domain g = formulaFamily L Γ) := by
    unfold IsRecursionAttempt
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (formulaNegationGraph_eq_iff (v 1) (v 2) (v 0))

instance negateFormula_definable : ℒₛₑₜ-function₄[V] negateFormula := by
  unfold negateFormula
  definability

instance negateFormula_fixed_definable (L Γ : V) : ℒₛₑₜ-function₂ (negateFormula L Γ) := by
  unfold negateFormula
  definability

theorem negateFormula_value (L Γ n φ : V) (hφ : φ ∈ formulaSet L Γ n) :
    negateFormula L Γ n φ = formulaNegationStep ⟨n, φ⟩ₖ ((formulaNegationGraph L Γ) ↾
      (predecessors (subformulaRelation (formulaFamily L Γ)) (formulaFamily L Γ) ⟨n, φ⟩ₖ)) :=
  formulaRecursion_value _ _ _ _ ((mem_formulaSet_iff _ _ _ _).mp hφ)

theorem formulaNegationGraph_previous {L Γ n φ p : V} (hL : IsLanguageCode L)
    (hφ : φ ∈ formulaSet L Γ n) (hp : IsImmediateSubformula p ⟨n, φ⟩ₖ) :
    ((formulaNegationGraph L Γ) ↾
      (predecessors (subformulaRelation (formulaFamily L Γ)) (formulaFamily L Γ) ⟨n, φ⟩ₖ)) ‘ p =
      (formulaNegationGraph L Γ) ‘ p :=
  formulaRecursion_previous_value hL _ _ ((mem_formulaSet_iff _ _ _ _).mp hφ) hp

theorem negateFormula_truth {L n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) (Γ : V) :
    negateFormula L Γ n truthCode = falsityCode := by
  rw [negateFormula_value _ _ _ _ (formulaSet_constants hL hn Γ).1]
  simp [formulaNegationStep, truthCode]

theorem negateFormula_falsity {L n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) (Γ : V) :
    negateFormula L Γ n falsityCode = truthCode := by
  rw [negateFormula_value _ _ _ _ (formulaSet_constants hL hn Γ).2]
  simp [formulaNegationStep, falsityCode]

theorem negateFormula_atom {L Γ n r args : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments L Γ n r args) : negateFormula L Γ n (atomCode r args) = negAtomCode r args := by
  rw [negateFormula_value _ _ _ _ (formulaSet_atoms hL hn ha).1]
  simp [formulaNegationStep, atomCode, negAtomCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem negateFormula_negAtom {L Γ n r args : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments L Γ n r args) : negateFormula L Γ n (negAtomCode r args) = atomCode r args := by
  rw [negateFormula_value _ _ _ _ (formulaSet_atoms hL hn ha).2]
  simp [formulaNegationStep, atomCode, negAtomCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem negateFormula_and {L Γ n φ ψ : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L Γ n) (hψ : ψ ∈ formulaSet L Γ n) :
    negateFormula L Γ n (andCode φ ψ) = orCode (negateFormula L Γ n φ) (negateFormula L Γ n ψ) := by
  have hp := (formulaSet_binary hL hn hφ hψ).1
  rw [negateFormula_value _ _ _ _ hp]
  simp [formulaNegationStep, andCode, orCode, negateFormula,
    OfNat.ofNat, internalNumeral_eq_iff]
  exact ⟨formulaNegationGraph_previous hL hp (Or.inl ⟨n, φ, ψ, Or.inl rfl, Or.inl rfl⟩),
    formulaNegationGraph_previous hL hp (Or.inl ⟨n, φ, ψ, Or.inl rfl, Or.inr rfl⟩)⟩

theorem negateFormula_or {L Γ n φ ψ : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L Γ n) (hψ : ψ ∈ formulaSet L Γ n) :
    negateFormula L Γ n (orCode φ ψ) = andCode (negateFormula L Γ n φ) (negateFormula L Γ n ψ) := by
  have hp := (formulaSet_binary hL hn hφ hψ).2
  rw [negateFormula_value _ _ _ _ hp]
  simp [formulaNegationStep, andCode, orCode, negateFormula,
    OfNat.ofNat, internalNumeral_eq_iff]
  exact ⟨formulaNegationGraph_previous hL hp (Or.inl ⟨n, φ, ψ, Or.inr rfl, Or.inl rfl⟩),
    formulaNegationGraph_previous hL hp (Or.inl ⟨n, φ, ψ, Or.inr rfl, Or.inr rfl⟩)⟩

theorem negateFormula_all {L Γ n φ : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L Γ (succ n)) :
    negateFormula L Γ n (allCode φ) = existsCode (negateFormula L Γ (succ n) φ) := by
  have hp := (formulaSet_quantifiers hL hn hφ).1
  rw [negateFormula_value _ _ _ _ hp]
  simp [formulaNegationStep, allCode, existsCode, negateFormula,
    OfNat.ofNat, internalNumeral_eq_iff]
  exact formulaNegationGraph_previous hL hp (Or.inr ⟨n, φ, Or.inl rfl, rfl⟩)

theorem negateFormula_exists {L Γ n φ : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L Γ (succ n)) :
    negateFormula L Γ n (existsCode φ) = allCode (negateFormula L Γ (succ n) φ) := by
  have hp := (formulaSet_quantifiers hL hn hφ).2
  rw [negateFormula_value _ _ _ _ hp]
  simp [formulaNegationStep, allCode, existsCode, negateFormula,
    OfNat.ofNat, internalNumeral_eq_iff]
  exact formulaNegationGraph_previous hL hp (Or.inr ⟨n, φ, Or.inr rfl, rfl⟩)

theorem negateFormula_mem {L Γ n φ : V} (hL : IsLanguageCode L) (hφ : φ ∈ formulaSet L Γ n) :
    negateFormula L Γ n φ ∈ formulaSet L Γ n := by
  refine formulaSet_induction hL Γ (fun n φ ↦ negateFormula L Γ n φ ∈ formulaSet L Γ n)
    (by definability) ?_ ?_ ?_ ?_ n φ hφ
  · intro n hn
    rw [negateFormula_truth hL hn, negateFormula_falsity hL hn]
    exact (formulaSet_constants hL hn Γ).symm
  · intro n hn r args ha
    rw [negateFormula_atom hL hn ha, negateFormula_negAtom hL hn ha]
    exact (formulaSet_atoms hL hn ha).symm
  · intro n hn φ ψ hφ hψ ihφ ihψ
    rw [negateFormula_and hL hn hφ hψ, negateFormula_or hL hn hφ hψ]
    exact (formulaSet_binary hL hn ihφ ihψ).symm
  · intro n hn φ hφ ih
    rw [negateFormula_all hL hn hφ, negateFormula_exists hL hn hφ]
    exact (formulaSet_quantifiers hL hn ih).symm

theorem negateFormula_involutive {L Γ n φ : V} (hL : IsLanguageCode L) (hφ : φ ∈ formulaSet L Γ n) :
    negateFormula L Γ n (negateFormula L Γ n φ) = φ := by
  refine formulaSet_induction hL Γ (fun n φ ↦ negateFormula L Γ n (negateFormula L Γ n φ) = φ)
    (by definability) ?_ ?_ ?_ ?_ n φ hφ
  · intro n hn
    rw [negateFormula_truth hL hn, negateFormula_falsity hL hn]
    exact ⟨rfl, negateFormula_truth hL hn Γ⟩
  · intro n hn r args ha
    rw [negateFormula_atom hL hn ha, negateFormula_negAtom hL hn ha]
    exact ⟨rfl, negateFormula_atom hL hn ha⟩
  · intro n hn φ ψ hφ hψ ihφ ihψ
    rw [negateFormula_and hL hn hφ hψ, negateFormula_or hL hn hφ hψ,
      negateFormula_or hL hn (negateFormula_mem hL hφ) (negateFormula_mem hL hψ),
      negateFormula_and hL hn (negateFormula_mem hL hφ) (negateFormula_mem hL hψ), ihφ, ihψ]
    exact ⟨rfl, rfl⟩
  · intro n hn φ hφ ih
    rw [negateFormula_all hL hn hφ, negateFormula_exists hL hn hφ,
      negateFormula_exists hL hn (negateFormula_mem hL hφ),
      negateFormula_all hL hn (negateFormula_mem hL hφ), ih]
    exact ⟨rfl, rfl⟩

end ZFVP
