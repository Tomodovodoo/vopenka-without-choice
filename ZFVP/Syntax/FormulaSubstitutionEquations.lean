import ZFVP.Syntax.FormulaSubstitution

/-! Constructor equations for formula substitution at each internal binder depth. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem formulaSubstitutionGraph_value (L Γ G : V) {n φ k : V}
    (hφ : φ ∈ formulaSet L Γ n) (hk : k ∈ (ω : V)) :
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ =
      formulaSubstitutionStep L Γ G ⟨⟨n, φ⟩ₖ, k⟩ₖ ((formulaSubstitutionGraph L Γ G) ↾
        (predecessors (formulaDepthRelation (formulaDepthDomain L Γ)) (formulaDepthDomain L Γ)
          ⟨⟨n, φ⟩ₖ, k⟩ₖ)) :=
  formulaDepthRecursion_value L Γ _ _ ((pair_mem_formulaDepthDomain _ _ _ _).mpr
    ⟨(mem_formulaSet_iff _ _ _ _).mp hφ, hk⟩)

theorem formulaSubstitutionGraph_previous {L Γ G n φ p i k : V} (hL : IsLanguageCode L)
    (hφ : φ ∈ formulaSet L Γ n) (hi : i ∈ (ω : V)) (hk : k ∈ (ω : V))
    (hp : IsImmediateSubformula p ⟨n, φ⟩ₖ) :
    ((formulaSubstitutionGraph L Γ G) ↾
      (predecessors (formulaDepthRelation (formulaDepthDomain L Γ)) (formulaDepthDomain L Γ)
        ⟨⟨n, φ⟩ₖ, k⟩ₖ)) ‘ ⟨p, i⟩ₖ = (formulaSubstitutionGraph L Γ G) ‘ ⟨p, i⟩ₖ :=
  formulaDepthRecursion_previous hL _ _ ((mem_formulaSet_iff _ _ _ _).mp hφ) hi hk hp

theorem formulaSubstitutionGraph_truth {L n k : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) (Γ G : V) :
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, truthCode⟩ₖ, k⟩ₖ = truthCode := by
  rw [formulaSubstitutionGraph_value _ _ _ (formulaSet_constants hL hn Γ).1 hk]
  simp [formulaSubstitutionStep, truthCode]

theorem formulaSubstitutionGraph_falsity {L n k : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) (Γ G : V) :
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, falsityCode⟩ₖ, k⟩ₖ = falsityCode := by
  rw [formulaSubstitutionGraph_value _ _ _ (formulaSet_constants hL hn Γ).2 hk]
  simp [formulaSubstitutionStep, falsityCode]

theorem formulaSubstitutionGraph_atom {L Γ n k r args : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) (ha : IsAtomicArguments L Γ n r args) (G : V) :
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, atomCode r args⟩ₖ, k⟩ₖ =
      atomCode r (compose args (termSubstitution L Γ n (stateBound (G ‘ k)) (stateFree (G ‘ k)))) := by
  rw [formulaSubstitutionGraph_value _ _ _ (formulaSet_atoms hL hn ha).1 hk]
  simp [formulaSubstitutionStep, atomCode, substitutedArguments, OfNat.ofNat, internalNumeral_eq_iff]

theorem formulaSubstitutionGraph_negAtom {L Γ n k r args : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) (ha : IsAtomicArguments L Γ n r args) (G : V) :
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, negAtomCode r args⟩ₖ, k⟩ₖ =
      negAtomCode r (compose args (termSubstitution L Γ n (stateBound (G ‘ k)) (stateFree (G ‘ k)))) := by
  rw [formulaSubstitutionGraph_value _ _ _ (formulaSet_atoms hL hn ha).2 hk]
  simp [formulaSubstitutionStep, negAtomCode, substitutedArguments, OfNat.ofNat, internalNumeral_eq_iff]

theorem formulaSubstitutionGraph_and {L Γ n k φ ψ : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V))
    (hφ : φ ∈ formulaSet L Γ n) (hψ : ψ ∈ formulaSet L Γ n) (G : V) :
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, andCode φ ψ⟩ₖ, k⟩ₖ =
      andCode ((formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ)
        ((formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, ψ⟩ₖ, k⟩ₖ) := by
  have hp := (formulaSet_binary hL hn hφ hψ).1
  rw [formulaSubstitutionGraph_value _ _ _ hp hk]
  simp [formulaSubstitutionStep, andCode, kpair.π₁_kpair, kpair.π₂_kpair,
    OfNat.ofNat, internalNumeral_eq_iff, reduceCtorEq, ↓reduceIte, substitutionChild]
  exact ⟨formulaSubstitutionGraph_previous hL hp hk hk (Or.inl ⟨n, φ, ψ, Or.inl rfl, Or.inl rfl⟩),
    formulaSubstitutionGraph_previous hL hp hk hk (Or.inl ⟨n, φ, ψ, Or.inl rfl, Or.inr rfl⟩)⟩

theorem formulaSubstitutionGraph_or {L Γ n k φ ψ : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V))
    (hφ : φ ∈ formulaSet L Γ n) (hψ : ψ ∈ formulaSet L Γ n) (G : V) :
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, orCode φ ψ⟩ₖ, k⟩ₖ =
      orCode ((formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, φ⟩ₖ, k⟩ₖ)
        ((formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, ψ⟩ₖ, k⟩ₖ) := by
  have hp := (formulaSet_binary hL hn hφ hψ).2
  rw [formulaSubstitutionGraph_value _ _ _ hp hk]
  simp [formulaSubstitutionStep, orCode, kpair.π₁_kpair, kpair.π₂_kpair,
    OfNat.ofNat, internalNumeral_eq_iff, reduceCtorEq, ↓reduceIte, substitutionChild]
  exact ⟨formulaSubstitutionGraph_previous hL hp hk hk (Or.inl ⟨n, φ, ψ, Or.inr rfl, Or.inl rfl⟩),
    formulaSubstitutionGraph_previous hL hp hk hk (Or.inl ⟨n, φ, ψ, Or.inr rfl, Or.inr rfl⟩)⟩

theorem formulaSubstitutionGraph_all {L Γ n k φ : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) (hφ : φ ∈ formulaSet L Γ (succ n)) (G : V) :
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, allCode φ⟩ₖ, k⟩ₖ =
      allCode ((formulaSubstitutionGraph L Γ G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ) := by
  have hp := (formulaSet_quantifiers hL hn hφ).1
  rw [formulaSubstitutionGraph_value _ _ _ hp hk]
  simp [formulaSubstitutionStep, allCode, kpair.π₁_kpair, kpair.π₂_kpair,
    OfNat.ofNat, internalNumeral_eq_iff, reduceCtorEq, ↓reduceIte, substitutionBody]
  exact formulaSubstitutionGraph_previous hL hp (ω_succ_closed hk) hk (Or.inr ⟨n, φ, Or.inl rfl, rfl⟩)

theorem formulaSubstitutionGraph_exists {L Γ n k φ : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hk : k ∈ (ω : V)) (hφ : φ ∈ formulaSet L Γ (succ n)) (G : V) :
    (formulaSubstitutionGraph L Γ G) ‘ ⟨⟨n, existsCode φ⟩ₖ, k⟩ₖ =
      existsCode ((formulaSubstitutionGraph L Γ G) ‘ ⟨⟨succ n, φ⟩ₖ, succ k⟩ₖ) := by
  have hp := (formulaSet_quantifiers hL hn hφ).2
  rw [formulaSubstitutionGraph_value _ _ _ hp hk]
  simp [formulaSubstitutionStep, existsCode, kpair.π₁_kpair, kpair.π₂_kpair,
    OfNat.ofNat, internalNumeral_eq_iff, reduceCtorEq, ↓reduceIte, substitutionBody]
  exact formulaSubstitutionGraph_previous hL hp (ω_succ_closed hk) hk (Or.inr ⟨n, φ, Or.inr rfl, rfl⟩)

end ZFVP
