import ZFVP.Syntax.LiftSubstitution
import ZFVP.SetTheory.NaturalIteration

/-! All iterated binder-lifting states form one internal set. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def substitutionState (n m B E : V) : V := ⟨⟨n, m⟩ₖ, ⟨B, E⟩ₖ⟩ₖ
noncomputable def stateSource (s : V) : V := kpair.π₁ (kpair.π₁ s)
noncomputable def stateTarget (s : V) : V := kpair.π₂ (kpair.π₁ s)
noncomputable def stateBound (s : V) : V := kpair.π₁ (kpair.π₂ s)
noncomputable def stateFree (s : V) : V := kpair.π₂ (kpair.π₂ s)

@[simp] theorem stateSource_code (n m B E : V) : stateSource (substitutionState n m B E) = n := by
  simp [stateSource, substitutionState]
@[simp] theorem stateTarget_code (n m B E : V) : stateTarget (substitutionState n m B E) = m := by
  simp [stateTarget, substitutionState]
@[simp] theorem stateBound_code (n m B E : V) : stateBound (substitutionState n m B E) = B := by
  simp [stateBound, substitutionState]
@[simp] theorem stateFree_code (n m B E : V) : stateFree (substitutionState n m B E) = E := by
  simp [stateFree, substitutionState]

instance substitutionState_definable : ℒₛₑₜ-function₄[V] substitutionState := by
  unfold substitutionState
  definability
instance stateSource_definable : ℒₛₑₜ-function₁[V] stateSource := by unfold stateSource; definability
instance stateTarget_definable : ℒₛₑₜ-function₁[V] stateTarget := by unfold stateTarget; definability
instance stateBound_definable : ℒₛₑₜ-function₁[V] stateBound := by unfold stateBound; definability
instance stateFree_definable : ℒₛₑₜ-function₁[V] stateFree := by unfold stateFree; definability

noncomputable def liftSubstitutionState (L Δ s : V) : V :=
  substitutionState (succ (stateSource s)) (succ (stateTarget s))
    (liftBoundReplacement L Δ (stateTarget s) (stateSource s) (stateBound s))
    (liftFreeReplacement L Δ (stateTarget s) (stateFree s))

instance liftSubstitutionState_definable : ℒₛₑₜ-function₃[V] liftSubstitutionState := by
  unfold liftSubstitutionState substitutionState
  have hB : ℒₛₑₜ-function₃ (fun L Δ s : V ↦
      liftBoundReplacement L Δ (stateTarget s) (stateSource s) (stateBound s)) :=
    Language.DefinableFunction₅.comp (by definability) (by definability) (by definability)
      (by definability) (by definability)
  have hE : ℒₛₑₜ-function₃ (fun L Δ s : V ↦ liftFreeReplacement L Δ (stateTarget s) (stateFree s)) :=
    Language.DefinableFunction₄.comp (by definability) (by definability) (by definability) (by definability)
  definability

def IsSubstitutionState (L Γ Δ s : V) : Prop :=
  stateSource s ∈ (ω : V) ∧ stateTarget s ∈ (ω : V) ∧
  stateBound s ∈ termSet L Δ (stateTarget s) ^ stateSource s ∧
  stateFree s ∈ termSet L Δ (stateTarget s) ^ Γ

instance isSubstitutionState_definable : ℒₛₑₜ-relation₄[V] IsSubstitutionState := by
  unfold IsSubstitutionState
  definability

theorem liftSubstitutionState_valid {L Γ Δ s : V} (hL : IsLanguageCode L)
    (hs : IsSubstitutionState L Γ Δ s) : IsSubstitutionState L Γ Δ (liftSubstitutionState L Δ s) := by
  rcases hs with ⟨hn, hm, hB, hE⟩
  simp only [IsSubstitutionState, liftSubstitutionState, stateSource_code, stateTarget_code,
    stateBound_code, stateFree_code]
  exact ⟨ω_succ_closed hn, ω_succ_closed hm, liftBoundReplacement_mem hL hm hn hB,
    liftFreeReplacement_mem hL hm hE⟩

noncomputable def substitutionStates (L Δ s : V) : V :=
  naturalIterationGraph (liftSubstitutionState L Δ) (by definability) s

instance substitutionStates_isFunction (L Δ s : V) : IsFunction (substitutionStates L Δ s) :=
  naturalIterationGraph_isFunction _ _ _

@[simp] theorem domain_substitutionStates (L Δ s : V) : domain (substitutionStates L Δ s) = ω :=
  domain_naturalIterationGraph _ _ _

theorem substitutionStates_zero (L Δ s : V) : (substitutionStates L Δ s) ‘ (0 : V) = s := by
  rw [substitutionStates, naturalIterationGraph_value _ _ _ (by simp), naturalIteration_zero]

theorem substitutionStates_succ (L Δ s : V) {k : V} (hk : k ∈ (ω : V)) :
    (substitutionStates L Δ s) ‘ (succ k) = liftSubstitutionState L Δ ((substitutionStates L Δ s) ‘ k) := by
  rw [substitutionStates, naturalIterationGraph_value _ _ _ (ω_succ_closed hk),
    naturalIteration_succ _ _ _ hk, naturalIterationGraph_value _ _ _ hk]

theorem substitutionStates_valid {L Γ Δ s k : V} (hL : IsLanguageCode L)
    (hs : IsSubstitutionState L Γ Δ s) (hk : k ∈ (ω : V)) :
    IsSubstitutionState L Γ Δ ((substitutionStates L Δ s) ‘ k) := by
  rw [substitutionStates, naturalIterationGraph_value _ _ _ hk]
  exact naturalIteration_invariant _ (by definability) s (IsSubstitutionState L Γ Δ)
    (by definability) hs (fun _ h ↦ liftSubstitutionState_valid hL h) k hk

end ZFVP
