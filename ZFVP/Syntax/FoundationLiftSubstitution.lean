import ZFVP.Syntax.LiftSubstitution

/-! Binder lifting of internal replacement tables matches Foundation's `Rew.q`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Λ : Language} {ξ η : Type*}

theorem liftBoundReplacement_encode {L Δ B : V} (hL : IsLanguageCode L)
    (F : ∀ {k}, Λ.Func k → V) (d : η → V)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : V)) (hd : ∀ x, d x ∈ Δ)
    {n m : ℕ} (σ : Rew Λ ξ n η m) (hB : B ∈ termSet L Δ (m : V) ^ (n : V))
    (hcompat : ∀ i : Fin n, B ‘ (i.val : V) = encodeSemiterm F d (σ (.bvar i)))
    (i : Fin (n + 1)) :
    (liftBoundReplacement L Δ (m : V) (n : V) B) ‘ (i.val : V) =
      encodeSemiterm F d (σ.q (.bvar i)) := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa [encodeSemiterm] using liftBoundReplacement_zero (V := V) (by simp : (n : V) ∈ ω) L Δ (m : V) B
  · simp only [Fin.val_succ, num_succ_def, Rew.q_bvar_succ]
    rw [liftBoundReplacement_succ hL (by simp) (by simp) hB (natCast_mem_of_lt j.isLt), hcompat]
    exact encodeSemiterm_bShift hL F d hF hd _

theorem liftFreeReplacement_encode {L Γ Δ E : V} (hL : IsLanguageCode L)
    (F : ∀ {k}, Λ.Func k → V) (e : ξ → V) (d : η → V)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : V))
    (he : ∀ x, e x ∈ Γ) (hd : ∀ x, d x ∈ Δ)
    {n m : ℕ} (σ : Rew Λ ξ n η m) (hE : E ∈ termSet L Δ (m : V) ^ Γ)
    (hcompat : ∀ x, E ‘ (e x) = encodeSemiterm F d (σ (.fvar x))) (x : ξ) :
    (liftFreeReplacement L Δ (m : V) E) ‘ (e x) =
      encodeSemiterm F d (σ.q (.fvar x)) := by
  rw [liftFreeReplacement_value hL (by simp) hE (he x), hcompat, Rew.q_fvar]
  exact encodeSemiterm_bShift hL F d hF hd _

end ZFVP
