import ZFVP.Syntax.TermSubstitution
import ZFVP.Syntax.FoundationEncoding

/-! Internal term substitution agrees with Foundation rewriting on encoded terms. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Λ : Language} {ξ η : Type*}

theorem encodeSemiterm_rew {L Γ B E : V} (hL : IsLanguageCode L)
    (F : ∀ {k}, Λ.Func k → V) (e : ξ → V) (d : η → V)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : V)) (he : ∀ x, e x ∈ Γ)
    {n m : ℕ} (σ : Rew Λ ξ n η m)
    (hB : ∀ i : Fin n, B ‘ (i.val : V) = encodeSemiterm F d (σ (.bvar i)))
    (hE : ∀ x, E ‘ (e x) = encodeSemiterm F d (σ (.fvar x)))
    (t : Semiterm Λ ξ n) :
    (termSubstitution L Γ (n : V) B E) ‘ (encodeSemiterm F e t) =
      encodeSemiterm F d (σ t) := by
  induction t with
  | bvar i =>
    rw [encodeSemiterm, termSubstitution_boundVar hL (by simp) _ _ _
      (natCast_mem_of_lt i.isLt), hB]
  | fvar x =>
    rw [encodeSemiterm, termSubstitution_freeVar hL (by simp) _ _ _ (he x), hE]
  | func f ts ih =>
    rw [encodeSemiterm, termSubstitution_function hL (by simp) _ _ _
      (encodeSemiterm_mem hL F e hF he (.func f ts))]
    rw [compose_standardTuple _ _ (fun i ↦ by
      simpa using encodeSemiterm_mem hL F e hF he (ts i))]
    rw [σ.func']
    simp only [encodeSemiterm, ih]

end ZFVP
