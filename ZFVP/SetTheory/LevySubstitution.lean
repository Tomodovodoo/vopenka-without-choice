import ZFVP.SetTheory.LevyFormulas

/-! Capture-avoiding substitution preserves the external Levy hierarchy. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[simp] theorem rew_boundedSetAll {n m : ℕ} (σ : Rew ℒₛₑₜ Empty n Empty m)
    (t : SetTheorySemiterm Empty n) (φ : SetTheorySemisentence (n + 1)) :
    σ ▹ boundedSetAll t φ = boundedSetAll (σ t) (σ.q ▹ φ) := by
  change ((σ.q ▹ (Semiformula.nrel Language.Set.Rel.mem ![.bvar 0, Rew.bShift t])).or (σ.q ▹ φ)).all = _
  simp [boundedSetAll]

@[simp] theorem rew_boundedSetExs {n m : ℕ} (σ : Rew ℒₛₑₜ Empty n Empty m)
    (t : SetTheorySemiterm Empty n) (φ : SetTheorySemisentence (n + 1)) :
    σ ▹ boundedSetExs t φ = boundedSetExs (σ t) (σ.q ▹ φ) := by
  change ((σ.q ▹ (Semiformula.rel Language.Set.Rel.mem ![.bvar 0, Rew.bShift t])).and (σ.q ▹ φ)).exs = _
  simp [boundedSetExs]

theorem IsBoundedSetFormula.rew {n m : ℕ} {φ : SetTheorySemisentence n}
    (h : IsBoundedSetFormula φ) (σ : Rew ℒₛₑₜ Empty n Empty m) :
    IsBoundedSetFormula (σ ▹ φ) := by
  induction h generalizing m with
  | verum => exact .verum
  | falsum => exact .falsum
  | rel r ts => exact .rel r (σ ∘ ts)
  | nrel r ts => exact .nrel r (σ ∘ ts)
  | and hφ hψ ihφ ihψ => exact .and (ihφ σ) (ihψ σ)
  | or hφ hψ ihφ ihψ => exact .or (ihφ σ) (ihψ σ)
  | all t hφ ih => simpa only [rew_boundedSetAll] using IsBoundedSetFormula.all (σ t) (ih σ.q)
  | exs t hφ ih => simpa only [rew_boundedSetExs] using IsBoundedSetFormula.exs (σ t) (ih σ.q)

theorem IsLevyFormula.rew {p k n m} {φ : SetTheorySemisentence n}
    (h : IsLevyFormula p k φ) (σ : Rew ℒₛₑₜ Empty n Empty m) :
    IsLevyFormula p k (σ ▹ φ) := by
  induction h generalizing m with
  | bounded hφ => exact .bounded (hφ.rew σ)
  | raise hφ ih => exact .raise (ih σ)
  | and hφ hψ ihφ ihψ => exact .and (ihφ σ) (ihψ σ)
  | or hφ hψ ihφ ihψ => exact .or (ihφ σ) (ihψ σ)
  | boundedAll t hφ ih => simpa only [rew_boundedSetAll] using IsLevyFormula.boundedAll (σ t) (ih σ.q)
  | boundedExs t hφ ih => simpa only [rew_boundedSetExs] using IsLevyFormula.boundedExs (σ t) (ih σ.q)
  | exs hφ ih => exact .exs (ih σ.q)
  | all hφ ih => exact .all (ih σ.q)

theorem IsBoundedSetFormula.subst {n m : ℕ} {φ : SetTheorySemisentence n}
    (h : IsBoundedSetFormula φ) (ts : Fin n → SetTheorySemiterm Empty m) :
    IsBoundedSetFormula (φ.subst ts) := h.rew (Rew.subst ts)

theorem IsLevyFormula.subst {p k n m} {φ : SetTheorySemisentence n}
    (h : IsLevyFormula p k φ) (ts : Fin n → SetTheorySemiterm Empty m) :
    IsLevyFormula p k (φ.subst ts) := h.rew (Rew.subst ts)

end ZFVP


