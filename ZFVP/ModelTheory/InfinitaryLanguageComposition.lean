import ZFVP.ModelTheory.InfinitaryLanguageDerivation

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace LanguageMap
variable {L K J : Language}

theorem hom_ext (η ε : L →ᵥ K)
    (hf : ∀ {k} (f : L.Func k), η.func f = ε.func f)
    (hr : ∀ {k} (r : L.Rel k), η.rel r = ε.rel r) : η = ε := by
  cases η
  cases ε
  congr
  · funext k f
    exact hf f
  · funext k r
    exact hr r

theorem term_comp (η : L →ᵥ K) (ε : K →ᵥ J) {n} (t : Semiterm L Empty n) :
    (t.lMap η).lMap ε = t.lMap (ε.comp η) := by
  induction t with
  | bvar i => rfl
  | fvar i => exact i.elim
  | func f ts ih => exact congrArg (Semiterm.func (ε.func (η.func f))) (funext ih)

theorem firstOrder_comp (η : L →ᵥ K) (ε : K →ᵥ J) {n} (φ : Semisentence L n) :
    (φ.lMap η).lMap ε = φ.lMap (ε.comp η) := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r ts => exact congrArg (Semiformula.rel (ε.rel (η.rel r))) (funext fun i ↦ term_comp η ε (ts i))
  | nrel r ts => exact congrArg (Semiformula.nrel (ε.rel (η.rel r))) (funext fun i ↦ term_comp η ε (ts i))
  | and φ ψ ihφ ihψ => exact congrArg₂ Semiformula.and ihφ ihψ
  | or φ ψ ihφ ihψ => exact congrArg₂ Semiformula.or ihφ ihψ
  | all φ ih => exact congrArg Semiformula.all ih
  | exs φ ih => exact congrArg Semiformula.exs ih

theorem formula_comp (η : L →ᵥ K) (ε : K →ᵥ J) {n} (φ : Formula L n) :
    (φ.lMap η).lMap ε = φ.lMap (ε.comp η) := by
  induction φ with
  | fo φ => exact congrArg Formula.fo (firstOrder_comp η ε φ)
  | neg φ ih => exact congrArg Formula.neg ih
  | conj φ ih => exact congrArg Formula.conj (funext ih)
  | exs φ ih => exact congrArg Formula.exs ih
  | q φ ih => exact congrArg Formula.q ih

theorem term_retract (η : L →ᵥ K) (ε : K →ᵥ L)
    (hf : ∀ {k} (f : L.Func k), ε.func (η.func f) = f)
    {n} (t : Semiterm L Empty n) : (t.lMap η).lMap ε = t := by
  induction t with
  | bvar i => rfl
  | fvar i => exact i.elim
  | func f ts ih =>
      change Semiterm.func (ε.func (η.func f)) (fun i ↦ ((ts i).lMap η).lMap ε) = _
      rw [hf]
      exact congrArg (Semiterm.func f) (funext ih)

theorem firstOrder_retract (η : L →ᵥ K) (ε : K →ᵥ L)
    (hf : ∀ {k} (f : L.Func k), ε.func (η.func f) = f)
    (hr : ∀ {k} (r : L.Rel k), ε.rel (η.rel r) = r)
    {n} (φ : Semisentence L n) : (φ.lMap η).lMap ε = φ := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
      change Semiformula.rel (ε.rel (η.rel r)) (fun i ↦ ((ts i).lMap η).lMap ε) = _
      rw [hr]
      exact congrArg (Semiformula.rel r) (funext fun i ↦ term_retract η ε hf (ts i))
  | nrel r ts =>
      change Semiformula.nrel (ε.rel (η.rel r)) (fun i ↦ ((ts i).lMap η).lMap ε) = _
      rw [hr]
      exact congrArg (Semiformula.nrel r) (funext fun i ↦ term_retract η ε hf (ts i))
  | and φ ψ ihφ ihψ => exact congrArg₂ Semiformula.and ihφ ihψ
  | or φ ψ ihφ ihψ => exact congrArg₂ Semiformula.or ihφ ihψ
  | all φ ih => exact congrArg Semiformula.all ih
  | exs φ ih => exact congrArg Semiformula.exs ih

theorem formula_retract (η : L →ᵥ K) (ε : K →ᵥ L)
    (hf : ∀ {k} (f : L.Func k), ε.func (η.func f) = f)
    (hr : ∀ {k} (r : L.Rel k), ε.rel (η.rel r) = r)
    {n} (φ : Formula L n) : (φ.lMap η).lMap ε = φ := by
  induction φ with
  | fo φ => exact congrArg Formula.fo (firstOrder_retract η ε hf hr φ)
  | neg φ ih => exact congrArg Formula.neg ih
  | conj φ ih => exact congrArg Formula.conj (funext ih)
  | exs φ ih => exact congrArg Formula.exs ih
  | q φ ih => exact congrArg Formula.q ih

/-- Retracting an equality-preserving language map also retracts every refutation. -/
theorem consistent_image [L.Eq] [K.Eq] (η : L →ᵥ K) (ε : K →ᵥ L)
    (he : ε.rel Language.Eq.eq = Language.Eq.eq)
    (hf : ∀ {k} (f : L.Func k), ε.func (η.func f) = f)
    (hr : ∀ {k} (r : L.Rel k), ε.rel (η.rel r) = r)
    {Γ : Set (Sentence L)} (hΓ : KeislerDerivation.Consistent Γ) :
    KeislerDerivation.Consistent (Formula.lMap η '' Γ) := by
  intro h
  have hd := h.lMap ε he
  have hs : Formula.lMap ε '' (Formula.lMap η '' Γ) = Γ := by
    ext φ
    constructor
    · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
      simpa only [formula_retract η ε hf hr] using hψ
    · intro hφ
      exact ⟨_, ⟨φ, hφ, rfl⟩, formula_retract η ε hf hr φ⟩
  rw [hs] at hd
  exact hΓ hd

end LanguageMap
end ZFVP.Infinitary

