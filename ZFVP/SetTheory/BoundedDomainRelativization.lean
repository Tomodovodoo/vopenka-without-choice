import ZFVP.SetTheory.LevySubstitution

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedDomainRelativize : {n m : ℕ} → SetTheorySemisentence n →
    SetTheorySemiterm Empty m → Rew ℒₛₑₜ Empty n Empty m → SetTheorySemisentence m
  | _, _, .verum, _, _ => .verum
  | _, _, .falsum, _, _ => .falsum
  | _, _, .rel r ts, _, σ => .rel r (σ ∘ ts)
  | _, _, .nrel r ts, _, σ => .nrel r (σ ∘ ts)
  | _, _, .and φ ψ, t, σ => .and (boundedDomainRelativize φ t σ) (boundedDomainRelativize ψ t σ)
  | _, _, .or φ ψ, t, σ => .or (boundedDomainRelativize φ t σ) (boundedDomainRelativize ψ t σ)
  | _, _, .all φ, t, σ => boundedSetAll t (boundedDomainRelativize φ (Rew.bShift t) σ.q)
  | _, _, .exs φ, t, σ => boundedSetExs t (boundedDomainRelativize φ (Rew.bShift t) σ.q)

theorem boundedDomainRelativize_bounded {n m : ℕ} (φ : SetTheorySemisentence n)
    (t : SetTheorySemiterm Empty m) (σ : Rew ℒₛₑₜ Empty n Empty m) :
    IsBoundedSetFormula (boundedDomainRelativize φ t σ) := by
  induction φ generalizing m with
  | verum => exact .verum
  | falsum => exact .falsum
  | rel r ts => exact .rel _ _
  | nrel r ts => exact .nrel _ _
  | and φ ψ ihφ ihψ => exact .and (ihφ t σ) (ihψ t σ)
  | or φ ψ ihφ ihψ => exact .or (ihφ t σ) (ihψ t σ)
  | all φ ih => exact .all t (ih (Rew.bShift t) σ.q)
  | exs φ ih => exact .exs t (ih (Rew.bShift t) σ.q)

variable {V : Type*} [SetStructure V]

theorem domain_rew_quantifier_values {A : V} {n m : ℕ}
    (σ : Rew ℒₛₑₜ Empty n Empty m) (b : Fin n → SetDomain A) (v : Fin m → V)
    (hσ : ∀ s, (σ s).val v Empty.elim = (s.val b Empty.elim).val) (x : SetDomain A) :
    ∀ s, (σ.q s).val (x.val :> v) Empty.elim = (s.val (x :> b) Empty.elim).val := by
  intro s
  cases s with
  | bvar i =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simpa using hσ (.bvar j)
  | fvar e => exact Empty.elim e
  | func f ts => exact Empty.elim f

theorem eval_boundedDomainRelativize {A : V} {n m : ℕ} (φ : SetTheorySemisentence n)
    (t : SetTheorySemiterm Empty m) (σ : Rew ℒₛₑₜ Empty n Empty m)
    (b : Fin n → SetDomain A) (v : Fin m → V) (ht : t.val v Empty.elim = A)
    (hσ : ∀ s, (σ s).val v Empty.elim = (s.val b Empty.elim).val) :
    (boundedDomainRelativize φ t σ).Evalb v ↔ φ.Evalb b := by
  induction φ generalizing m with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
    cases r <;> simp only [boundedDomainRelativize, Semiformula.Evalb,
      Semiformula.eval_rel, Structure.rel, Function.comp_def, hσ]
    · exact Subtype.ext_iff.symm
    · rfl
  | nrel r ts =>
    cases r <;> simp only [boundedDomainRelativize, Semiformula.Evalb,
      Semiformula.eval_nrel, Structure.rel, Function.comp_def, hσ]
    · exact not_congr Subtype.ext_iff.symm
    · rfl
  | and φ ψ ihφ ihψ => exact and_congr (ihφ t σ b v ht hσ) (ihψ t σ b v ht hσ)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ t σ b v ht hσ) (ihψ t σ b v ht hσ)
  | all φ ih =>
    rw [boundedDomainRelativize, eval_boundedSetAll, ht]
    constructor
    · intro h x
      exact (ih (Rew.bShift t) σ.q (x :> b) (x.val :> v)
        (by simpa using ht) (domain_rew_quantifier_values σ b v hσ x)).mp (h x.val x.property)
    · intro h x hx
      exact (ih (Rew.bShift t) σ.q ((⟨x, hx⟩ : SetDomain A) :> b) (x :> v)
        (by simpa using ht) (domain_rew_quantifier_values σ b v hσ ⟨x, hx⟩)).mpr (h ⟨x, hx⟩)
  | exs φ ih =>
    rw [boundedDomainRelativize, eval_boundedSetExs, ht]
    constructor
    · rintro ⟨x, hx, h⟩
      exact ⟨⟨x, hx⟩, (ih (Rew.bShift t) σ.q ((⟨x, hx⟩ : SetDomain A) :> b) (x :> v)
        (by simpa using ht) (domain_rew_quantifier_values σ b v hσ ⟨x, hx⟩)).mp h⟩
    · rintro ⟨x, h⟩
      exact ⟨x.val, x.property, (ih (Rew.bShift t) σ.q (x :> b) (x.val :> v)
        (by simpa using ht) (domain_rew_quantifier_values σ b v hσ x)).mpr h⟩

def boundedDomainSentenceFormula (φ : SetTheorySentence) : SetTheorySemisentence 1 :=
  boundedDomainRelativize φ (.bvar 0) (Rew.subst Fin.elim0)

theorem boundedDomainSentenceFormula_bounded (φ : SetTheorySentence) :
    IsBoundedSetFormula (boundedDomainSentenceFormula φ) :=
  boundedDomainRelativize_bounded φ _ _

theorem eval_boundedDomainSentenceFormula (φ : SetTheorySentence) (A : V) :
    (boundedDomainSentenceFormula φ).Evalb ![A] ↔
      φ.Evalb (![] : Fin 0 → SetDomain A) := by
  apply eval_boundedDomainRelativize φ _ _ ![] ![A] rfl
  intro s
  cases s with
  | bvar i => exact Fin.elim0 i
  | fvar e => exact Empty.elim e
  | func f ts => exact Empty.elim f

end ZFVP
