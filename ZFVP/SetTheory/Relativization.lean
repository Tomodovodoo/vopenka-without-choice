import Foundation.FirstOrder.SetTheory.Basic

/-! Syntactic relativization to a set parameter, including empty domains. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The membership structure induced on the elements of an internal set. -/
def SetDomain {V : Type*} [SetStructure V] (a : V) := {x : V // x ∈ a}

instance {V : Type*} [SetStructure V] (a : V) : SetStructure (SetDomain a) :=
  ⟨fun x y ↦ y.val ∈ x.val⟩

/-- Reserve the free variable `none` for the domain parameter. -/
def liftDomainTerm {ξ : Type*} {n : ℕ} :
    SetTheorySemiterm ξ n → SetTheorySemiterm (Option ξ) n
  | .bvar i => .bvar i
  | .fvar x => .fvar (some x)

/-- Bound each quantifier by membership in the additional free parameter. -/
def relativize {ξ : Type*} : {n : ℕ} →
    SetTheorySemiformula ξ n → SetTheorySemiformula (Option ξ) n
  | _, .verum => .verum
  | _, .falsum => .falsum
  | _, .rel r ts => .rel r (fun i ↦ liftDomainTerm (ts i))
  | _, .nrel r ts => .nrel r (fun i ↦ liftDomainTerm (ts i))
  | _, .and φ ψ => .and (relativize φ) (relativize ψ)
  | _, .or φ ψ => .or (relativize φ) (relativize ψ)
  | _, .all φ => .all (.or (.nrel Language.Set.Rel.mem ![.bvar 0, .fvar none])
      (relativize φ))
  | _, .exs φ => .exs (.and (.rel Language.Set.Rel.mem ![.bvar 0, .fvar none])
      (relativize φ))

variable {V : Type*} [SetStructure V] {ξ : Type*} {n : ℕ}

theorem setDomain_val_vecCons (a : V) (x : SetDomain a) (b : Fin n → SetDomain a) :
    (fun i ↦ ((x :> b) i).val) = (x.val :> fun i ↦ (b i).val) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl

theorem val_liftDomainTerm (a : V) (b : Fin n → SetDomain a)
    (f : ξ → SetDomain a) (t : SetTheorySemiterm ξ n) :
    (liftDomainTerm t).val (fun i ↦ (b i).val)
      (fun x ↦ x.elim a (fun i ↦ (f i).val)) = (t.val b f).val := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func g ts => exact Empty.elim g

theorem eval_relativize (a : V) (φ : SetTheorySemiformula ξ n)
    (b : Fin n → SetDomain a) (f : ξ → SetDomain a) :
    (relativize φ).Eval (fun i ↦ (b i).val)
      (fun x ↦ x.elim a (fun i ↦ (f i).val)) ↔ φ.Eval b f := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
    cases r <;> simp only [relativize, Semiformula.eval_rel, Structure.rel, Function.comp_def,
      val_liftDomainTerm]
    · exact Subtype.ext_iff.symm
    · rfl
  | nrel r ts =>
    cases r <;> simp only [relativize, Semiformula.eval_nrel, Structure.rel, Function.comp_def,
      val_liftDomainTerm]
    · exact not_congr Subtype.ext_iff.symm
    · rfl
  | and φ ψ ihφ ihψ => exact and_congr (ihφ b) (ihψ b)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ b) (ihψ b)
  | all φ ih =>
    change (∀ x : V, x ∉ a ∨ (relativize φ).Eval (x :> fun i ↦ (b i).val) (fun x ↦ x.elim a (fun i ↦ (f i).val))) ↔ ∀ x : SetDomain a, φ.Eval (x :> b) f
    constructor
    · intro h x
      apply (ih (x :> b)).mp
      have hx := h x.val
      simpa [x.property, setDomain_val_vecCons] using hx
    · intro h x
      by_cases hx : x ∈ a
      · have hh := (ih (⟨x, hx⟩ :> b)).mpr (h ⟨x, hx⟩)
        exact Or.inr (by simpa only [setDomain_val_vecCons a ⟨x, hx⟩ b] using hh)
      · exact Or.inl hx
  | exs φ ih =>
    change (∃ x : V, x ∈ a ∧ (relativize φ).Eval (x :> fun i ↦ (b i).val) (fun x ↦ x.elim a (fun i ↦ (f i).val))) ↔ ∃ x : SetDomain a, φ.Eval (x :> b) f
    constructor
    · rintro ⟨x, hx⟩
      have hx' : x ∈ a ∧ (relativize φ).Eval (x :> fun i ↦ (b i).val)
          (fun x ↦ x.elim a (fun i ↦ (f i).val)) := by
        exact hx
      exact ⟨⟨x, hx'.1⟩, (ih (⟨x, hx'.1⟩ :> b)).mp (by simpa only [setDomain_val_vecCons a ⟨x, hx'.1⟩ b] using hx'.2)⟩
    · rintro ⟨x, hx⟩
      refine ⟨x.val, ?_⟩
      have hh := (ih (x :> b)).mpr hx
      exact ⟨x.property, by simpa [setDomain_val_vecCons] using hh⟩

end ZFVP




