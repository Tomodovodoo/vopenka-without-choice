import ZFVP.SetTheory.ElementaryMap

/-! Membership isomorphisms preserve full first-order satisfaction. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [SetStructure W]

theorem val_map_term {ξ : Type*} {n : ℕ} (g : V → W)
    (b : Fin n → V) (f : ξ → V) (t : SetTheorySemiterm ξ n) :
    t.val (fun i ↦ g (b i)) (fun i ↦ g (f i)) = g (t.val b f) := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func h ts => exact Empty.elim h

omit [SetStructure V] [SetStructure W] in
theorem map_vecCons {n : ℕ} (g : V → W) (x : V) (b : Fin n → V) :
    g ∘ (x :> b) = (g x :> g ∘ b) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl

theorem eval_membershipIso {ξ : Type*} {n : ℕ} (e : V ≃ W)
    (he : ∀ x y, e x ∈ e y ↔ x ∈ y) (φ : SetTheorySemiformula ξ n)
    (b : Fin n → V) (f : ξ → V) :
    φ.Eval b f ↔ φ.Eval (e ∘ b) (e ∘ f) := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
    cases r <;> simp only [Semiformula.eval_rel, Structure.rel,
      Function.comp_def,
      val_map_term]
    · exact e.injective.eq_iff.symm
    · exact (he _ _).symm
  | nrel r ts =>
    cases r <;> simp only [Semiformula.eval_nrel, Structure.rel,
      Function.comp_def,
      val_map_term]
    · exact not_congr e.injective.eq_iff.symm
    · exact not_congr (he _ _).symm
  | and φ ψ ihφ ihψ => exact and_congr (ihφ b) (ihψ b)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ b) (ihψ b)
  | all φ ih =>
    change (∀ x : V, φ.Eval (x :> b) f) ↔ ∀ y : W, φ.Eval (y :> e ∘ b) (e ∘ f)
    constructor
    · intro h y
      obtain ⟨x, rfl⟩ := e.surjective y
      simpa only [map_vecCons] using (ih (x :> b)).mp (h x)
    · intro h x
      apply (ih (x :> b)).mpr
      simpa only [map_vecCons] using h (e x)
  | exs φ ih =>
    change (∃ x : V, φ.Eval (x :> b) f) ↔ ∃ y : W, φ.Eval (y :> e ∘ b) (e ∘ f)
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨e x, by simpa only [map_vecCons] using (ih (x :> b)).mp hx⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := e.surjective y
      exact ⟨x, (ih (x :> b)).mpr (by simpa only [map_vecCons] using hy)⟩

def ElementaryMap.ofMembershipIso (e : V ≃ W)
    (he : ∀ x y, e x ∈ e y ↔ x ∈ y) : ElementaryMap V W where
  toFun := e
  elementary φ b f := eval_membershipIso e he φ b f

end ZFVP


