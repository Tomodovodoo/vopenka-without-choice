import ZFVP.SetTheory.Relativization

/-! Syntactic relativization to a definable class. The class is given by a two-variable formula
`H`; its second argument is a parameter carried by the reserved free variable `none`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The membership structure induced on the elements of a class. -/
def ClassDomain {V : Type*} [SetStructure V] (P : V → Prop) := {x : V // P x}

instance {V : Type*} [SetStructure V] (P : V → Prop) : SetStructure (ClassDomain P) :=
  ⟨fun x y ↦ y.val ∈ x.val⟩

/-- The guard `H(#0, &none)` of a bound variable. -/
def classGuard {ξ : Type*} (H : SetTheorySemisentence 2) (n : ℕ) :
    SetTheorySemiformula (Option ξ) (n + 1) :=
  Rew.embSubsts ![Semiterm.bvar 0, Semiterm.fvar none] ▹ H

/-- Bound each quantifier by the class defined by `H` with the parameter `none`. -/
def relativizeClass {ξ : Type*} (H : SetTheorySemisentence 2) : {n : ℕ} →
    SetTheorySemiformula ξ n → SetTheorySemiformula (Option ξ) n
  | _, .verum => .verum
  | _, .falsum => .falsum
  | _, .rel r ts => .rel r (fun i ↦ liftDomainTerm (ts i))
  | _, .nrel r ts => .nrel r (fun i ↦ liftDomainTerm (ts i))
  | _, .and φ ψ => .and (relativizeClass H φ) (relativizeClass H ψ)
  | _, .or φ ψ => .or (relativizeClass H φ) (relativizeClass H ψ)
  | n, .all φ => .all (.or (∼(classGuard H n)) (relativizeClass H φ))
  | n, .exs φ => .exs (.and (classGuard H n) (relativizeClass H φ))

variable {V : Type*} [SetStructure V] {ξ : Type*} {n : ℕ}

theorem eval_classGuard (H : SetTheorySemisentence 2) (a x : V) (b : Fin n → V) (f : ξ → V) :
    (classGuard H n).Eval (x :> b) (fun y ↦ y.elim a f) ↔ H.Evalb ![x, a] := by
  unfold classGuard
  rw [Semiformula.eval_embSubsts]
  have hv : (Semiterm.val (L := ℒₛₑₜ) (M := V) (x :> b) (fun y ↦ y.elim a f) ∘
      (![Semiterm.bvar 0, Semiterm.fvar none] : Fin 2 → SetTheorySemiterm (Option ξ) (n + 1))) = ![x, a] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
  rw [hv]

theorem classDomain_val_vecCons (P : V → Prop) (x : ClassDomain P) (b : Fin n → ClassDomain P) :
    (fun i ↦ ((x :> b) i).val) = (x.val :> fun i ↦ (b i).val) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl

theorem val_liftDomainTerm_class (P : V → Prop) (a : V) (b : Fin n → ClassDomain P)
    (f : ξ → ClassDomain P) (t : SetTheorySemiterm ξ n) :
    (liftDomainTerm t).val (fun i ↦ (b i).val)
      (fun x ↦ x.elim a (fun i ↦ (f i).val)) = (t.val b f).val := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func g ts => exact Empty.elim g

/-- Truth of the relativized formula in `V` is truth in the class model. -/
theorem eval_relativizeClass (H : SetTheorySemisentence 2) (a : V) (φ : SetTheorySemiformula ξ n)
    (b : Fin n → ClassDomain (fun x : V ↦ H.Evalb ![x, a]))
    (f : ξ → ClassDomain (fun x : V ↦ H.Evalb ![x, a])) :
    (relativizeClass H φ).Eval (fun i ↦ (b i).val)
      (fun x ↦ x.elim a (fun i ↦ (f i).val)) ↔ φ.Eval b f := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
    cases r <;> simp only [relativizeClass, Semiformula.eval_rel, Structure.rel, Function.comp_def,
      val_liftDomainTerm_class]
    · exact Subtype.ext_iff.symm
    · rfl
  | nrel r ts =>
    cases r <;> simp only [relativizeClass, Semiformula.eval_nrel, Structure.rel, Function.comp_def,
      val_liftDomainTerm_class]
    · exact not_congr Subtype.ext_iff.symm
    · rfl
  | and φ ψ ihφ ihψ => exact and_congr (ihφ b) (ihψ b)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ b) (ihψ b)
  | all φ ih =>
    have hg : ∀ x : V, (∼(classGuard H _ : SetTheorySemiformula (Option ξ) _)).Eval
        (x :> fun i ↦ (b i).val) (fun y ↦ y.elim a (fun i ↦ (f i).val)) ↔ ¬ H.Evalb ![x, a] := by
      intro x
      rw [← eval_classGuard H a x (fun i ↦ (b i).val) (fun i ↦ (f i).val)]
      simp
    change (∀ x : V, (∼(classGuard H _)).Eval (x :> fun i ↦ (b i).val) (fun y ↦ y.elim a (fun i ↦ (f i).val)) ∨
        (relativizeClass H φ).Eval (x :> fun i ↦ (b i).val) (fun y ↦ y.elim a (fun i ↦ (f i).val))) ↔
      ∀ x : ClassDomain (fun x : V ↦ H.Evalb ![x, a]), φ.Eval (x :> b) f
    constructor
    · intro h x
      apply (ih (x :> b)).mp
      rcases h x.val with hx | hx
      · exact ((hg x.val).mp hx x.property).elim
      · simpa only [classDomain_val_vecCons _ x b] using hx
    · intro h x
      by_cases hx : H.Evalb ![x, a]
      · right
        have hh := (ih (⟨x, hx⟩ :> b)).mpr (h ⟨x, hx⟩)
        simpa only [classDomain_val_vecCons _ ⟨x, hx⟩ b] using hh
      · exact Or.inl ((hg x).mpr hx)
  | exs φ ih =>
    change (∃ x : V, (classGuard H _).Eval (x :> fun i ↦ (b i).val) (fun y ↦ y.elim a (fun i ↦ (f i).val)) ∧
        (relativizeClass H φ).Eval (x :> fun i ↦ (b i).val) (fun y ↦ y.elim a (fun i ↦ (f i).val))) ↔
      ∃ x : ClassDomain (fun x : V ↦ H.Evalb ![x, a]), φ.Eval (x :> b) f
    constructor
    · rintro ⟨x, hx, hφ⟩
      rw [eval_classGuard] at hx
      refine ⟨⟨x, hx⟩, (ih (⟨x, hx⟩ :> b)).mp ?_⟩
      simpa only [classDomain_val_vecCons _ ⟨x, hx⟩ b] using hφ
    · rintro ⟨x, hx⟩
      refine ⟨x.val, (eval_classGuard H a x.val _ _).mpr x.property, ?_⟩
      have hh := (ih (x :> b)).mpr hx
      simpa only [classDomain_val_vecCons _ x b] using hh

end ZFVP
