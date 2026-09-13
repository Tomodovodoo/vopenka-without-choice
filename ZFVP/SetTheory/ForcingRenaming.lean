import ZFVP.SetTheory.ClassForcingCongruence

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingTermValue_bShift {n : ℕ} (t : SetTheorySemiterm Empty n)
    (v : Fin n → V) (x : V) :
    forcingTermValue (Rew.bShift t) (standardTuple (x :> v)) = forcingTermValue t (standardTuple v) := by
  cases t with
  | bvar i =>
    change (standardTuple (x :> v)) ‘ (i.succ.val : V) = (standardTuple v) ‘ (i.val : V)
    rw [value_standardTuple, value_standardTuple]
    rfl
  | fvar i => exact Empty.elim i
  | func f _ => exact Empty.elim f

theorem forcingTermValue_rew {n m : ℕ} (ω : Rew ℒₛₑₜ Empty n Empty m)
    (v : Fin m → V) (w : Fin n → V)
    (h : ∀ i, forcingTermValue (ω (.bvar i)) (standardTuple v) = w i)
    (t : SetTheorySemiterm Empty n) :
    forcingTermValue (ω t) (standardTuple v) = forcingTermValue t (standardTuple w) := by
  cases t with
  | bvar i => simpa only [forcingTermValue, value_standardTuple] using h i
  | fvar i => exact Empty.elim i
  | func f _ => exact Empty.elim f

theorem forcingTermValue_q {n m : ℕ} (ω : Rew ℒₛₑₜ Empty n Empty m)
    (v : Fin m → V) (w : Fin n → V)
    (h : ∀ i, forcingTermValue (ω (.bvar i)) (standardTuple v) = w i) (x : V) :
    ∀ i, forcingTermValue (ω.q (.bvar i)) (standardTuple (x :> v)) = (x :> w) i := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change (standardTuple (x :> v)) ‘ ((0 : Fin (m + 1)).val : V) = x
    exact value_standardTuple _ 0
  · simpa only [Rew.q_bvar_succ, forcingTermValue_bShift, Matrix.cons_val_succ] using h j

theorem classForcingFormula_rew (P R : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    {n : ℕ} (φ : SetTheorySemisentence n) {m : ℕ} (ω : Rew ℒₛₑₜ Empty n Empty m)
    (v : Fin m → V) (w : Fin n → V)
    (h : ∀ i, forcingTermValue (ω (.bvar i)) (standardTuple v) = w i) :
    classForcingFormula P R N hN (ω ▹ φ) (standardTuple v) =
      classForcingFormula P R N hN φ (standardTuple w) := by
  induction φ generalizing m with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
    cases r <;> simp only [Semiformula.rew_rel, classForcingFormula_rel, forcingAtomic,
      forcingTermValue_rew ω v w h]
  | nrel r ts =>
    cases r <;> simp only [Semiformula.rew_nrel, classForcingFormula_nrel, forcingAtomic,
      forcingTermValue_rew ω v w h]
  | and φ ψ ihφ ihψ =>
    exact congrArg₂ (fun A B : V ↦ A ∩ B) (ihφ ω v w h) (ihψ ω v w h)
  | or φ ψ ihφ ihψ =>
    exact congrArg₂ (fun A B : V ↦ forcingClosure P R (A ∪ B)) (ihφ ω v w h) (ihψ ω v w h)
  | all φ ih =>
    apply mem_ext
    intro p
    change p ∈ classForcingFormula P R N hN (.all (ω.q ▹ φ)) _ ↔ _
    rw [classForcingFormula_all, classForcingFormula_all,
      mem_forcingClassIntersection_iff, mem_forcingClassIntersection_iff]
    apply and_congr Iff.rfl
    apply forall_congr'
    intro x
    apply imp_congr_right
    intro _
    exact Iff.of_eq (congrArg (fun A ↦ p ∈ A)
      (ih ω.q (x :> v) (x :> w) (forcingTermValue_q ω v w h x)))
  | exs φ ih =>
    apply mem_ext
    intro p
    change p ∈ classForcingFormula P R N hN (.exs (ω.q ▹ φ)) _ ↔ _
    rw [classForcingFormula_exs_dense_iff, classForcingFormula_exs_dense_iff]
    have he (x : V) := ih ω.q (x :> v) (x :> w) (forcingTermValue_q ω v w h x)
    change (p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
      ∃ x, N x ∧ r ∈ classForcingFormula P R N hN (ω.q ▹ φ) (standardTuple (x :> v))) ↔ _
    simp only [he]
    rfl

theorem forcingFormula_rename (P R : V) {n m : ℕ} (φ : SetTheorySemisentence n)
    (r : Fin n → Fin m) (v : Fin m → V) :
    forcingFormula P R (φ.subst (fun i ↦ .bvar (r i))) (standardTuple v) =
      forcingFormula P R φ (standardTuple (fun i ↦ v (r i))) :=
  classForcingFormula_rew P R (IsForcingName P) (by definability) φ
    (Rew.subst (fun i ↦ .bvar (r i))) v (fun i ↦ v (r i)) (by intro i; simp [forcingTermValue])

end ZFVP
