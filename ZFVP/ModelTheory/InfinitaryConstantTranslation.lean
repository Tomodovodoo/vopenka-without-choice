import ZFVP.ModelTheory.InfinitaryKeislerConsistency
import ZFVP.ModelTheory.ConstantExpansion
import ZFVP.ModelTheory.InfinitaryLanguageMap

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
abbrev WithConstants (L : Language.{u}) (C : Type v) := Language.add L (Language.constant C)

namespace ConstantTranslation
variable {L : Language.{u}} {C : Type v}

def term {n : ℕ} (c : C → Semiterm L Empty n) :
    Semiterm (WithConstants L C) Empty n → Semiterm L Empty n
  | .bvar i => .bvar i
  | .fvar i => i.elim
  | .func f ts => match f with
    | .inl f => .func f (fun i ↦ term c (ts i))
    | .inr (.const a) => c a

/-- Constant elimination commutes with compatible bound-variable rewritings. -/
theorem term_rewrite {n m : ℕ} (c : C → Semiterm L Empty n) (d : C → Semiterm L Empty m)
    (w : Rew (WithConstants L C) Empty n Empty m) (v : Rew L Empty n Empty m)
    (hb : ∀ i, term d (w (.bvar i)) = v (.bvar i)) (hc : ∀ a, d a = v (c a))
    (t : Semiterm (WithConstants L C) Empty n) : term d (w t) = v (term c t) := by
  induction t with
  | bvar i => exact hb i
  | fvar i => exact i.elim
  | func f ts ih =>
      rw [Rew.func]
      cases f with
      | inl f =>
          change Semiterm.func f (fun i ↦ term d (w (ts i))) = v (Semiterm.func f (fun i ↦ term c (ts i)))
          rw [Rew.func]
          exact congrArg (Semiterm.func f) (funext ih)
      | inr f => cases f; exact hc _

theorem term_bShift {n} (c : C → Semiterm L Empty n)
    (t : Semiterm (WithConstants L C) Empty n) :
    term (fun a ↦ Rew.bShift (c a)) (Rew.bShift t) = Rew.bShift (term c t) :=
  term_rewrite c _ Rew.bShift Rew.bShift (fun _ ↦ rfl) (fun _ ↦ rfl) t

theorem q_compatible {n m} (c : C → Semiterm L Empty n) (d : C → Semiterm L Empty m)
    (w : Rew (WithConstants L C) Empty n Empty m) (v : Rew L Empty n Empty m)
    (hb : ∀ i, term d (w (.bvar i)) = v (.bvar i)) :
    ∀ i, term (fun a ↦ Rew.bShift (d a)) (w.q (.bvar i)) = v.q (.bvar i) := by
  intro i
  cases i using Fin.cases with
  | zero => simp only [Rew.q_bvar_zero]; rfl
  | succ i => rw [Rew.q_bvar_succ, Rew.q_bvar_succ, term_bShift, hb]

def firstOrder : {n : ℕ} → (C → Semiterm L Empty n) →
    Semisentence (WithConstants L C) n → Semisentence L n
  | _, _, .verum => .verum
  | _, _, .falsum => .falsum
  | _, c, .rel (.inl r) ts => .rel r (fun i ↦ term c (ts i))
  | _, _, .rel (.inr r) _ => r.elim
  | _, c, .nrel (.inl r) ts => .nrel r (fun i ↦ term c (ts i))
  | _, _, .nrel (.inr r) _ => r.elim
  | _, c, .and φ ψ => .and (firstOrder c φ) (firstOrder c ψ)
  | _, c, .or φ ψ => .or (firstOrder c φ) (firstOrder c ψ)
  | _, c, .all φ => .all (firstOrder (fun a ↦ Rew.bShift (c a)) φ)
  | _, c, .exs φ => .exs (firstOrder (fun a ↦ Rew.bShift (c a)) φ)

def formula : {n : ℕ} → (C → Semiterm L Empty n) →
    Formula (WithConstants L C) n → Formula L n
  | _, c, .fo φ => .fo (firstOrder c φ)
  | _, c, .neg φ => .neg (formula c φ)
  | _, c, .conj φ => .conj fun i ↦ formula c (φ i)
  | _, c, .exs φ => .exs (formula (fun a ↦ Rew.bShift (c a)) φ)
  | _, c, .q φ => .q (formula (fun a ↦ Rew.bShift (c a)) φ)

theorem firstOrder_rewrite {n m} (c : C → Semiterm L Empty n) (d : C → Semiterm L Empty m)
    (w : Rew (WithConstants L C) Empty n Empty m) (v : Rew L Empty n Empty m)
    (hb : ∀ i, term d (w (.bvar i)) = v (.bvar i)) (hc : ∀ a, d a = v (c a))
    (φ : Semisentence (WithConstants L C) n) :
    firstOrder d (w ▹ φ) = v ▹ firstOrder c φ := by
  induction φ generalizing m with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
      cases r with
      | inl r =>
          change Semiformula.rel r (fun i ↦ term d (w (ts i))) =
            Semiformula.rel r (fun i ↦ v (term c (ts i)))
          exact congrArg (Semiformula.rel r) (funext fun i ↦ term_rewrite c d w v hb hc (ts i))
      | inr r => exact r.elim
  | nrel r ts =>
      cases r with
      | inl r =>
          change Semiformula.nrel r (fun i ↦ term d (w (ts i))) =
            Semiformula.nrel r (fun i ↦ v (term c (ts i)))
          exact congrArg (Semiformula.nrel r) (funext fun i ↦ term_rewrite c d w v hb hc (ts i))
      | inr r => exact r.elim
  | and φ ψ ihφ ihψ => exact congrArg₂ Semiformula.and (ihφ c d w v hb hc) (ihψ c d w v hb hc)
  | or φ ψ ihφ ihψ => exact congrArg₂ Semiformula.or (ihφ c d w v hb hc) (ihψ c d w v hb hc)
  | all φ ih =>
      apply congrArg Semiformula.all
      apply ih _ _ w.q v.q (q_compatible c d w v hb)
      intro a
      rw [Rew.q_comp_bShift_app, hc]
  | exs φ ih =>
      apply congrArg Semiformula.exs
      apply ih _ _ w.q v.q (q_compatible c d w v hb)
      intro a
      rw [Rew.q_comp_bShift_app, hc]

theorem formula_rewrite {n m} (c : C → Semiterm L Empty n) (d : C → Semiterm L Empty m)
    (w : Rew (WithConstants L C) Empty n Empty m) (v : Rew L Empty n Empty m)
    (hb : ∀ i, term d (w (.bvar i)) = v (.bvar i)) (hc : ∀ a, d a = v (c a))
    (φ : Formula (WithConstants L C) n) :
    formula d (φ.rewrite w) = (formula c φ).rewrite v := by
  induction φ generalizing m with
  | fo φ => exact congrArg Formula.fo (firstOrder_rewrite c d w v hb hc φ)
  | neg φ ih => exact congrArg Formula.neg (ih c d w v hb hc)
  | conj φ ih => exact congrArg Formula.conj (funext fun i ↦ ih i c d w v hb hc)
  | exs φ ih =>
      apply congrArg Formula.exs
      apply ih _ _ w.q v.q (q_compatible c d w v hb)
      intro a
      rw [Rew.q_comp_bShift_app, hc]
  | q φ ih =>
      apply congrArg Formula.q
      apply ih _ _ w.q v.q (q_compatible c d w v hb)
      intro a
      rw [Rew.q_comp_bShift_app, hc]

@[simp] theorem term_lMap {n} (c : C → Semiterm L Empty n) (t : Semiterm L Empty n) :
    term c (t.lMap (Language.Hom.add₁ L (Language.constant C))) = t := by
  induction t with
  | bvar i => rfl
  | fvar i => exact i.elim
  | func f ts ih => exact congrArg (Semiterm.func f) (funext ih)

@[simp] theorem firstOrder_lMap {n} (c : C → Semiterm L Empty n) (φ : Semisentence L n) :
    firstOrder c (φ.lMap (Language.Hom.add₁ L (Language.constant C))) = φ := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r ts => exact congrArg (Semiformula.rel r) (funext fun i ↦ term_lMap c (ts i))
  | nrel r ts => exact congrArg (Semiformula.nrel r) (funext fun i ↦ term_lMap c (ts i))
  | and φ ψ ihφ ihψ => exact congrArg₂ Semiformula.and (ihφ c) (ihψ c)
  | or φ ψ ihφ ihψ => exact congrArg₂ Semiformula.or (ihφ c) (ihψ c)
  | all φ ih => exact congrArg Semiformula.all (ih _)
  | exs φ ih => exact congrArg Semiformula.exs (ih _)

@[simp] theorem formula_lMap {n} (c : C → Semiterm L Empty n) (φ : Formula L n) :
    formula c (φ.lMap (Language.Hom.add₁ L (Language.constant C))) = φ := by
  induction φ with
  | fo φ => exact congrArg Formula.fo (firstOrder_lMap c φ)
  | neg φ ih => exact congrArg Formula.neg (ih c)
  | conj φ ih => exact congrArg Formula.conj (funext fun i ↦ ih i c)
  | exs φ ih => exact congrArg Formula.exs (ih _)
  | q φ ih => exact congrArg Formula.q (ih _)

@[simp] theorem formula_and {n} (c : C → Semiterm L Empty n) (φ ψ : Formula (WithConstants L C) n) :
    formula c (φ.and ψ) = (formula c φ).and (formula c ψ) := by
  change Formula.conj (fun i ↦ formula c (if i = 0 then φ else ψ)) = _
  apply congrArg Formula.conj
  funext i
  split_ifs <;> rfl

@[simp] theorem formula_or {n} (c : C → Semiterm L Empty n) (φ ψ : Formula (WithConstants L C) n) :
    formula c (φ.or ψ) = (formula c φ).or (formula c ψ) := by
  change Formula.neg (formula c ((Formula.neg φ).and (.neg ψ))) = _
  rw [formula_and]
  rfl

@[simp] theorem formula_imp {n} (c : C → Semiterm L Empty n) (φ ψ : Formula (WithConstants L C) n) :
    formula c (φ.imp ψ) = (formula c φ).imp (formula c ψ) := formula_or c (.neg φ) ψ

@[simp] theorem formula_iff {n} (c : C → Semiterm L Empty n) (φ ψ : Formula (WithConstants L C) n) :
    formula c (φ.iff ψ) = (formula c φ).iff (formula c ψ) := by
  simp only [Formula.iff, formula_and, formula_imp]

@[simp] theorem formula_all {n} (c : C → Semiterm L Empty n) (φ : Formula (WithConstants L C) (n + 1)) :
    formula c (Formula.all φ) = Formula.all (formula (fun a ↦ Rew.bShift (c a)) φ) := rfl

@[simp] theorem formula_expandFirstOrder {n} (c : C → Semiterm L Empty n)
    (φ : Semisentence (WithConstants L C) n) :
    formula c (Formula.expandFirstOrder φ) = Formula.expandFirstOrder (firstOrder c φ) := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r ts => cases r with
      | inl r => rfl
      | inr r => exact r.elim
  | nrel r ts => cases r with
      | inl r => rfl
      | inr r => exact r.elim
  | and φ ψ ihφ ihψ => simp only [Formula.expandFirstOrder, firstOrder, formula_and, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp only [Formula.expandFirstOrder, firstOrder, formula_or, ihφ, ihψ]
  | all φ ih => simp only [Formula.expandFirstOrder, firstOrder, formula_all, ih]
  | exs φ ih => exact congrArg Formula.exs (ih _)

theorem substFirst_bShift {n} (s t : Semiterm L Empty n) :
    Rew.subst (Fin.cases s Semiterm.bvar) (Rew.bShift t) = t := by
  have he : (Rew.subst (Fin.cases s Semiterm.bvar)).comp Rew.bShift =
      (Rew.id : Rew L Empty n Empty n) := by
    apply Rew.ext
    · intro i
      simp only [Rew.comp_app, Rew.bShift_bvar, Rew.subst_bvar, Fin.cases_succ, Rew.id_app]
    · intro i
      exact i.elim
  simpa only [Rew.comp_app, Rew.id_app] using congrArg (fun w ↦ w t) he

@[simp] theorem formula_substFirst {n} (c : C → Semiterm L Empty n)
    (t : Semiterm (WithConstants L C) Empty n) (φ : Formula (WithConstants L C) (n + 1)) :
    formula c (φ.substFirst t) =
      (formula (fun a ↦ Rew.bShift (c a)) φ).substFirst (term c t) := by
  simp only [Formula.substFirst, ← Formula.rewrite_subst]
  apply formula_rewrite
  · intro i
    cases i using Fin.cases <;> simp only [Rew.subst_bvar, Fin.cases_zero, Fin.cases_succ]
    rfl
  · intro a
    exact (substFirst_bShift _ _).symm

/-- Interpret the added constants by a specified assignment. -/
@[instance_reducible] def expansion {M : Type*} [Structure L M] (c : C → M) : Structure (WithConstants L C) M :=
  @Structure.add L (Language.constant C) M inferInstance (ZFVP.constStructure c)

theorem term_val {M : Type*} [Structure L M] {n}
    (c : C → Semiterm L Empty n) (t : Semiterm (WithConstants L C) Empty n) (b : Fin n → M) :
    (term c t).val b Empty.elim =
      Semiterm.val (s := expansion (L := L) (fun a ↦ (c a).val b Empty.elim)) b Empty.elim t := by
  induction t with
  | bvar i => rfl
  | fvar i => exact i.elim
  | func f ts ih =>
      cases f with
      | inl f => exact congrArg (Structure.func f) (funext ih)
      | inr f => cases f; rfl

theorem firstOrder_eval {M : Type*} [Structure L M] {n}
    (c : C → Semiterm L Empty n) (φ : Semisentence (WithConstants L C) n) (b : Fin n → M) :
    (firstOrder c φ).Evalb b ↔
      Semiformula.Eval (s := expansion (L := L) (fun a ↦ (c a).val b Empty.elim)) b Empty.elim φ := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r ts =>
      cases r with
      | inl r =>
          apply iff_of_eq
          apply congrArg (Structure.rel r)
          funext i
          exact term_val c (ts i) b
      | inr r => exact r.elim
  | nrel r ts =>
      cases r with
      | inl r =>
          apply not_congr
          apply iff_of_eq
          apply congrArg (Structure.rel r)
          funext i
          exact term_val c (ts i) b
      | inr r => exact r.elim
  | and φ ψ ihφ ihψ => exact and_congr (ihφ c b) (ihψ c b)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ c b) (ihψ c b)
  | all φ ih =>
      apply forall_congr'
      intro x
      have h := ih (fun a ↦ Rew.bShift (c a)) (x :> b)
      have he : (fun a ↦ Semiterm.val (x :> b) Empty.elim (Rew.bShift (c a))) =
          (fun a ↦ Semiterm.val b Empty.elim (c a)) :=
        funext fun a ↦ Semiterm.val_bShift x (c a)
      rw [he] at h
      exact h
  | exs φ ih =>
      apply exists_congr
      intro x
      have h := ih (fun a ↦ Rew.bShift (c a)) (x :> b)
      have he : (fun a ↦ Semiterm.val (x :> b) Empty.elim (Rew.bShift (c a))) =
          (fun a ↦ Semiterm.val b Empty.elim (c a)) :=
        funext fun a ↦ Semiterm.val_bShift x (c a)
      rw [he] at h
      exact h

theorem formula_eval {M : Type*} [Structure L M] {n}
    (c : C → Semiterm L Empty n) (φ : Formula (WithConstants L C) n) (b : Fin n → M) :
    (formula c φ).Eval b ↔
      @Formula.Eval _ M (expansion (L := L) (fun a ↦ (c a).val b Empty.elim)) _ φ b := by
  induction φ with
  | fo φ => exact firstOrder_eval c φ b
  | neg φ ih => exact not_congr (ih c b)
  | conj φ ih => exact forall_congr' (fun i ↦ ih i c b)
  | exs φ ih =>
      apply exists_congr
      intro x
      have h := ih (fun a ↦ Rew.bShift (c a)) (x :> b)
      have he : (fun a ↦ Semiterm.val (x :> b) Empty.elim (Rew.bShift (c a))) =
          (fun a ↦ Semiterm.val b Empty.elim (c a)) :=
        funext fun a ↦ Semiterm.val_bShift x (c a)
      rw [he] at h
      exact h
  | q φ ih =>
      change (¬Set.Countable {x | (formula (fun a ↦ Rew.bShift (c a)) φ).Eval (x :> b)}) ↔ _
      have he : {x | (formula (fun a ↦ Rew.bShift (c a)) φ).Eval (x :> b)} =
          {x | @Formula.Eval _ M (expansion (L := L) (fun a ↦ (c a).val b Empty.elim)) _ φ (x :> b)} := by
        ext x
        have h := ih (fun a ↦ Rew.bShift (c a)) (x :> b)
        have he : (fun a ↦ Semiterm.val (x :> b) Empty.elim (Rew.bShift (c a))) =
            (fun a ↦ Semiterm.val b Empty.elim (c a)) :=
          funext fun a ↦ Semiterm.val_bShift x (c a)
        rw [he] at h
        exact h
      rw [he]
      rfl

end ConstantTranslation
end ZFVP.Infinitary







