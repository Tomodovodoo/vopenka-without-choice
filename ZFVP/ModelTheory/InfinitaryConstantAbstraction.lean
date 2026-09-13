import ZFVP.ModelTheory.InfinitaryConstantDerivation

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace ConstantAbstraction
variable {L : Language} {C : Type*}

/-- Reserve the last free variable for the added constants. -/
def term {n} (t : Semiterm (WithConstants L C) Empty n) : Semiterm L Empty (n + 1) :=
  ConstantTranslation.term (fun _ ↦ .bvar (Fin.last n)) (Rew.map Fin.castSucc id t)

def formula {n} (φ : Formula (WithConstants L C) n) : Formula L (n + 1) :=
  ConstantTranslation.formula (fun _ ↦ .bvar (Fin.last n)) (φ.rename Fin.castSucc)

theorem lift_castSucc {n} : liftRenaming (Fin.castSucc : Fin n → Fin (n + 1)) = Fin.castSucc := by
  funext i
  cases i using Fin.cases <;> rfl

theorem shift_last {n} :
    (fun _ : C ↦ Rew.bShift (.bvar (Fin.last n) : Semiterm L Empty (n + 1))) =
      fun _ ↦ (.bvar (Fin.last (n + 1)) : Semiterm L Empty (n + 1 + 1)) := rfl

@[simp] theorem formula_neg {n} (φ : Formula (WithConstants L C) n) :
    formula (.neg φ) = .neg (formula φ) := rfl
@[simp] theorem formula_conj {n} (φ : ℕ → Formula (WithConstants L C) n) :
    formula (.conj φ) = .conj (fun i ↦ formula (φ i)) := rfl
@[simp] theorem formula_exs {n} (φ : Formula (WithConstants L C) (n + 1)) :
    formula (.exs φ) = .exs (formula φ) := by
  simp only [formula, Formula.rename, ConstantTranslation.formula, lift_castSucc, shift_last]
@[simp] theorem formula_q {n} (φ : Formula (WithConstants L C) (n + 1)) :
    formula (.q φ) = .q (formula φ) := by
  simp only [formula, Formula.rename, ConstantTranslation.formula, lift_castSucc, shift_last]
@[simp] theorem formula_all {n} (φ : Formula (WithConstants L C) (n + 1)) :
    formula (Formula.all φ) = Formula.all (formula φ) := by simp only [Formula.all, formula_neg, formula_exs]
@[simp] theorem formula_and {n} (φ ψ : Formula (WithConstants L C) n) :
    formula (φ.and ψ) = (formula φ).and (formula ψ) := by
  change Formula.conj (fun i ↦ formula (if i = 0 then φ else ψ)) = _
  apply congrArg Formula.conj
  funext i
  split_ifs <;> rfl
@[simp] theorem formula_or {n} (φ ψ : Formula (WithConstants L C) n) :
    formula (φ.or ψ) = (formula φ).or (formula ψ) := by simp only [Formula.or, formula_neg, formula_and]
@[simp] theorem formula_imp {n} (φ ψ : Formula (WithConstants L C) n) :
    formula (φ.imp ψ) = (formula φ).imp (formula ψ) := by simp only [Formula.imp, formula_or, formula_neg]
@[simp] theorem formula_iff {n} (φ ψ : Formula (WithConstants L C) n) :
    formula (φ.iff ψ) = (formula φ).iff (formula ψ) := by simp only [Formula.iff, formula_and, formula_imp]

theorem lMap_rename {K : Language} (η : L →ᵥ K) {n m} (ρ : Fin n → Fin m) (φ : Formula L n) :
    (φ.lMap η).rename ρ = (φ.rename ρ).lMap η := by
  induction φ generalizing m with
  | fo φ => exact congrArg Formula.fo (Semiformula.lMap_map ρ id φ).symm
  | neg φ ih => exact congrArg Formula.neg (ih ρ)
  | conj φ ih => exact congrArg Formula.conj (funext fun i ↦ ih i ρ)
  | exs φ ih => exact congrArg Formula.exs (ih (liftRenaming ρ))
  | q φ ih => exact congrArg Formula.q (ih (liftRenaming ρ))

@[simp] theorem formula_lMap {n} (φ : Formula L n) :
    formula (φ.lMap (Language.Hom.add₁ L (Language.constant C))) = φ.rename Fin.castSucc := by
  unfold formula
  rw [lMap_rename, ConstantTranslation.formula_lMap]

/-- Extend a substitution by fixing the reserved last variable. -/
def liftLast {K : Language} {n m} (σ : Fin n → Semiterm K Empty m) :
    Fin (n + 1) → Semiterm K Empty (m + 1) :=
  Fin.lastCases (.bvar (Fin.last m)) (fun i ↦ Rew.map Fin.castSucc id (σ i))

@[simp] theorem liftLast_last {K : Language} {n m} (σ : Fin n → Semiterm K Empty m) :
    liftLast σ (Fin.last n) = .bvar (Fin.last m) := by simp [liftLast]
@[simp] theorem liftLast_castSucc {K : Language} {n m} (σ : Fin n → Semiterm K Empty m) (i : Fin n) :
    liftLast σ i.castSucc = Rew.map Fin.castSucc id (σ i) := by simp [liftLast]

theorem rename_subst {K : Language} {n m} (σ : Fin n → Semiterm K Empty m) (φ : Formula K n) :
    (φ.subst σ).rename Fin.castSucc = (φ.rename Fin.castSucc).subst (liftLast σ) := by
  simp only [← Formula.rewrite_map, ← Formula.rewrite_subst, Formula.rewrite_comp]
  congr 1
  apply Rew.ext
  · intro i
    simp only [Rew.comp_app, Rew.subst_bvar, Rew.map_bvar, liftLast_castSucc]
  · intro i; exact i.elim

theorem formula_subst {n m} (σ : Fin n → Semiterm (WithConstants L C) Empty m)
    (φ : Formula (WithConstants L C) n) :
    formula (φ.subst σ) = (formula φ).subst
      (Fin.lastCases (.bvar (Fin.last m)) (fun i ↦ term (σ i))) := by
  unfold formula
  rw [rename_subst, ← Formula.rewrite_subst, ← Formula.rewrite_subst]
  apply ConstantTranslation.formula_rewrite
  · intro i
    cases i using Fin.lastCases with
    | last => simp only [Rew.subst_bvar, liftLast_last, Fin.lastCases_last]; rfl
    | cast i => simp only [Rew.subst_bvar, liftLast_castSucc, Fin.lastCases_castSucc]; rfl
  · intro a
    simp only [Rew.subst_bvar, Fin.lastCases_last]

@[simp] theorem term_bvar {n} (i : Fin n) : term (L := L) (C := C) (.bvar i) = .bvar i.castSucc := rfl

theorem formula_rename {n m} (ρ : Fin n → Fin m) (φ : Formula (WithConstants L C) n) :
    formula (φ.rename ρ) = (formula φ).rename (Fin.lastCases (Fin.last m) (fun i ↦ (ρ i).castSucc)) := by
  rw [← Formula.subst_bvar_eq_rename, formula_subst, ← Formula.subst_bvar_eq_rename]
  congr 1
  funext i
  cases i using Fin.lastCases <;> simp only [Fin.lastCases_last, Fin.lastCases_castSucc, term_bvar]

theorem formula_rename_succ {n} (φ : Formula (WithConstants L C) n) :
    formula (φ.rename Fin.succ) = (formula φ).rename Fin.succ := by
  rw [formula_rename]
  congr 1
  funext i
  cases i using Fin.lastCases <;> simp only [Fin.lastCases_last, Fin.lastCases_castSucc] <;> rfl

theorem formula_substFirst {n} (t : Semiterm (WithConstants L C) Empty n)
    (φ : Formula (WithConstants L C) (n + 1)) :
    formula (φ.substFirst t) = (formula φ).substFirst (term t) := by
  simp only [Formula.substFirst, formula_subst]
  congr 1
  funext i
  cases i using Fin.lastCases with
  | last => simp only [Fin.lastCases_last]; rfl
  | cast i =>
      simp only [Fin.lastCases_castSucc]
      cases i using Fin.cases <;> rfl

theorem formula_swapFirstTwo {n} (φ : Formula (WithConstants L C) (n + 2)) :
    formula (φ.swapFirstTwo) = (formula φ).swapFirstTwo := by
  simp only [Formula.swapFirstTwo, formula_rename]
  congr 1
  funext i
  cases i using Fin.lastCases with
  | last => simp only [Fin.lastCases_last]; rfl
  | cast i =>
      simp only [Fin.lastCases_castSucc]
      cases i using Fin.cases with
      | zero => rfl
      | succ i => cases i using Fin.cases <;> rfl

def firstOrder {n} (φ : Semisentence (WithConstants L C) n) : Semisentence L (n + 1) :=
  ConstantTranslation.firstOrder (fun _ ↦ .bvar (Fin.last n)) (Rew.map Fin.castSucc id ▹ φ)

@[simp] theorem formula_fo {n} (φ : Semisentence (WithConstants L C) n) :
    formula (.fo φ) = .fo (firstOrder φ) := rfl

@[simp] theorem firstOrder_all {n} (φ : Semisentence (WithConstants L C) (n + 1)) :
    firstOrder (.all φ) = .all (firstOrder φ) := by
  change Semiformula.all (ConstantTranslation.firstOrder _ ((Rew.map Fin.castSucc id).q ▹ φ)) = _
  rw [Formula.q_map_eq, lift_castSucc]
  rfl

@[simp] theorem firstOrder_exs {n} (φ : Semisentence (WithConstants L C) (n + 1)) :
    firstOrder (.exs φ) = .exs (firstOrder φ) := by
  change Semiformula.exs (ConstantTranslation.firstOrder _ ((Rew.map Fin.castSucc id).q ▹ φ)) = _
  rw [Formula.q_map_eq, lift_castSucc]
  rfl

@[simp] theorem formula_expandFirstOrder {n} (φ : Semisentence (WithConstants L C) n) :
    formula (Formula.expandFirstOrder φ) = Formula.expandFirstOrder (firstOrder φ) := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r ts => cases r with
      | inl r => rfl
      | inr r => exact r.elim
  | nrel r ts => cases r with
      | inl r => rfl
      | inr r => exact r.elim
  | and φ ψ ihφ ihψ =>
      change formula ((Formula.expandFirstOrder φ).and (Formula.expandFirstOrder ψ)) =
        (Formula.expandFirstOrder (firstOrder φ)).and (Formula.expandFirstOrder (firstOrder ψ))
      rw [formula_and, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      change formula ((Formula.expandFirstOrder φ).or (Formula.expandFirstOrder ψ)) =
        (Formula.expandFirstOrder (firstOrder φ)).or (Formula.expandFirstOrder (firstOrder ψ))
      rw [formula_or, ihφ, ihψ]
  | all φ ih => simp only [Formula.expandFirstOrder, firstOrder_all, formula_all, ih]
  | exs φ ih => simp only [Formula.expandFirstOrder, firstOrder_exs, formula_exs, ih]

@[simp] theorem formula_termEqual [L.Eq] {n} (s t : Semiterm (WithConstants L C) Empty n) :
    formula (Formula.termEqual s t) = Formula.termEqual (term s) (term t) := by
  change Formula.fo (.rel Language.Eq.eq (fun i ↦ term (![s, t] i))) = _
  congr 2
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => exact i.elim0

@[simp] theorem formula_equal [L.Eq] {n} (i j : Fin n) :
    formula (C := C) (Formula.equal (L := WithConstants L C) i j) =
      Formula.equal (L := L) i.castSucc j.castSucc := formula_termEqual (.bvar i) (.bvar j)

theorem boolean {n} {Γ : Set (Formula (WithConstants L C) n)}
    {φ : Formula (WithConstants L C) n} (h : BooleanDerivation Γ φ) :
    BooleanDerivation (formula '' Γ) (formula φ) := by
  induction h with
  | hypothesis h => exact .hypothesis ⟨_, h, rfl⟩
  | k φ ψ => simpa only [formula_imp] using BooleanDerivation.k (Γ := formula '' Γ) (formula φ) (formula ψ)
  | s φ ψ χ => simpa only [formula_imp] using BooleanDerivation.s (Γ := formula '' Γ) (formula φ) (formula ψ) (formula χ)
  | dne φ => simpa only [formula_imp, formula_neg] using BooleanDerivation.dne (Γ := formula '' Γ) (formula φ)
  | contraposition φ ψ =>
      simpa only [formula_imp, formula_neg] using BooleanDerivation.contraposition (Γ := formula '' Γ) (formula φ) (formula ψ)
  | projection φ i =>
      simpa only [Formula.countableProjection, formula_imp, formula_conj] using
        BooleanDerivation.projection (Γ := formula '' Γ) (fun i ↦ formula (φ i)) i
  | distribution φ ψ =>
      simpa only [Formula.countableDistribution, formula_imp, formula_conj] using
        BooleanDerivation.distribution (Γ := formula '' Γ) (formula φ) (fun i ↦ formula (ψ i))
  | qMono φ ψ =>
      simpa only [Formula.qMonotonicity, formula_imp, formula_all, formula_q] using
        BooleanDerivation.qMono (Γ := formula '' Γ) (formula φ) (formula ψ)
  | qUnion φ =>
      simpa only [Formula.qCountableUnion, Formula.disj, formula_imp, formula_q, formula_neg, formula_conj] using
        BooleanDerivation.qUnion (Γ := formula '' Γ) (fun i ↦ formula (φ i))
  | mp h₁ h₂ ih₁ ih₂ => exact .mp (by simpa only [formula_imp] using ih₁) ih₂
  | conjunction φ h ih => exact .conjunction _ ih

/-- Abstract all fresh constants without changing the old-language hypotheses. -/
theorem derivation [L.Eq] {Γ : Set (Sentence L)} {n} {φ : Formula (WithConstants L C) n}
    (h : KeislerDerivation (Formula.lMap (Language.Hom.add₁ L (Language.constant C)) '' Γ) φ) :
    KeislerDerivation Γ (formula φ) := by
  induction h with
  | hypothesis h =>
      obtain ⟨ψ, hψ, rfl⟩ := h
      simp only [formula, Formula.rename_closed_rename, lMap_rename, ConstantTranslation.formula_lMap]
      exact .hypothesis hψ
  | boolean h =>
      apply KeislerDerivation.boolean
      simpa only [Set.image_empty] using boolean h
  | truth => exact .truth
  | nonempty => exact .nonempty
  | expansion φ =>
      simpa only [formula_iff, formula_expandFirstOrder, formula_fo] using
        KeislerDerivation.expansion (Γ := Γ) (firstOrder φ)
  | instantiation φ t =>
      simpa only [Formula.universalInstantiation, formula_imp, formula_all, formula_substFirst] using
        KeislerDerivation.instantiation (Γ := Γ) (formula φ) (term t)
  | distribution φ ψ =>
      simpa only [Formula.universalDistribution, formula_imp, formula_all] using
        KeislerDerivation.distribution (Γ := Γ) (formula φ) (formula ψ)
  | exDistribution φ ψ =>
      simpa only [Formula.existentialDistribution, formula_imp, formula_all, formula_exs] using
        KeislerDerivation.exDistribution (Γ := Γ) (formula φ) (formula ψ)
  | vacuous φ =>
      simpa only [Formula.vacuousGeneralization, formula_imp, formula_all, formula_rename_succ] using
        KeislerDerivation.vacuous (Γ := Γ) (formula φ)
  | eqRefl t =>
      simpa only [Formula.equalityReflexivity, formula_termEqual] using
        KeislerDerivation.eqRefl (Γ := Γ) (term t)
  | eqSubst φ s t =>
      simpa only [Formula.equalitySubstitution, formula_imp, formula_iff, formula_termEqual, formula_substFirst] using
        KeislerDerivation.eqSubst (Γ := Γ) (formula φ) (term s) (term t)
  | qSmall i j =>
      simpa only [Formula.qTwoPoints, formula_neg, formula_q, formula_or, formula_equal, Fin.castSucc_zero, Fin.castSucc_succ] using
        KeislerDerivation.qSmall (Γ := Γ) i.castSucc j.castSucc
  | qInterchange φ =>
      simpa only [Formula.qInterchange, formula_imp, formula_or, formula_q, formula_exs,
        formula_swapFirstTwo] using KeislerDerivation.qInterchange (Γ := Γ) (formula φ)
  | mp h₁ h₂ ih₁ ih₂ => exact .mp (by simpa only [formula_imp] using ih₁) ih₂
  | conjunction φ h ih => exact .conjunction _ ih
  | generalization h ih =>
      simpa only [formula_all] using KeislerDerivation.generalization ih
  | substitution σ h ih =>
      rw [formula_subst]
      exact .substitution _ ih

end ConstantAbstraction
end ZFVP.Infinitary







