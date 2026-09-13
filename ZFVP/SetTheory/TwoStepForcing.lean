import ZFVP.ModelTheory.ForcedOrderLaws

/-! A set presentation of two-step forcing using the subnames of the named
poset, together with a specified name for its top. Different equivalent names
may give distinct conditions, so the resulting order is a preorder. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingTruthFormula {n : ℕ} (φ : SetTheorySemisentence n) : SetTheorySemisentence 4 :=
  (ordinaryForcingTranslation φ).subst (fun i ↦ .bvar ((![1, 2, 1, 1, 0, 3] : Fin 6 → Fin 4) i))

def tripleForcingTruthFormula (φ : SetTheorySemisentence 3) : SetTheorySemisentence 6 :=
  f“p P R x y z. !(ordinaryForcingTranslation φ) P R P P p
    (!assignmentPrependFormula (!(numeralFormula 2))
      (!assignmentPrependFormula (!(numeralFormula 1))
        (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) z) y) x)”

def twoStepNamesFormula : SetTheorySemisentence 3 :=
  f“N Q t. ∀ z, z ∈ N ↔ z ∈ !domain.dfn Q ∨ z = t”

def twoStepConditionsFormula : SetTheorySemisentence 5 :=
  f“C P R Q t. ∀ z, z ∈ C ↔ z ∈ !prod.dfn P (!twoStepNamesFormula Q t) ∧
    !kpair.π₁.dfn z ∈ !atomicMembershipFormula P R (!kpair.π₂.dfn z) Q”

def twoStepOrderFormula : SetTheorySemisentence 6 :=
  f“T P R Q S t. ∀ z, z ∈ T ↔
    z ∈ !prod.dfn (!twoStepConditionsFormula P R Q t) (!twoStepConditionsFormula P R Q t) ∧
    !kpair.dfn (!kpair.π₁.dfn (!kpair.π₁.dfn z)) (!kpair.π₁.dfn (!kpair.π₂.dfn z)) ∈ R ∧
    !(tripleForcingTruthFormula boundedPairMemberFormula)
      (!kpair.π₁.dfn (!kpair.π₁.dfn z)) P R S
      (!kpair.π₂.dfn (!kpair.π₁.dfn z)) (!kpair.π₂.dfn (!kpair.π₂.dfn z))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingTruthFormula_defined {n : ℕ} (φ : SetTheorySemisentence n) :
    ℒₛₑₜ-relation₄[V] (fun p P R b ↦ p ∈ forcingFormula P R φ b) via forcingTruthFormula φ :=
  ⟨fun v ↦ by simp [forcingTruthFormula, Semiformula.eval_substs]⟩

instance forcingTruth_definable {n : ℕ} (φ : SetTheorySemisentence n) :
    ℒₛₑₜ-relation₄[V] (fun p P R b ↦ p ∈ forcingFormula P R φ b) :=
  (forcingTruthFormula_defined φ).to_definable

instance tripleForcingTruthFormula_defined (φ : SetTheorySemisentence 3) :
    Defined (fun v : Fin 6 → V ↦ v 0 ∈ forcingFormula (v 1) (v 2) φ
      (standardTuple ![v 3, v 4, v 5])) (tripleForcingTruthFormula φ) :=
  ⟨fun v ↦ by
    simp [tripleForcingTruthFormula, standardTuple, Semiformula.eval_nestFormulae,
      Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
    constructor
    · intro h
      exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    · intro h
      rintro a b c d e f rfl rfl rfl rfl rfl rfl
      exact h⟩

noncomputable def twoStepNames (Q t : V) : V := domain Q ∪ {t}

noncomputable def twoStepConditions (P R Q t : V) : V :=
  {z ∈ P ×ˢ twoStepNames Q t ; kpair.π₁ z ∈ atomicMembership P R (kpair.π₂ z) Q}

noncomputable def twoStepOrder (P R Q S t : V) : V :=
  {z ∈ twoStepConditions P R Q t ×ˢ twoStepConditions P R Q t ;
    ⟨kpair.π₁ (kpair.π₁ z), kpair.π₁ (kpair.π₂ z)⟩ₖ ∈ R ∧
    kpair.π₁ (kpair.π₁ z) ∈ forcingFormula P R boundedPairMemberFormula
      (standardTuple ![S, kpair.π₂ (kpair.π₁ z), kpair.π₂ (kpair.π₂ z)])}

instance twoStepNamesFormula_defined : ℒₛₑₜ-function₂[V] twoStepNames via twoStepNamesFormula :=
  ⟨fun v ↦ by
    change twoStepNamesFormula.Evalb v ↔ v 0 = twoStepNames (v 1) (v 2)
    rw [mem_ext_iff]
    simp [twoStepNamesFormula, twoStepNames]⟩

instance twoStepNames_definable : ℒₛₑₜ-function₂[V] twoStepNames := twoStepNamesFormula_defined.to_definable

instance twoStepConditionsFormula_defined : ℒₛₑₜ-function₄[V] twoStepConditions via twoStepConditionsFormula :=
  ⟨fun v ↦ by
    change twoStepConditionsFormula.Evalb v ↔ v 0 = twoStepConditions (v 1) (v 2) (v 3) (v 4)
    rw [mem_ext_iff]
    simp [twoStepConditionsFormula, twoStepConditions]⟩

instance twoStepConditions_definable : ℒₛₑₜ-function₄[V] twoStepConditions :=
  twoStepConditionsFormula_defined.to_definable

private theorem forall_six_eq {α : Type*} (a b c d e f : α) (F : α → α → α → α → α → α → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

instance twoStepOrderFormula_defined : ℒₛₑₜ-function₅[V] twoStepOrder via twoStepOrderFormula :=
  ⟨fun v ↦ by
    change twoStepOrderFormula.Evalb v ↔ v 0 = twoStepOrder (v 1) (v 2) (v 3) (v 4) (v 5)
    rw [mem_ext_iff]
    simp [twoStepOrderFormula, twoStepOrder, Semiformula.eval_nestFormulae,
      Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq]⟩

instance twoStepOrder_definable :
    Language.DefinableFunction ℒₛₑₜ (fun v : Fin 5 → V ↦ twoStepOrder (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  twoStepOrderFormula_defined.to_definable

theorem kpair_mem_twoStepConditions (P R Q t p τ : V) :
    ⟨p, τ⟩ₖ ∈ twoStepConditions P R Q t ↔
      p ∈ P ∧ τ ∈ twoStepNames Q t ∧ p ∈ atomicMembership P R τ Q := by
  simp [twoStepConditions, and_assoc]

theorem mem_twoStepConditions (P R Q t z : V) :
    z ∈ twoStepConditions P R Q t ↔ ∃ p ∈ P, ∃ τ ∈ twoStepNames Q t,
      z = ⟨p, τ⟩ₖ ∧ p ∈ atomicMembership P R τ Q := by
  constructor
  · intro hz
    obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    exact ⟨p, hp, τ, hτ, rfl, (kpair_mem_twoStepConditions _ _ _ _ _ _).mp hz |>.2.2⟩
  · rintro ⟨p, hp, τ, hτ, rfl, hm⟩
    exact (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hp, hτ, hm⟩

theorem kpair_mem_twoStepOrder (P R Q S t a b : V) :
    ⟨a, b⟩ₖ ∈ twoStepOrder P R Q S t ↔
      a ∈ twoStepConditions P R Q t ∧ b ∈ twoStepConditions P R Q t ∧
      ⟨kpair.π₁ a, kpair.π₁ b⟩ₖ ∈ R ∧
      kpair.π₁ a ∈ forcingFormula P R boundedPairMemberFormula
        (standardTuple ![S, kpair.π₂ a, kpair.π₂ b]) := by
  simp [twoStepOrder, and_assoc]

structure IsForcingIterand (P R Q S t : V) : Prop where
  posetName : IsForcingName P Q
  orderName : IsForcingName P S
  topName : IsForcingName P t
  preorder : ∀ p ∈ P, p ∈ forcingFormula P R forcingPreorderFormula (standardTuple ![Q, S])
  top : ∀ p ∈ P, p ∈ forcingFormula P R forcingTopFormula (standardTuple ![Q, S, t])

theorem IsForcingIterand.name {P R Q S t τ : V} (h : IsForcingIterand P R Q S t)
    (hτ : τ ∈ twoStepNames Q t) : IsForcingName P τ := by
  rcases mem_union_iff.mp hτ with hτ | hτ
  · obtain ⟨p, hp⟩ := mem_domain_iff.mp hτ
    exact forcingName_subname h.posetName hp
  · exact (mem_singleton_iff.mp hτ).symm ▸ h.topName

theorem twoStep_preorder {P R Q S t one : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t) :
    IsForcingPreorder (twoStepConditions P R Q t) (twoStepOrder P R Q S t) := by
  let q : ForcingName P := ⟨Q, h.posetName⟩
  let s : ForcingName P := ⟨S, h.orderName⟩
  refine ⟨fun z hz ↦ (mem_sep_iff.mp hz).1, ?_, ?_⟩
  · intro a ha
    obtain ⟨p, hp, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
    apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
    refine ⟨ha, ha, ?_, ?_⟩
    · simpa using hR.2.1 p hp
    · simpa using forcedPreorder_refl hR htop hp q s ⟨τ, h.name hτ⟩ (h.preorder p hp) hm
  · intro a ha b hb c hc hab hbc
    obtain ⟨p, hp, τ, hτ, rfl, hmτ⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
    obtain ⟨r, hr, σ, hσ, rfl, hmσ⟩ := (mem_twoStepConditions _ _ _ _ _).mp hb
    obtain ⟨v, hv, υ, hυ, rfl, hmυ⟩ := (mem_twoStepConditions _ _ _ _ _).mp hc
    obtain ⟨_, _, hpr, hτσ⟩ := (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hab
    obtain ⟨_, _, hrv, hσυ⟩ := (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hbc
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hpr hrv hτσ hσυ
    have hpσυ := (forcingFormula_regular hR boundedPairMemberFormula _).2.1 r hσυ p hp hpr
    apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
    refine ⟨ha, hc, ?_, ?_⟩
    · simpa using hR.2.2 p hp r hr v hv hpr hrv
    · simpa using forcedPreorder_trans hR htop hp q s ⟨τ, h.name hτ⟩ ⟨σ, h.name hσ⟩
        ⟨υ, h.name hυ⟩ (h.preorder p hp) hτσ hpσυ

theorem twoStep_section_mem {P R Q S t one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t) (hp : p ∈ P) :
    ⟨p, t⟩ₖ ∈ twoStepConditions P R Q t :=
  (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hp, by simp [twoStepNames],
    forcedTop_mem hR htop hp ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩ ⟨t, h.topName⟩ (h.top p hp)⟩

theorem twoStep_top {P R Q S t one : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t) :
    IsForcingTop (twoStepConditions P R Q t) (twoStepOrder P R Q S t) ⟨one, t⟩ₖ := by
  have ho := twoStep_section_mem hR htop h htop.1
  refine ⟨ho, ?_⟩
  intro a ha
  obtain ⟨p, hp, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
  apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
  refine ⟨ha, ho, ?_, ?_⟩
  · simpa using htop.2 p hp
  · simpa using forcedTop_above hR htop hp ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩ ⟨t, h.topName⟩
      ⟨τ, h.name hτ⟩ (h.top p hp) hm

end ZFVP
