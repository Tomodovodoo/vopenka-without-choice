import ZFVP.ModelTheory.WoodinPrefixNameRanks

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def woodinPrefixNameBoundsFormula : SetTheorySemisentence 6 :=
  f“P R o κ δ θ. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !choicelessInaccessibleFormula δ ∧ P ∈ !hierarchyFormula δ ∧ κ ⊆ δ ∧
    !choicelessInaccessibleFormula θ ∧ δ ∈ θ → ∀ Q S t,
      !woodinPrefixPosetNameFormula Q P R o κ δ ∧ !reverseInclusionOrderNameFormula S P R Q ∧
        !forcedEmptyNameFormula t P R → Q ∈ !hierarchyFormula θ ∧ S ∈ !hierarchyFormula θ ∧
          t ∈ !hierarchyFormula θ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem forall_three_eq {α : Type*} (a b c : α) (F : α → α → α → Prop) :
    (∀ x y z, x = a → y = b → z = c → F x y z) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, by rintro h x y z rfl rfl rfl; exact h⟩
private theorem forall_four_eq {α : Type*} (a b c d : α) (F : α → α → α → α → Prop) :
    (∀ x y z u, x = a → y = b → z = c → u = d → F x y z u) ↔ F a b c d :=
  ⟨fun h ↦ h a b c d rfl rfl rfl rfl, by rintro h x y z u rfl rfl rfl rfl; exact h⟩
private theorem forall_six_eq {α : Type*} (a b c d e f : α) (F : α → α → α → α → α → α → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔
      F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    by rintro h u v w x y z rfl rfl rfl rfl rfl rfl; exact h⟩

theorem eval_woodinPrefixNameBoundsFormula (v : Fin 6 → V) :
    woodinPrefixNameBoundsFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsChoicelessInaccessible (v 4) → v 0 ∈ hierarchy (v 4) → v 3 ⊆ v 4 →
        IsChoicelessInaccessible (v 5) → v 4 ∈ v 5 →
        woodinPrefixPosetName (v 0) (v 1) (v 2) (v 3) (v 4) ∈ hierarchy (v 5) ∧
        woodinPrefixOrderName (v 0) (v 1) (v 2) (v 3) (v 4) ∈ hierarchy (v 5) ∧
        forcedEmptyName (v 0) (v 1) ∈ hierarchy (v 5)) := by
  simp [woodinPrefixNameBoundsFormula, woodinPrefixOrderName, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ,
    forall_three_eq, forall_four_eq, forall_six_eq]
  constructor
  · intro h hR ht hd hp hk hθ hdθ
    exact h hR ht hd hp hk hθ hdθ _ _ _ rfl rfl rfl
  · intro h hR ht hd hp hk hθ hdθ Q S t hQ hS ht'
    subst Q S t
    exact h hR ht hd hp hk hθ hdθ

theorem woodinPrefixNameBounds_countable [Countable V] (v : Fin 6 → V) :
    woodinPrefixNameBoundsFormula.Evalb v := by
  apply (eval_woodinPrefixNameBoundsFormula v).mpr
  intro hR ht hδ hP hκ hθ hδθ
  let := hδ.1
  let := hθ.1
  exact ⟨woodinPrefixPosetName_mem_hierarchy_countable hR ht hδ hP hκ hθ hδθ,
    woodinPrefixOrderName_mem_hierarchy_countable hR ht hδ hP hκ hθ hδθ,
    forcedEmptyName_mem_hierarchy_countable hR ht hθ
      (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hδθ) _ hP)⟩

theorem woodinPrefixNameBounds_valid (v : Fin 6 → V) : woodinPrefixNameBoundsFormula.Evalb v :=
  eval_of_countable_zf woodinPrefixNameBoundsFormula (fun _W _ _ _ _ w ↦ woodinPrefixNameBounds_countable w) v

theorem woodinPrefix_names_mem_hierarchy {P R one κ δ θ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκ : κ ⊆ δ)
    (hθ : IsChoicelessInaccessible θ) (hδθ : δ ∈ θ) :
    woodinPrefixPosetName P R one κ δ ∈ hierarchy θ ∧
      woodinPrefixOrderName P R one κ δ ∈ hierarchy θ ∧ forcedEmptyName P R ∈ hierarchy θ :=
  (eval_woodinPrefixNameBoundsFormula ![P, R, one, κ, δ, θ]).mp
    (woodinPrefixNameBounds_valid ![P, R, one, κ, δ, θ]) hR htop hδ hP hκ hθ hδθ

end ZFVP
