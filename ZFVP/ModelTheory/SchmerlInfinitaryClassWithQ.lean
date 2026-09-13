import ZFVP.ModelTheory.SchmerlInfinitaryQFree

/-! Construct the fixed class sentence using an arbitrary extensional Q.
Only the two cardinality clauses use Q; branch definitions remain in the
original first-order language. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary (Formula)

variable {L : Language} {M : Type*} [Structure L M]

theorem evalWithQ_cofinalityWitnessClause (Q : Set M → Prop)
    (O D : Formula L 1) (r : Formula L 2) :
    Formula.EvalWithQ Q (cofinalityWitnessClause O D r) ![] ↔
      Q {x | Formula.EvalWithQ Q D ![x]} ∧
      (∀ x, Formula.EvalWithQ Q D ![x] → Formula.EvalWithQ Q O ![x]) ∧
      (∀ a, Formula.EvalWithQ Q O ![a] → ¬Q {x | Formula.EvalWithQ Q D ![x] ∧ Formula.EvalWithQ Q r ![x, a]}) ∧
      (∀ a, Formula.EvalWithQ Q O ![a] → ∃ x, Formula.EvalWithQ Q D ![x] ∧ Formula.EvalWithQ Q r ![a, x]) := by
  simp only [cofinalityWitnessClause, Formula.evalWithQ_and, Formula.evalWithQ_q,
    Formula.evalWithQ_all, Formula.evalWithQ_imp, Formula.evalWithQ_neg, Formula.evalWithQ_exs,
    Formula.evalWithQ_rename, Formula.evalWithQ_swapFirstTwo]
  have he (x a : M) : (x :> a :> ![]) ∘ (fun _ : Fin 1 ↦ (0 : Fin 2)) = ![x] := by
    funext i
    have hi := Fin.eq_zero i
    subst i
    rfl
  simp only [he]

theorem evalWithQ_countableRangeClause (Q : Set M → Prop) (F : Formula L 2) :
    Formula.EvalWithQ Q (countableRangeClause F) ![] ↔
      ¬Q {c | ∃ x, Formula.EvalWithQ Q F ![c, x]} := by
  simp only [countableRangeClause, Formula.evalWithQ_neg, Formula.evalWithQ_q,
    Formula.evalWithQ_exs, Formula.evalWithQ_swapFirstTwo]

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure ClassRankSelectionWithQ (Q : Set W → Prop) (D : W → Prop) : Prop where
  large : Q {x | D x}
  ordinal : ∀ x, D x → IsOrdinal x
  initial : ∀ a : SetTheory.Ordinal W, ¬Q {x | D x ∧ x ⊆ a.val}
  cofinal : ∀ a : SetTheory.Ordinal W, ∃ x, D x ∧ a.val ⊆ x

theorem classTreeSentence_of_semanticDataWithQ (Q : Set W → Prop) (D : W → Prop) (f : W → W)
    (hD : ClassRankSelectionWithQ Q D) (hcount : ¬Q (Set.range f))
    (hweak : ∀ x y z : ClassTreeNode W,
      D x.level.val → D y.level.val → D z.level.val →
      x ≤ y → x ≤ z → f x.code = f y.code → f x.code = f z.code → y ≤ z ∨ z ≤ y)
    (hdefs : @Formula.Eval classLanguage W (classExpansion D f) 0
      (branchDefinabilityClause classLanguageEmbedding (classOriginal classNodeFormula)
        (selectedRankNodes classSelected (classOriginal classRankFormula)) (classOriginal ordinalNodeFormula)
        (classOriginal classOrderFormula) (equalityOfColors classColor)
        (nodeRankAbove (classOriginal classRankFormula) (classOriginal ordinalOrderFormula))) ![]) :
    @Formula.EvalWithQ classLanguage W (classExpansion D f) Q 0 classTreeSentence ![] := by
  classical
  let : Structure classLanguage W := classExpansion D f
  let N := classOriginal classNodeFormula
  let O := classOriginal ordinalNodeFormula
  let r := classOriginal classOrderFormula
  let rO := classOriginal ordinalOrderFormula
  let J := classOriginal classRankFormula
  let selected := selectedRankNodes classSelected J
  let E := equalityOfColors classColor
  let H := nodeRankAbove J rO
  have hN (x : W) : N.Eval ![x] ↔ x ∈ Set.range (ClassTreeNode.code (V := W)) :=
    (eval_classOriginal D f classNodeFormula ![x]).trans (eval_classNodeFormula x)
  have hr (x y : ClassTreeNode W) : r.Eval ![x.code, y.code] ↔ x ≤ y :=
    (eval_classOriginal D f classOrderFormula ![x.code, y.code]).trans (eval_classOrderFormula x y)
  have hJ (x : ClassTreeNode W) (a : W) : J.Eval ![x.code, a] ↔ a = x.level.val :=
    (eval_classOriginal D f classRankFormula ![x.code, a]).trans (eval_classRankFormula x a)
  have hselected (x : ClassTreeNode W) : selected.Eval ![x.code] ↔ D x.level.val := by
    simp only [selected, eval_selectedRankNodes, hJ, eval_classSelected]
    exact ⟨fun ⟨a, ha, he⟩ ↦ he ▸ ha, fun hx ↦ ⟨x.level.val, hx, rfl⟩⟩
  have hE (x y : ClassTreeNode W) : E.Eval ![x.code, y.code] ↔ f x.code = f y.code := by
    simp [E, eval_equalityOfColors, eval_classColor]
  have hO (x : W) : Formula.EvalWithQ Q O ![x] ↔ IsOrdinal x := by
    change ordinalNodeFormula.Evalb ![x] ↔ IsOrdinal x
    simp [ordinalNodeFormula]
  have hD' (x : W) : Formula.EvalWithQ Q classSelected ![x] ↔ D x := Iff.rfl
  have hrO (x y : W) : Formula.EvalWithQ Q rO ![x, y] ↔ x ⊆ y := by
    change ordinalOrderFormula.Evalb ![x, y] ↔ x ⊆ y
    simp [ordinalOrderFormula]
  have hcof : Formula.EvalWithQ Q (cofinalityWitnessClause O classSelected rO) ![] := by
    apply (evalWithQ_cofinalityWitnessClause Q O classSelected rO).mpr
    simpa only [hD', hO, hrO] using
      (show Q {x | D x} ∧ (∀ x, D x → IsOrdinal x) ∧
        (∀ a, IsOrdinal a → ¬Q {x | D x ∧ x ⊆ a}) ∧
        (∀ a, IsOrdinal a → ∃ x, D x ∧ a ⊆ x) from
        ⟨hD.large, hD.ordinal, fun a ha ↦ hD.initial ⟨a, ha⟩, fun a ha ↦ hD.cofinal ⟨a, ha⟩⟩)
  have hcountClause : Formula.EvalWithQ Q (countableRangeClause classColor) ![] := by
    apply (evalWithQ_countableRangeClause Q classColor).mpr
    have he : {c : W | ∃ x, Formula.EvalWithQ Q classColor ![c, x]} = Set.range f := by
      ext c
      exact ⟨fun ⟨x, hx⟩ ↦ ⟨x, hx.symm⟩, fun ⟨x, hx⟩ ↦ ⟨x, hx.symm⟩⟩
    rwa [he]
  have hweakClause : (weakSpecializationClause N selected r E).Eval (M := W) ![] := by
    apply (eval_weakSpecializationClause N selected r E).mpr
    intro x y z hx hy hz hdx hdy hdz hxy hxz hexy hexz
    obtain ⟨x, rfl⟩ := (hN x).mp hx
    obtain ⟨y, rfl⟩ := (hN y).mp hy
    obtain ⟨z, rfl⟩ := (hN z).mp hz
    exact (or_congr (hr y z) (hr z y)).mpr
      (hweak x y z ((hselected x).mp hdx) ((hselected y).mp hdy) ((hselected z).mp hdz)
        ((hr x y).mp hxy) ((hr x z).mp hxz) ((hE x y).mp hexy) ((hE x z).mp hexz))
  have htotal : classColorTotal.Eval (M := W) ![] := by
    apply (eval_classColorTotal (classExpansion D f) rfl).mpr
    exact fun x ↦ ⟨f x, rfl, fun _ he ↦ he⟩
  have hqweak : Formula.QFree (weakSpecializationClause N selected r E) := by
    apply qFree_weakSpecializationClause <;> simp [N, selected, J, r, E]
  have hqdefs : Formula.QFree (branchDefinabilityClause classLanguageEmbedding N selected O r E H) := by
    apply qFree_branchDefinabilityClause <;> simp [N, selected, J, O, r, E, H, rO]
  change Formula.EvalWithQ Q (.and classColorTotal (treeDefinitionSentence _ _ _ _ _ _ _ _)) ![]
  simp only [treeDefinitionSentence, Formula.evalWithQ_and]
  exact ⟨(qFree_classColorTotal.evalWithQ_iff Q ![]).mpr htotal, hcof, hcountClause,
    (hqweak.evalWithQ_iff Q ![]).mpr hweakClause, (hqdefs.evalWithQ_iff Q ![]).mpr hdefs⟩

end ZFVP.Schmerl
