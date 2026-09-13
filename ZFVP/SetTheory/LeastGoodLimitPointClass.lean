import ZFVP.SetTheory.GoodLimitPointClass
import ZFVP.SetTheory.RelativizedSatisfaction

/-! The least good limit point above a given ordinal, as a `Pi_{k+2}` class.

The converse of Bagaria's Theorem 4.12 feeds a `Pi_{k+2}` fragment of Vopenka's principle a family
of structures indexed by an ordinal `r`, where the rank stage attached to `r` is the least good
limit point above `r`. Written directly, minimality is a bounded universal quantifier over the
negation of a `Pi_{k+2}` condition, which is not `Pi_{k+2}`. The fix is to relativize the negative
clause to the stage itself: `satisfiesAtFormula` turns "the domain named by the first variable
satisfies `φ` at the remaining variables" into a single `Pi_1` formula, and a `C(k+2)` stage
computes the `Pi_{k+2}` condition correctly, so the relativized clause says the right thing. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- No good limit point for `a` lies strictly above `r`. Free variables: `r`, `a`. -/
def noGoodLimitAboveFormula (k : ℕ) : SetTheorySemisentence 2 :=
  “r a. ∀ ξ, ¬(r ∈ ξ ∧ !(goodLimitPointFormula k) ξ a)”

/-- `lam` is the least good limit point for the predecessor of `ρ` that lies above `r`.
Free variables: `lam`, `r`, `ρ`; it is used at `ρ = succ α`. -/
def leastGoodLimitPointFormula (k : ℕ) : SetTheorySemisentence 3 :=
  “lam r ρ. ∃ a ∈ ρ, !boundedSuccFormula ρ a ∧ !(goodLimitPointFormula k) lam a ∧ r ∈ lam ∧
    ∀ A, !piOneHierarchyFormula A lam →
      !(satisfiesAtFormula (noGoodLimitAboveFormula k)) A r a”

theorem leastGoodLimitPointFormula_pi (k : ℕ) :
    IsPiFormula (k + 2) (leastGoodLimitPointFormula k) := by
  refine .boundedExs (.bvar 2) ?_
  refine .and (.bounded (boundedSuccFormula_bounded.subst _)) ?_
  refine .and ((goodLimitPointFormula_pi k).subst _) ?_
  refine .and (.bounded (.rel _ _)) ?_
  exact .all (.or ((piOneHierarchyFormula_piOne.subst _).neg.raise.mono (by omega))
    (((satisfiesAtFormula_piOne (noGoodLimitAboveFormula k)).subst _).mono (by omega)))

theorem eval_noGoodLimitAboveFormula {W : Type*} [SetStructure W] (k : ℕ) (r a : W) :
    (noGoodLimitAboveFormula k).Evalb ![r, a] ↔
      ∀ ξ : W, r ∈ ξ → ¬(goodLimitPointFormula k).Evalb ![ξ, a] := by
  simp [noGoodLimitAboveFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Function.comp_def, Matrix.constant_eq_singleton]
  exact forall_congr' fun x ↦ imp_iff_not_or.symm

theorem eval_leastGoodLimitPointFormula_components {W : Type*} [SetStructure W]
    (k : ℕ) (lam r ρ : W) :
    (leastGoodLimitPointFormula k).Evalb ![lam, r, ρ] ↔
      ∃ a ∈ ρ, boundedSuccFormula.Evalb ![ρ, a] ∧ (goodLimitPointFormula k).Evalb ![lam, a] ∧
        r ∈ lam ∧ ∀ A : W, piOneHierarchyFormula.Evalb ![A, lam] →
          (satisfiesAtFormula (noGoodLimitAboveFormula k)).Evalb ![A, r, a] := by
  simp [leastGoodLimitPointFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Function.comp_def, Matrix.constant_eq_singleton]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem succ_inj_ordinal {x y : V} [IsOrdinal x] [IsOrdinal y] (h : succ x = succ y) : x = y := by
  have hx : x ∈ succ y := h ▸ mem_succ_self x
  have hy : y ∈ succ x := h.symm ▸ mem_succ_self y
  rcases mem_succ_iff.mp hx with hxy | hxy
  · exact hxy
  rcases mem_succ_iff.mp hy with hyx | hyx
  · exact hyx.symm
  exact (mem_irrefl x (IsOrdinal.toIsTransitive.mem_trans hxy hyx)).elim

/-- At a `C(k+2)` stage the relativized clause says exactly that no good limit point for `α`
lies between `r` and the stage. -/
theorem eval_satisfiesAt_noGoodLimitAbove {k : ℕ} {α lam r : V} [IsOrdinal α]
    (hcn : Cn (k + 2) lam) (hr : r ∈ lam) (hα : α ∈ lam) :
    (satisfiesAtFormula (noGoodLimitAboveFormula k)).Evalb ![hierarchy lam, r, α] ↔
      ∀ ξ ∈ lam, r ∈ ξ → ¬ IsGoodLimitPoint k α ξ := by
  have := hcn.ordinal
  have := goodLimitPointFormula_defines (V := V) k
  have hs : IsSequenceSupport (hierarchy lam) := ((cn_successor_iff (k + 1) lam).mp hcn).2.support
  let rd : SetDomain (hierarchy lam) := ⟨r, ordinal_subset_hierarchy lam r hr⟩
  let ad : SetDomain (hierarchy lam) := ⟨α, ordinal_subset_hierarchy lam α hα⟩
  have hgood : ∀ ξ : SetDomain (hierarchy lam),
      (goodLimitPointFormula k).Evalb ![ξ, ad] ↔ IsGoodLimitPoint k α ξ.val := by
    intro ξ
    have h := hcn.defined_correct (goodLimitPointFormula_pi k)
      (fun v : Fin 2 → V ↦ IsGoodLimitPoint k (v 1) (v 0)) ![ξ, ad]
    simpa using h
  have hvec : (hierarchy lam :> fun i ↦ ((![rd, ad] : Fin 2 → SetDomain (hierarchy lam)) i).val)
      = ![hierarchy lam, r, α] := by
    funext i
    refine Fin.cases rfl (fun j ↦ ?_) i
    exact Fin.cases rfl (fun l ↦ Fin.cases rfl (fun s ↦ Fin.elim0 s) l) j
  rw [← hvec, eval_satisfiesAtFormula _ _ hs, eval_noGoodLimitAboveFormula]
  constructor
  · intro h ξ hξ hrξ hg
    exact h ⟨ξ, ordinal_subset_hierarchy lam ξ hξ⟩ hrξ ((hgood _).mpr hg)
  · intro h ξ hrξ hg
    have hgv : IsGoodLimitPoint k α ξ.val := (hgood ξ).mp hg
    have : IsOrdinal ξ.val := hgv.cn.ordinal
    exact h ξ.val (ordinal_mem_hierarchy_iff.mp ξ.property) hrξ hgv

theorem leastGoodLimitPointFormula_sound {k : ℕ} {α lam r : V} [IsOrdinal α]
    (hαlam : α ∈ lam)
    (h : (leastGoodLimitPointFormula k).Evalb ![lam, r, succ α]) :
    IsGoodLimitPoint k α lam ∧ r ∈ lam ∧ ∀ ξ ∈ lam, r ∈ ξ → ¬ IsGoodLimitPoint k α ξ := by
  have := goodLimitPointFormula_defines (V := V) k
  rw [eval_leastGoodLimitPointFormula_components] at h
  obtain ⟨a, ha, hsucc, hgl, hrlam, hrel⟩ := h
  have : IsOrdinal a := IsOrdinal.of_mem ha
  have hsucc' : succ α = succ a := by
    simpa using (Defined.eval_iff (R := fun v : Fin 2 → V ↦ v 0 = succ (v 1)) ![succ α, a]).mp hsucc
  have hae : a = α := (succ_inj_ordinal hsucc').symm
  subst hae
  have hglp : IsGoodLimitPoint k a lam := by
    simpa using (Defined.eval_iff
      (R := fun v : Fin 2 → V ↦ IsGoodLimitPoint k (v 1) (v 0)) ![lam, a]).mp hgl
  have : IsOrdinal lam := hglp.cn.ordinal
  have hrelH := hrel (hierarchy lam) ((eval_piOneHierarchyFormula _ _).mpr ⟨inferInstance, rfl⟩)
  exact ⟨hglp, hrlam,
    (eval_satisfiesAt_noGoodLimitAbove hglp.cn hrlam hαlam).mp hrelH⟩

theorem leastGoodLimitPointFormula_complete {k : ℕ} {α lam r : V} [IsOrdinal α]
    (hαlam : α ∈ lam) (hlam : IsGoodLimitPoint k α lam) (hr : r ∈ lam)
    (hleast : ∀ ξ ∈ lam, r ∈ ξ → ¬ IsGoodLimitPoint k α ξ) :
    (leastGoodLimitPointFormula k).Evalb ![lam, r, succ α] := by
  have := goodLimitPointFormula_defines (V := V) k
  have : IsOrdinal lam := hlam.cn.ordinal
  rw [eval_leastGoodLimitPointFormula_components]
  refine ⟨α, mem_succ_self α, ?_, ?_, hr, ?_⟩
  · show boundedSuccFormula.Evalb ![succ α, α]
    simp
  · show (goodLimitPointFormula k).Evalb ![lam, α]
    simpa using hlam
  · intro A hA
    obtain ⟨-, rfl⟩ := (eval_piOneHierarchyFormula A lam).mp hA
    exact (eval_satisfiesAt_noGoodLimitAbove hlam.cn hr hαlam).mpr hleast

theorem leastGoodLimitPointFormula_functional {k : ℕ} {α lam₁ lam₂ r : V} [IsOrdinal α]
    (hα₁ : α ∈ lam₁) (hα₂ : α ∈ lam₂)
    (h₁ : (leastGoodLimitPointFormula k).Evalb ![lam₁, r, succ α])
    (h₂ : (leastGoodLimitPointFormula k).Evalb ![lam₂, r, succ α]) : lam₁ = lam₂ := by
  obtain ⟨hg₁, hr₁, hm₁⟩ := leastGoodLimitPointFormula_sound hα₁ h₁
  obtain ⟨hg₂, hr₂, hm₂⟩ := leastGoodLimitPointFormula_sound hα₂ h₂
  have : IsOrdinal lam₁ := hg₁.cn.ordinal
  have : IsOrdinal lam₂ := hg₂.cn.ordinal
  rcases IsOrdinal.mem_trichotomy lam₁ lam₂ with h | h | h
  · exact absurd hg₁ (hm₂ lam₁ h hr₁)
  · exact h
  · exact absurd hg₂ (hm₁ lam₂ h hr₂)

end ZFVP
