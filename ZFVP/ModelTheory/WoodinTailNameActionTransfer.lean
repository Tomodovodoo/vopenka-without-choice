import ZFVP.ModelTheory.WoodinTailNameActionForcing
import ZFVP.SetTheory.LevyForcingUniqueName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def tailApplicationWitnessFormula : SetTheorySemisentence 5 :=
  f“P R a n p. !(ordinaryForcingTranslation functionValueFormula) P R P P p
    (!assignmentPrependFormula (!(numeralFormula 2))
      (!assignmentPrependFormula (!(numeralFormula 1))
        (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) n)
        (!kpair.π₂.dfn a)) (!kpair.π₁.dfn a))”

@[irreducible] def tailApplicationGraphFormula : SetTheorySemisentence 5 :=
  f“n P R f t. !(levyUniqueNameGraphFormula tailApplicationWitnessFormula) n P R (!kpair.dfn f t)”

def tailFunctionFormula : SetTheorySemisentence 1 := f“f. !IsFunction.dfn f”

@[irreducible] def tailApplicationLawFormula : SetTheorySemisentence 7 :=
  f“P R o f t n p. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingNameFormula P f ∧ !forcingNameFormula P t ∧ p ∈ P ∧
    !tailApplicationGraphFormula n P R f t ∧
    !(ordinaryForcingTranslation tailFunctionFormula) P R P P p
      (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) f) →
    !(ordinaryForcingTranslation functionValueFormula) P R P P p
      (!assignmentPrependFormula (!(numeralFormula 2))
        (!assignmentPrependFormula (!(numeralFormula 1))
          (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) n) t) f)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_tailApplicationWitnessFormula (P R f τ ν p : V) :
    tailApplicationWitnessFormula.Evalb ![P, R, ⟨f, τ⟩ₖ, ν, p] ↔
      p ∈ tailFunctionValueForcing P R f τ ν := by
  simp [tailApplicationWitnessFormula, tailFunctionValueForcing, standardTuple,
    Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  constructor
  · intro h
    exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  · rintro h a b c d e g rfl rfl rfl rfl rfl rfl
    exact h

instance tailApplicationGraphFormula_defined :
    Defined (fun v : Fin 5 → V ↦ v 0 = tailFunctionValueName (v 1) (v 2) (v 3) (v 4))
      tailApplicationGraphFormula := by
  refine ⟨fun v ↦ ?_⟩
  have he := eval_levyUniqueNameGraphFormula tailApplicationWitnessFormula
    (v 0) (v 1) (v 2) ⟨v 3, v 4⟩ₖ (v 4)
    (tailFunctionValueForcing (v 1) (v 2) (v 3)) (by infer_instance)
    (fun ν _ p ↦ eval_tailApplicationWitnessFormula _ _ _ _ ν p)
  simpa [tailApplicationGraphFormula, tailFunctionValueName,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, Semiformula.Evalb] using he

instance tailFunctionFormula_defined :
    Defined (fun v : Fin 1 → V ↦ IsFunction (v 0)) tailFunctionFormula :=
  ⟨fun v ↦ by simp [tailFunctionFormula]⟩

private theorem tail_forall_two_eq {β : Type*} (a b : β) (F : β → β → Prop) :
    (∀ u v, u = a → v = b → F u v) ↔ F a b :=
  ⟨fun h ↦ h a b rfl rfl, fun h u v hu hv ↦ by subst u v; exact h⟩
private theorem tail_forall_three_eq {β : Type*} (a b c : β) (F : β → β → β → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩
private theorem tail_forall_five_eq {β : Type*} (a b c d e : β) (F : β → β → β → β → β → Prop) :
    (∀ u v w x y, u = a → v = b → w = c → x = d → y = e → F u v w x y) ↔ F a b c d e :=
  ⟨fun h ↦ h a b c d e rfl rfl rfl rfl rfl,
    fun h u v w x y hu hv hw hx hy ↦ by subst u v w x y; exact h⟩
private theorem tail_forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

theorem eval_tailApplicationLawFormula (v : Fin 7 → V) :
    tailApplicationLawFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsForcingName (v 0) (v 3) → IsForcingName (v 0) (v 4) → v 6 ∈ v 0 →
        v 5 = tailFunctionValueName (v 0) (v 1) (v 3) (v 4) →
        v 6 ∈ forcingFormula (v 0) (v 1) tailFunctionFormula (standardTuple ![v 3]) →
        v 6 ∈ tailFunctionValueForcing (v 0) (v 1) (v 3) (v 4) (v 5)) := by
  simp [tailApplicationLawFormula, tailFunctionValueForcing, standardTuple,
    Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ, tail_forall_three_eq, tail_forall_five_eq, tail_forall_six_eq]

theorem tailFunctionValueName_forces_countable [Countable V] {P R top p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hp : p ∈ P)
    (f τ : ForcingName P)
    (hf : p ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val])) :
    p ∈ tailFunctionValueForcing P R f.val τ.val (tailFunctionValueName P R f.val τ.val) := by
  apply forcingFormula_of_all_generics hR ht hp functionValueFormula
    ![f, τ, ⟨_, tailFunctionValueName_isName _ _ _ _⟩]
  intro G hG hpG
  let A : ForcingContext V := ⟨P, R, top, G, hR, ht, hG⟩
  have hfun : IsFunction (A.ofName f) := (Defined.eval_iff _).mp
    ((A.formula_truth tailFunctionFormula ![f]).mpr ⟨p, hpG, hf⟩)
  exact (eval_functionValueFormula _).mpr
    ⟨hfun, (A.tailFunctionValueName_value f τ hfun).symm⟩

theorem tailFunctionValueName_forces {P R top p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hp : p ∈ P)
    (f τ : ForcingName P)
    (hf : p ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val])) :
    p ∈ tailFunctionValueForcing P R f.val τ.val (tailFunctionValueName P R f.val τ.val) := by
  have hv : tailApplicationLawFormula.Evalb
      ![P, R, top, f.val, τ.val, tailFunctionValueName P R f.val τ.val, p] :=
    eval_of_countable_zf tailApplicationLawFormula (by
    intro W _ _ _ _ w
    apply (eval_tailApplicationLawFormula w).mpr
    intro hR ht hfn hτn hp hn hf
    rw [hn]
    exact tailFunctionValueName_forces_countable hR ht hp ⟨w 3, hfn⟩ ⟨w 4, hτn⟩ hf)
    ![P, R, top, f.val, τ.val, tailFunctionValueName P R f.val τ.val, p]
  exact (eval_tailApplicationLawFormula
    ![P, R, top, f.val, τ.val, tailFunctionValueName P R f.val τ.val, p]).mp
      hv hR ht f.property τ.property hp rfl hf

theorem tailAction_forcingFormula_congr {P R p : V} {n : ℕ}
    (hR : IsForcingPreorder P R) (φ : SetTheorySemisentence n)
    (v w : Fin n → V) (hp : p ∈ P)
    (he : ∀ i, p ∈ atomicEquality P R (v i) (w i)) :
    p ∈ forcingFormula P R φ (standardTuple v) ↔
      p ∈ forcingFormula P R φ (standardTuple w) :=
  classForcingFormula_congr hR (IsForcingName P) (by definability) φ v w hp he

theorem tailFunctionValueForcing_congr_result {P R p f τ σ ν : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P)
    (he : p ∈ atomicEquality P R σ ν) :
    p ∈ tailFunctionValueForcing P R f τ σ ↔ p ∈ tailFunctionValueForcing P R f τ ν := by
  apply tailAction_forcingFormula_congr hR functionValueFormula ![f, τ, σ] ![f, τ, ν] hp
  intro i
  exact Fin.cases ((atomicEquality_refl hR f).symm ▸ hp)
    (fun j ↦ Fin.cases ((atomicEquality_refl hR τ).symm ▸ hp)
      (fun k ↦ Fin.cases he (fun l ↦ Fin.elim0 l) k) j) i

theorem normalizedTailFunctionValueName_forces {P R top : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (f τ : ForcingName P)
    (hf : top ∈ forcingFormula P R tailFunctionFormula (standardTuple ![f.val])) :
    top ∈ tailFunctionValueForcing P R f.val τ.val
      (normalizedTailFunctionValueName P R top f.val τ.val) := by
  exact (tailFunctionValueForcing_congr_result (f := f.val) (τ := τ.val) hR ht.1
    (forcingLeastRankName_forced_equal hR ht.1
      (tailFunctionValueName_isName P R f.val τ.val))).mp
    (tailFunctionValueName_forces hR ht ht.1 f τ hf)

end ZFVP

