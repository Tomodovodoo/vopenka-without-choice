import ZFVP.ModelTheory.ForcingEvaluatedUnion
import ZFVP.ModelTheory.ForcingCompositionName
import ZFVP.SetTheory.WoodinCollapseSeparative

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingSelectedUnionFormula : SetTheorySemisentence 7 :=
  f“n P R o C H f. ∀ s,
    !forcingCompositionNameFormula s P R f (!checkNameFormula o H) →
    !forcingEvaluatedUnionFormula n P R o C s”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingSelectedUnion (P R one C H f : V) : V :=
  forcingEvaluatedUnion P R one C (forcingCompositionName P R f (checkName one H))

private theorem forall_six_eq {T : Type*} (a b c d e f : T) (F : T → T → T → T → T → T → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔
      F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

instance forcingSelectedUnionFormula_defined :
    Defined (fun v : Fin 7 → V ↦ v 0 = forcingSelectedUnion (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
      forcingSelectedUnionFormula :=
  ⟨fun v ↦ by
    simp [forcingSelectedUnionFormula, forcingSelectedUnion]
    simp [Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq]⟩

instance forcingSelectedUnion_definable : Language.DefinableFunction ℒₛₑₜ
    (fun v : Fin 6 → V ↦ forcingSelectedUnion (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  forcingSelectedUnionFormula_defined.to_definable

theorem forcingSelectedUnion_isName (P R one C H f : V) :
    IsForcingName P (forcingSelectedUnion P R one C H f) := forcingEvaluatedUnion_isName _ _ _ _ _

namespace ForcingContext
variable (A : ForcingContext V)

theorem forcingSelectedUnion_value (C : V) (hC : ∀ σ ∈ C, IsForcingName A.P σ)
    (H : V) (f : ForcingName A.P) :
    A.ofName ⟨forcingSelectedUnion A.P A.R A.one C H f.val, forcingSelectedUnion_isName _ _ _ _ _ _⟩ =
      evaluatedUnion (A.evaluationGraph C hC) (compose (A.ofName f) (A.check H)) := by
  let g : ForcingName A.P := ⟨checkName A.one H, checkName_isName A.top.1 H⟩
  let s : ForcingName A.P := ⟨forcingCompositionName A.P A.R f.val g.val,
    forcingCompositionName_isName _ _ _ _⟩
  exact (A.forcingEvaluatedUnion_value C hC s).trans
    (congrArg (evaluatedUnion (A.evaluationGraph C hC)) (A.forcingCompositionName_value f g))

theorem forcingSelectedUnion_eq_union_range {C D H : V}
    (hC : ∀ σ ∈ C, IsForcingName A.P σ) (hH : H ∈ C ^ D)
    (f : ForcingName A.P) {X : A.Model} (hf : A.ofName f ∈ A.check D ^ X) :
    A.ofName ⟨forcingSelectedUnion A.P A.R A.one C H f.val, forcingSelectedUnion_isName _ _ _ _ _ _⟩ =
      ⋃ˢ range (compose (compose (A.ofName f) (A.check H)) (A.evaluationGraph C hC)) := by
  rw [A.forcingSelectedUnion_value C hC H f]
  exact evaluatedUnion_eq_union_compose
    (compose_function hf ((A.check_function_iff H D C).mpr hH)) (A.evaluationGraph_mem_function C hC)

theorem selectedEvaluation_value {C D H d : V}
    (hC : ∀ σ ∈ C, IsForcingName A.P σ) (hH : H ∈ C ^ D)
    (f : A.Model) {X i : A.Model} (hf : f ∈ A.check D ^ X) (hi : i ∈ X)
    (hd : d ∈ D) (he : f ‘ i = A.check d) :
    (compose (compose f (A.check H)) (A.evaluationGraph C hC)) ‘ i =
      A.ofName ⟨H ‘ d, hC _ (function_value_mem hH hd)⟩ := by
  let := IsFunction.of_mem hH
  have hcheck := (A.check_function_iff H D C).mpr hH
  rw [value_compose_of_mem_function (compose_function hf hcheck)
    (A.evaluationGraph_mem_function C hC) hi,
    value_compose_of_mem_function hf hcheck hi, he,
    A.check_value ((domain_eq_of_mem_function hH).symm ▸ hd),
    A.evaluationGraph_value C hC _ (function_value_mem hH hd)]

theorem forcingSelectedUnion_collapse_bound {C D H : V}
    (hC : ∀ σ ∈ C, IsForcingName A.P σ) (hH : H ∈ C ^ D)
    (f : ForcingName A.P) {κ δ α : A.Model} (hf : A.ofName f ∈ A.check D ^ α)
    (hκ : IsRegularCardinal κ) (hα : α ∈ κ) (hDC : InternalDependentChoiceAt α)
    (hs : IsForcingDescending (woodinCollapse κ δ)
      (forcingSeparativeOrder (woodinCollapse κ δ) (woodinCollapseOrder κ δ)) α
      (compose (compose (A.ofName f) (A.check H)) (A.evaluationGraph C hC))) :
    let u := A.ofName ⟨forcingSelectedUnion A.P A.R A.one C H f.val, forcingSelectedUnion_isName _ _ _ _ _ _⟩
    u ∈ woodinCollapse κ δ ∧ ∀ i ∈ α,
      ⟨u, (compose (compose (A.ofName f) (A.check H)) (A.evaluationGraph C hC)) ‘ i⟩ₖ ∈
        woodinCollapseOrder κ δ := by
  dsimp only
  rw [A.forcingSelectedUnion_eq_union_range hC hH f hf]
  let := hκ.1.1
  let := IsOrdinal.of_mem hα
  have hc := compatible_range_of_separative_descending
    (fun p hp ↦ ((mem_woodinCollapse κ δ p).mp hp).2.1) hs
  have hu := woodinCollapse_sequence_union hκ hα hDC hs.1 hc
  refine ⟨hu, fun i hi ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hu, function_value_mem hs.1 hi, ?_⟩⟩
  intro x hx
  exact mem_sUnion_iff.mpr ⟨_, value_mem_range hs.1 hi, hx⟩

end ForcingContext
end ZFVP
