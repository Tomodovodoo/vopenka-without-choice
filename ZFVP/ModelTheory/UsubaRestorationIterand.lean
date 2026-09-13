import ZFVP.ModelTheory.UsubaCollapseNames
import ZFVP.ModelTheory.WoodinSelectorUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def usubaRestorationPosetFormula : SetTheorySemisentence 1 :=
  f“Q. (!choiceFunctionSentence ∧ Q = !singleton.dfn (!isEmpty)) ∨
    (¬!choiceFunctionSentence ∧ !usubaCollapseFormula Q (!woodinSeedCardinalFormula)
      (!hierarchyFormula (!usubaLeastTargetFormula (!woodinSeedCardinalFormula))))”

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def usubaRestorationPoset : V := by
  classical
  exact if InternalChoice V then {∅} else
    usubaCollapse woodinSeedCardinal (hierarchy (usubaLeastTarget woodinSeedCardinal))

instance usubaRestorationPosetFormula_defined :
    ℒₛₑₜ-function₀[V] usubaRestorationPoset via usubaRestorationPosetFormula := by
  refine ⟨fun v ↦ ?_⟩
  classical
  by_cases h : InternalChoice V <;> simp [usubaRestorationPosetFormula, usubaRestorationPoset, h]

theorem usubaRestorationPoset_of_choice (h : InternalChoice V) :
    (usubaRestorationPoset : V) = {∅} := by
  classical
  simp [usubaRestorationPoset, h]

theorem usubaRestorationPoset_of_not_choice (h : ¬InternalChoice V) :
    (usubaRestorationPoset : V) =
      usubaCollapse woodinSeedCardinal (hierarchy (usubaLeastTarget woodinSeedCardinal)) := by
  classical
  simp [usubaRestorationPoset, h]

theorem usubaRestorationPoset_empty_mem : (∅ : V) ∈ (usubaRestorationPoset : V) := by
  classical
  by_cases h : InternalChoice V
  · simp [usubaRestorationPoset_of_choice h]
  · rw [usubaRestorationPoset_of_not_choice h]
    exact empty_mem_usubaCollapse (woodinSeedCardinal_omega_subset _ empty_mem_ω) _

theorem usubaRestorationPoset_top :
    IsForcingTop (usubaRestorationPoset : V) (reverseInclusionOrder usubaRestorationPoset) ∅ :=
  ⟨usubaRestorationPoset_empty_mem, fun p hp ↦
    (pair_mem_reverseInclusionOrder _ _ _).mpr
      ⟨hp, usubaRestorationPoset_empty_mem, empty_subset _⟩⟩

noncomputable def usubaRestorationPosetName (P R : V) : V :=
  formulaUniqueName P R usubaRestorationPosetFormula ∅

instance usubaRestorationPosetName_definable :
    ℒₛₑₜ-function₂[V] usubaRestorationPosetName := by
  have := (formulaUniqueNameFormula_defined (V := V) usubaRestorationPosetFormula).to_definable
  unfold usubaRestorationPosetName
  apply Language.DefinableFunction₃.comp
    (F := fun P R a ↦ formulaUniqueName P R usubaRestorationPosetFormula a) <;> definability

theorem usubaRestorationPosetName_isName (P R : V) :
    IsForcingName P (usubaRestorationPosetName P R) := formulaUniqueName_isName _ _ _ _

theorem usubaRestorationPosetName_forces {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) :
    p ∈ forcingFormula P R usubaRestorationPosetFormula
      (standardTuple ![usubaRestorationPosetName P R]) := by
  apply formulaUniqueName_forces usubaRestorationPosetFormula _ hR htop hp
    (![] : Fin 0 → ForcingName P)
  intro W _ _ _ v
  have ht (x : W) : usubaRestorationPosetFormula.Evalb (x :> v) ↔
      x = usubaRestorationPoset := usubaRestorationPosetFormula_defined.iff _
  exact ⟨_, (ht _).mpr rfl, fun y hy ↦ (ht y).mp hy⟩

theorem usubaRestoration_top_forced {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) :
    p ∈ forcingFormula P R forcingTopFormula
      (standardTuple ![usubaRestorationPosetName P R,
        reverseInclusionOrderName P R (usubaRestorationPosetName P R), forcedEmptyName P R]) := by
  let Q : ForcingName P := ⟨usubaRestorationPosetName P R, usubaRestorationPosetName_isName _ _⟩
  let S : ForcingName P := ⟨reverseInclusionOrderName P R Q.val, reverseInclusionOrderName_isName _ _ _⟩
  let t : ForcingName P := ⟨forcedEmptyName P R, forcedEmptyName_isName _ _⟩
  let φ : SetTheorySemisentence 3 :=
    (usubaRestorationPosetFormula.subst (fun i ↦ .bvar ((![0] : Fin 1 → Fin 3) i))).and
      ((piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 3) i))).and
        (isEmpty.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 3) i))))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![Q.val, S.val, t.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_rename, forcingFormula_rename, forcingFormula_rename]
    exact ⟨usubaRestorationPosetName_forces hR htop hp,
      reverseInclusionOrderName_forces hR htop hp Q, forcedEmptyName_forces hR htop hp⟩
  exact forcingFormula_entailment φ forcingTopFormula (by
    intro W _ _ _ v hv
    change (usubaRestorationPosetFormula.subst (fun i ↦ .bvar ((![0] : Fin 1 → Fin 3) i))).Evalb v ∧
      (piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 3) i))).Evalb v ∧
      (isEmpty.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 3) i))).Evalb v at hv
    have hh : v 0 = usubaRestorationPoset ∧ v 1 = reverseInclusionOrder (v 0) ∧ v 2 = ∅ := by
      simpa [Semiformula.eval_substs] using hv
    have ht : IsForcingTop (v 0) (v 1) (v 2) := by
      rw [hh.2.1, hh.1, hh.2.2]
      exact usubaRestorationPoset_top
    simpa using ht) hR htop hp ![Q, S, t] hφ

theorem usubaRestoration_iterand {P R one : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) :
    IsForcingIterand P R (usubaRestorationPosetName P R)
      (reverseInclusionOrderName P R (usubaRestorationPosetName P R)) (forcedEmptyName P R) where
  posetName := usubaRestorationPosetName_isName _ _
  orderName := reverseInclusionOrderName_isName _ _ _
  topName := forcedEmptyName_isName _ _
  preorder := fun p hp ↦ reverseInclusionOrderName_preorder hR htop hp
    ⟨usubaRestorationPosetName P R, usubaRestorationPosetName_isName _ _⟩
  top := fun p hp ↦ usubaRestoration_top_forced hR htop hp

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def usubaRestorationName : ForcingName A.P :=
  ⟨usubaRestorationPosetName A.P A.R, usubaRestorationPosetName_isName _ _⟩

theorem usubaRestorationName_value :
    A.ofName A.usubaRestorationName = (usubaRestorationPoset : A.Model) := by
  have ht (x : A.Model) : usubaRestorationPosetFormula.Evalb
      (x :> (fun i ↦ A.ofName ((![] : Fin 0 → ForcingName A.P) i))) ↔
        x = usubaRestorationPoset := usubaRestorationPosetFormula_defined.iff _
  exact A.formulaName_value usubaRestorationPosetFormula ![]
    (fun x y hx hy ↦ ((ht x).mp hx).trans ((ht y).mp hy).symm) ((ht _).mpr rfl)

end ForcingContext
end ZFVP
