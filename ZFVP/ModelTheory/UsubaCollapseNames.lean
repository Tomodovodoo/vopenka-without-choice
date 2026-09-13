import ZFVP.SetTheory.UsubaLeastTarget
import ZFVP.SetTheory.UsubaCollapse
import ZFVP.SetTheory.UniformFormulaName
import ZFVP.ModelTheory.WoodinSuccessorIterand

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def usubaCollapseFormula : SetTheorySemisentence 3 :=
  f“Q κ S. ∀ p, p ∈ Q ↔ p ⊆ !prod.dfn κ S ∧
    !IsFunction.dfn p ∧ !cardinalSmallFormula κ (!domain.dfn p)”

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance usubaCollapseFormula_defined :
    ℒₛₑₜ-function₂[V] usubaCollapse via usubaCollapseFormula := by
  refine ⟨fun v ↦ ?_⟩
  change usubaCollapseFormula.Evalb v ↔ v 0 = usubaCollapse (v 1) (v 2)
  rw [mem_ext_iff]
  simp [usubaCollapseFormula, mem_usubaCollapse]

noncomputable def usubaCollapseName (P R κ S : V) : V :=
  formulaUniqueName P R usubaCollapseFormula (standardTuple ![κ, S])

noncomputable def usubaTargetName (P R κ : V) : V :=
  formulaUniqueName P R usubaLeastTargetFormula (standardTuple ![κ])

noncomputable def usubaHierarchyName (P R α : V) : V :=
  formulaUniqueName P R hierarchyFormula (standardTuple ![α])

instance usubaCollapseName_definable : ℒₛₑₜ-function₄[V] usubaCollapseName := by
  have := (formulaUniqueNameFormula_defined (V := V) usubaCollapseFormula).to_definable
  unfold usubaCollapseName
  apply Language.DefinableFunction₃.comp (F := fun P R a ↦ formulaUniqueName P R usubaCollapseFormula a)
  · definability
  · definability
  · simp only [standardTuple]
    definability

instance usubaTargetName_definable : ℒₛₑₜ-function₃[V] usubaTargetName := by
  have := (formulaUniqueNameFormula_defined (V := V) usubaLeastTargetFormula).to_definable
  unfold usubaTargetName
  apply Language.DefinableFunction₃.comp (F := fun P R a ↦ formulaUniqueName P R usubaLeastTargetFormula a)
  · definability
  · definability
  · simp only [standardTuple]
    definability

instance usubaHierarchyName_definable : ℒₛₑₜ-function₃[V] usubaHierarchyName := by
  have := (formulaUniqueNameFormula_defined (V := V) hierarchyFormula).to_definable
  unfold usubaHierarchyName
  apply Language.DefinableFunction₃.comp (F := fun P R a ↦ formulaUniqueName P R hierarchyFormula a)
  · definability
  · definability
  · simp only [standardTuple]
    definability

theorem usubaCollapseName_isName (P R κ S : V) :
    IsForcingName P (usubaCollapseName P R κ S) := formulaUniqueName_isName _ _ _ _

theorem usubaTargetName_isName (P R κ : V) :
    IsForcingName P (usubaTargetName P R κ) := formulaUniqueName_isName _ _ _ _

theorem usubaHierarchyName_isName (P R α : V) :
    IsForcingName P (usubaHierarchyName P R α) := formulaUniqueName_isName _ _ _ _

theorem usubaCollapseName_forces {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (κ S : ForcingName P) :
    p ∈ forcingFormula P R usubaCollapseFormula
      (standardTuple ![usubaCollapseName P R κ.val S.val, κ.val, S.val]) := by
  apply formulaUniqueName_forces usubaCollapseFormula _ hR htop hp ![κ, S]
  intro W _ _ _ v
  have ht (x : W) : usubaCollapseFormula.Evalb (x :> v) ↔
      x = usubaCollapse (v 0) (v 1) := usubaCollapseFormula_defined.iff _
  exact ⟨_, (ht _).mpr rfl, fun y hy ↦ (ht y).mp hy⟩

theorem usubaTargetName_forces {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (κ : ForcingName P) :
    p ∈ forcingFormula P R usubaLeastTargetFormula
      (standardTuple ![usubaTargetName P R κ.val, κ.val]) := by
  apply formulaUniqueName_forces usubaLeastTargetFormula _ hR htop hp ![κ]
  intro W _ _ _ v
  have ht (x : W) : usubaLeastTargetFormula.Evalb (x :> v) ↔
      x = usubaLeastTarget (v 0) := usubaLeastTargetFormula_defined.iff _
  exact ⟨_, (ht _).mpr rfl, fun y hy ↦ (ht y).mp hy⟩

theorem usubaHierarchyName_forces {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (α : ForcingName P) :
    p ∈ forcingFormula P R hierarchyFormula
      (standardTuple ![usubaHierarchyName P R α.val, α.val]) := by
  apply formulaUniqueName_forces hierarchyFormula _ hR htop hp ![α]
  intro W _ _ _ v
  have ht (x : W) : hierarchyFormula.Evalb (x :> v) ↔
      x = hierarchy (v 0) := hierarchyFormula_defined.iff _
  exact ⟨_, (ht _).mpr rfl, fun y hy ↦ (ht y).mp hy⟩

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def usubaCollapseName (κ S : ForcingName A.P) : ForcingName A.P :=
  ⟨ZFVP.usubaCollapseName A.P A.R κ.val S.val, usubaCollapseName_isName _ _ _ _⟩

noncomputable def usubaTargetName (κ : ForcingName A.P) : ForcingName A.P :=
  ⟨ZFVP.usubaTargetName A.P A.R κ.val, usubaTargetName_isName _ _ _⟩

noncomputable def usubaHierarchyName (α : ForcingName A.P) : ForcingName A.P :=
  ⟨ZFVP.usubaHierarchyName A.P A.R α.val, usubaHierarchyName_isName _ _ _⟩

theorem usubaCollapseName_value (κ S : ForcingName A.P) :
    A.ofName (A.usubaCollapseName κ S) = usubaCollapse (A.ofName κ) (A.ofName S) := by
  have ht (x : A.Model) : usubaCollapseFormula.Evalb
      (x :> (fun i ↦ A.ofName ((![κ, S] : Fin 2 → ForcingName A.P) i))) ↔
        x = usubaCollapse (A.ofName κ) (A.ofName S) := usubaCollapseFormula_defined.iff _
  exact A.formulaName_value usubaCollapseFormula ![κ, S]
    (fun x y hx hy ↦ ((ht x).mp hx).trans ((ht y).mp hy).symm) ((ht _).mpr rfl)

theorem usubaTargetName_value (κ : ForcingName A.P) :
    A.ofName (A.usubaTargetName κ) = usubaLeastTarget (A.ofName κ) := by
  have ht (x : A.Model) : usubaLeastTargetFormula.Evalb
      (x :> (fun i ↦ A.ofName ((![κ] : Fin 1 → ForcingName A.P) i))) ↔
        x = usubaLeastTarget (A.ofName κ) := usubaLeastTargetFormula_defined.iff _
  exact A.formulaName_value usubaLeastTargetFormula ![κ]
    (fun x y hx hy ↦ ((ht x).mp hx).trans ((ht y).mp hy).symm) ((ht _).mpr rfl)

theorem usubaHierarchyName_value (α : ForcingName A.P) :
    A.ofName (A.usubaHierarchyName α) = hierarchy (A.ofName α) := by
  have ht (x : A.Model) : hierarchyFormula.Evalb
      (x :> (fun i ↦ A.ofName ((![α] : Fin 1 → ForcingName A.P) i))) ↔
        x = hierarchy (A.ofName α) := hierarchyFormula_defined.iff _
  exact A.formulaName_value hierarchyFormula ![α]
    (fun x y hx hy ↦ ((ht x).mp hx).trans ((ht y).mp hy).symm) ((ht _).mpr rfl)

end ForcingContext
end ZFVP

