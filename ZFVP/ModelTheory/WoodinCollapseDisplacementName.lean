import ZFVP.ModelTheory.WoodinCollapseDisplacementFormula

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinCollapseDisplacementName (P R κ δ p q : V) : V :=
  formulaUniqueName P R woodinCollapseDisplacementFormula (standardTuple ![κ, δ, p, q])

theorem woodinCollapseDisplacementName_isName (P R κ δ p q : V) :
    IsForcingName P (woodinCollapseDisplacementName P R κ δ p q) :=
  formulaUniqueName_isName _ _ _ _

theorem woodinCollapseDisplacementName_forces {P R one r : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hr : r ∈ P)
    (κ δ p q : ForcingName P) :
    r ∈ forcingFormula P R woodinCollapseDisplacementFormula
      (standardTuple ![woodinCollapseDisplacementName P R κ.val δ.val p.val q.val,
        κ.val, δ.val, p.val, q.val]) := by
  apply formulaUniqueName_forces woodinCollapseDisplacementFormula _ hR ht hr ![κ, δ, p, q]
  intro W _ _ _ v
  have he (x : W) : woodinCollapseDisplacementFormula.Evalb (x :> v) ↔
      x = totalWoodinCollapseDisplacement (v 0) (v 1) (v 2) (v 3) :=
    woodinCollapseDisplacementFormula_defined.iff _
  exact ⟨_, (he _).mpr rfl, fun y hy ↦ (he y).mp hy⟩

noncomputable def collapseConverseName (P R f : V) : V :=
  formulaUniqueName P R sparseConverseGraphFormula (standardTuple ![f])

theorem collapseConverseName_isName (P R f : V) : IsForcingName P (collapseConverseName P R f) :=
  formulaUniqueName_isName _ _ _ _

theorem collapseConverseName_forces {P R one r : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hr : r ∈ P)
    (f : ForcingName P) :
    r ∈ forcingFormula P R sparseConverseGraphFormula
      (standardTuple ![collapseConverseName P R f.val, f.val]) := by
  apply formulaUniqueName_forces sparseConverseGraphFormula _ hR ht hr ![f]
  intro W _ _ _ v
  have he (x : W) : sparseConverseGraphFormula.Evalb (x :> v) ↔ x = converseGraph (v 0) :=
    sparseConverseGraphFormula_defined.iff _
  exact ⟨_, (he _).mpr rfl, fun y hy ↦ (he y).mp hy⟩

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def collapseDisplacementName (κ δ p q : ForcingName A.P) : ForcingName A.P :=
  ⟨woodinCollapseDisplacementName A.P A.R κ.val δ.val p.val q.val,
    woodinCollapseDisplacementName_isName _ _ _ _ _ _⟩

theorem collapseDisplacementName_value (κ δ p q : ForcingName A.P) :
    A.ofName (A.collapseDisplacementName κ δ p q) =
      totalWoodinCollapseDisplacement (A.ofName κ) (A.ofName δ) (A.ofName p) (A.ofName q) := by
  have he (x : A.Model) : woodinCollapseDisplacementFormula.Evalb
      (x :> (fun i ↦ A.ofName ((![κ, δ, p, q] : Fin 4 → ForcingName A.P) i))) ↔
      x = totalWoodinCollapseDisplacement (A.ofName κ) (A.ofName δ) (A.ofName p) (A.ofName q) :=
    woodinCollapseDisplacementFormula_defined.iff _
  exact A.formulaName_value woodinCollapseDisplacementFormula ![κ, δ, p, q]
    (fun x y hx hy ↦ ((he x).mp hx).trans ((he y).mp hy).symm) ((he _).mpr rfl)

theorem collapseDisplacementName_value_of_ordinal (κ δ p q : ForcingName A.P)
    [IsOrdinal (A.ofName δ)] :
    A.ofName (A.collapseDisplacementName κ δ p q) =
      woodinCollapseDisplacement (A.ofName κ) (A.ofName δ) (A.ofName p) (A.ofName q) :=
  (A.collapseDisplacementName_value κ δ p q).trans (totalWoodinCollapseDisplacement_eq _ _ _ _)

noncomputable def collapseConverseName (f : ForcingName A.P) : ForcingName A.P :=
  ⟨ZFVP.collapseConverseName A.P A.R f.val, collapseConverseName_isName _ _ _⟩

theorem collapseConverseName_value (f : ForcingName A.P) :
    A.ofName (A.collapseConverseName f) = converseGraph (A.ofName f) := by
  have he (x : A.Model) : sparseConverseGraphFormula.Evalb
      (x :> (fun i ↦ A.ofName ((![f] : Fin 1 → ForcingName A.P) i))) ↔
      x = converseGraph (A.ofName f) := sparseConverseGraphFormula_defined.iff _
  exact A.formulaName_value sparseConverseGraphFormula ![f]
    (fun x y hx hy ↦ ((he x).mp hx).trans ((he y).mp hy).symm) ((he _).mpr rfl)

end ForcingContext
end ZFVP
