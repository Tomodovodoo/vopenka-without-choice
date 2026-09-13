import ZFVP.ModelTheory.ProjectionQuotientClosureForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingSeparativeDescendingFormula : SetTheorySemisentence 4 :=
  f“P R α f. !boundedFunctionFormula f α P ∧ ∃ S, !forcingSeparativeOrderFormula S P R ∧
    ∀ i ∈ α, ∀ j ∈ i, !kpair.dfn (!value.dfn f i) (!value.dfn f j) ∈ S”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingSeparativeDescendingFormula_defined :
    Defined (fun v : Fin 4 → V ↦ IsForcingDescending (v 0)
      (forcingSeparativeOrder (v 0) (v 1)) (v 2) (v 3)) forcingSeparativeDescendingFormula :=
  ⟨fun v ↦ by simp [forcingSeparativeDescendingFormula, IsForcingDescending]⟩

namespace ForcingContext

theorem projectionQuotient_descending_of_forced (A : ForcingContext V)
    {Q S π α p : V} (hπ : IsForcingProjection A.P A.R Q S π) (hS : IsForcingPreorder Q S)
    (f : ForcingName A.P) (hp : p ∈ A.G)
    (hf : p ∈ forcingFormula A.P A.R forcingSeparativeDescendingFormula
      (standardTuple ![projectionQuotientName Q π A.one, projectionQuotientOrderName S π A.one,
        checkName A.one α, f.val])) :
    IsForcingDescending (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π))
      (A.check α) (A.ofName f) := by
  let QN : ForcingName A.P := ⟨projectionQuotientName Q π A.one, projectionQuotientName_isName A.top.1 hπ.maps⟩
  let SN : ForcingName A.P := ⟨projectionQuotientOrderName S π A.one, projectionQuotientOrderName_isName A.top.1 hπ.maps hS⟩
  have ht := (Defined.eval_iff _).mp ((A.formula_truth forcingSeparativeDescendingFormula
    ![QN, SN, ⟨checkName A.one α, checkName_isName A.top.1 α⟩, f]).mpr ⟨p, hp, hf⟩)
  change IsForcingDescending (A.ofName QN) (forcingSeparativeOrder (A.ofName QN) (A.ofName SN))
    (A.check α) (A.ofName f) at ht
  rwa [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hS] at ht

theorem projectionQuotient_bound_of_forced (A : ForcingContext V)
    {Q S π α p q : V} (hπ : IsForcingProjection A.P A.R Q S π) (hS : IsForcingPreorder Q S)
    (f : ForcingName A.P) (hp : p ∈ A.G)
    (hf : p ∈ forcingFormula A.P A.R forcingSeparativeBoundFormula
      (standardTuple ![projectionQuotientName Q π A.one, projectionQuotientOrderName S π A.one,
        checkName A.one α, f.val, checkName A.one q])) :
    A.check q ∈ A.projectionQuotient Q π ∧
      ∀ a ∈ A.check α, ⟨A.check q, (A.ofName f) ‘ a⟩ₖ ∈
        forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π) := by
  let QN : ForcingName A.P := ⟨projectionQuotientName Q π A.one, projectionQuotientName_isName A.top.1 hπ.maps⟩
  let SN : ForcingName A.P := ⟨projectionQuotientOrderName S π A.one, projectionQuotientOrderName_isName A.top.1 hπ.maps hS⟩
  have ht := (Defined.eval_iff _).mp ((A.formula_truth forcingSeparativeBoundFormula
    ![QN, SN, ⟨checkName A.one α, checkName_isName A.top.1 α⟩, f,
      ⟨checkName A.one q, checkName_isName A.top.1 q⟩]).mpr ⟨p, hp, hf⟩)
  change A.check q ∈ A.ofName QN ∧ ∀ a ∈ A.check α, ⟨A.check q, (A.ofName f) ‘ a⟩ₖ ∈
    forcingSeparativeOrder (A.ofName QN) (A.ofName SN) at ht
  rwa [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hS] at ht

end ForcingContext

theorem projectionQuotient_bound_forced_of_generics [Countable V]
    {P R one Q S π α p q : V} (hR : IsForcingPreorder P R) (ho : IsForcingTop P R one)
    (hπ : IsForcingProjection P R Q S π) (hS : IsForcingPreorder Q S)
    (hp : p ∈ P) (f : ForcingName P)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), p ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
      A.check q ∈ A.projectionQuotient Q π ∧
        ∀ a ∈ A.check α, ⟨A.check q, (A.ofName f) ‘ a⟩ₖ ∈
          forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) :
    p ∈ forcingFormula P R forcingSeparativeBoundFormula
      (standardTuple ![projectionQuotientName Q π one, projectionQuotientOrderName S π one,
        checkName one α, f.val, checkName one q]) := by
  let QN : ForcingName P := ⟨projectionQuotientName Q π one, projectionQuotientName_isName ho.1 hπ.maps⟩
  let SN : ForcingName P := ⟨projectionQuotientOrderName S π one, projectionQuotientOrderName_isName ho.1 hπ.maps hS⟩
  apply forcingFormula_of_all_generics hR ho hp forcingSeparativeBoundFormula
    ![QN, SN, ⟨checkName one α, checkName_isName ho.1 α⟩, f, ⟨checkName one q, checkName_isName ho.1 q⟩]
  intro G hG hpG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
  apply (Defined.eval_iff _).mpr
  change A.check q ∈ A.ofName QN ∧ ∀ a ∈ A.check α, ⟨A.check q, (A.ofName f) ‘ a⟩ₖ ∈
    forcingSeparativeOrder (A.ofName QN) (A.ofName SN)
  rw [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hS]
  exact hf G hG hpG

end ZFVP
