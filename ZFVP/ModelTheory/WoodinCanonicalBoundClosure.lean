import ZFVP.ModelTheory.ProjectionQuotientSequenceForcing

/-! Packaging step: if every name for a descending sequence in the projection quotient has a
forced separative bound, then the whole closure statement below `η` is forced. This is the
general form, with no assumption on the shape of the projection, so that it can later be used
for the raw inverse limit. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Turn forced bounds for named descending sequences into
`ForcesProjectionQuotientClosedBelow`. The hypothesis says: for every `α ∈ η`, every condition
`p` and every name `f`, if `p` forces `f` to be an `α`-sequence descending in the separative
order of the projection quotient, then some name `ν` is forced by `p` to be a lower bound for
that sequence. -/
theorem forcesProjectionQuotientClosedBelow_of_named_bounds [Countable V]
    {P R one Q S π η : V} [IsOrdinal η]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hπ : IsForcingProjection P R Q S π) (hS : IsForcingPreorder Q S)
    (hbound : ∀ α ∈ η, ∀ p ∈ P, ∀ f : ForcingName P,
      p ∈ forcingFormula P R forcingSeparativeDescendingFormula
        (standardTuple ![projectionQuotientName Q π one, projectionQuotientOrderName S π one,
          checkName one α, f.val]) →
      ∃ ν : ForcingName P, p ∈ forcingFormula P R forcingSeparativeBoundFormula
        (standardTuple ![projectionQuotientName Q π one, projectionQuotientOrderName S π one,
          checkName one α, f.val, ν.val])) :
    ForcesProjectionQuotientClosedBelow P R one Q S π η := by
  apply projectionQuotient_closedBelow_forced_of_generics hR htop hπ hS
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  let QN : ForcingName P := ⟨projectionQuotientName Q π one,
    projectionQuotientName_isName htop.1 hπ.maps⟩
  let SN : ForcingName P := ⟨projectionQuotientOrderName S π one,
    projectionQuotientOrderName_isName htop.1 hπ.maps hS⟩
  let cn (x : V) : ForcingName P := ⟨checkName one x, checkName_isName htop.1 x⟩
  show IsForcingClosedBelow (A.projectionQuotient Q π)
    (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π))
    (A.check η)
  intro a ha
  obtain ⟨α, hα, rfl⟩ := (A.mem_check_iff η a).mp ha
  intro g hg
  obtain ⟨f, rfl⟩ := A.ofName_surjective g
  have hdesc : forcingSeparativeDescendingFormula.Evalb
      (fun i ↦ A.ofName (![QN, SN, cn α, f] i)) := by
    apply (Defined.eval_iff _).mpr
    change IsForcingDescending (A.ofName QN)
      (forcingSeparativeOrder (A.ofName QN) (A.ofName SN)) (A.check α) (A.ofName f)
    rw [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hS]
    exact hg
  obtain ⟨p, hpG, hpf⟩ :=
    (A.formula_truth forcingSeparativeDescendingFormula ![QN, SN, cn α, f]).mp hdesc
  obtain ⟨ν, hν⟩ := hbound α hα p (hG.1.1 p hpG) f hpf
  have hb := (Defined.eval_iff _).mp ((A.formula_truth forcingSeparativeBoundFormula
    ![QN, SN, cn α, f, ν]).mpr ⟨p, hpG, hν⟩)
  change A.ofName ν ∈ A.ofName QN ∧ ∀ i ∈ A.check α,
    ⟨A.ofName ν, (A.ofName f) ‘ i⟩ₖ ∈ forcingSeparativeOrder (A.ofName QN) (A.ofName SN) at hb
  rw [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hS] at hb
  exact ⟨A.ofName ν, hb.1, hb.2⟩

end ZFVP
