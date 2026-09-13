import ZFVP.ModelTheory.SchmerlCodedInfinitarySemantics

/-! Actual universe fragments represent every supported external constructor. -/
namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory ZFVP.Schmerl
variable {Λ : Language}

theorem universeFragment_coding {L : Universe.{u}} (hL : IsLanguageCode L)
    (F : ∀ {k}, Λ.Func k → Universe.{u}) (R : ∀ {k}, Λ.Rel k → Universe.{u})
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧ (functionArities L) ‘ (F f) = (k : Universe.{u}))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧ (relationArities L) ‘ (R r) = (k : Universe.{u}))
    {A : Set (Σ n, Formula Λ n)} [Small.{u} A] (hA : SubformulaClosed A) :
    IsFragmentCoding L (universeFragment F R A) F R (universeFormulaCode F R) A where
  fragment := universeFragment_valid hL F R hF hR hA
  closed := hA
  node _ hφ := contextCode_mem_universeFragment F R hφ
  fo _ _ := rfl
  neg _ _ := rfl
  conj φ _ := ⟨universeSequence (fun i ↦ universeFormulaCode F R (φ i)),
    inferInstance, domain_universeSequence _, rfl, value_universeSequence _⟩
  exs _ _ := rfl
  q _ _ := rfl

end ZFVP.Infinitary.Internal

