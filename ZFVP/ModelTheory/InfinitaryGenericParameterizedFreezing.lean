import ZFVP.ModelTheory.InfinitaryGenericSmallFibers

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.GenericConditionChain
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

theorem closedTerm_val_extension (u : Semiterm (limit L) Empty 0) :
    u.val (s := C.extensionStructure) Fin.elim0 Empty.elim = C.oldTerm u := by
  let ψ : Formula (limit L) 1 := Formula.termEqual (Formula.liftClosedTerm u) (.bvar 0)
  have hold : Formula.WeakEval H.weakQuantifier ψ (H.classOf u :> Fin.elim0) := by
    rw [Formula.weakEval_termEqual, Formula.val_liftClosedTerm]
    exact closedTerm_val u
  have hnew := (C.extension_elementary ψ (fo_in_fragment _) (H.classOf u :> Fin.elim0)).mpr hold
  rw [Formula.weakEval_termEqual, Formula.val_liftClosedTerm] at hnew
  change u.val (s := C.extensionStructure) Fin.elim0 Empty.elim =
    C.oldEmbedding (H.classOf u) at hnew
  exact hnew.trans (C.oldEmbedding_classOf u)

/-- Every fiber with old parameters and a negative old Q label is unchanged by
the generic extension, up to its embedding of the old domain. -/
theorem parameterized_small_fiber_eq_oldImage {n} {φ : Formula (limit L) (n + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (b : Fin n → H.Domain)
    (hs : ¬H.weakQuantifier {x : H.Domain | Formula.WeakEval H.weakQuantifier φ (x :> b)}) :
    {y : C.ExtensionDomain | Formula.WeakEval C.extensionQuantifier φ
      (y :> C.oldEmbedding ∘ b)} =
      C.oldEmbedding '' {x : H.Domain | Formula.WeakEval H.weakQuantifier φ (x :> b)} := by
  let σ : Fin (n + 1) → Semiterm (limit L) Empty 1 :=
    Fin.cases (.bvar 0) (fun i ↦ Formula.liftClosedTerm (b i).out)
  let ψ := φ.subst σ
  have hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) := subst_closed hφ σ
  have hold (x : H.Domain) : Formula.WeakEval H.weakQuantifier ψ (x :> Fin.elim0) ↔
      Formula.WeakEval H.weakQuantifier φ (x :> b) := by
    dsimp only [ψ]
    rw [Formula.weakEval_subst]
    have heq : (fun i ↦ (σ i).val (x :> Fin.elim0) Empty.elim) = x :> b := by
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
        change (Formula.liftClosedTerm (b i).out).val (x :> Fin.elim0) Empty.elim = b i
        rw [Formula.val_liftClosedTerm, closedTerm_val]
        exact Quotient.out_eq (b i)
    rw [heq]
  have hnew (y : C.ExtensionDomain) : Formula.WeakEval C.extensionQuantifier ψ (y :> Fin.elim0) ↔
      Formula.WeakEval C.extensionQuantifier φ (y :> C.oldEmbedding ∘ b) := by
    dsimp only [ψ]
    rw [Formula.weakEval_subst]
    have heq : (fun i ↦ (σ i).val (y :> Fin.elim0) Empty.elim) = y :> C.oldEmbedding ∘ b := by
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
        change (Formula.liftClosedTerm (b i).out).val (y :> Fin.elim0) Empty.elim =
          C.oldEmbedding (b i)
        rw [Formula.val_liftClosedTerm, C.closedTerm_val_extension]
        rfl
    rw [heq]
  have hsmall : ¬Formula.WeakEval H.weakQuantifier (.q ψ) Fin.elim0 := by
    change ¬H.weakQuantifier {x : H.Domain | Formula.WeakEval H.weakQuantifier ψ (x :> Fin.elim0)}
    rwa [Set.ext hold]
  exact (Set.ext (fun y ↦ (hnew y).symm)).trans
    ((C.small_fiber_eq_oldImage_of_not_q hψ hsmall).trans
      (congrArg (Set.image C.oldEmbedding) (Set.ext hold)))

end HenkinConstruction.FragmentExtension.GenericConditionChain
end ZFVP.Infinitary
