import ZFVP.ModelTheory.InfinitaryGenericQuantifier

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.GenericConditionChain
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

theorem eval_closedTuple_iff {n} (φ : Formula (limit L) n)
    (ts : Fin n → Semiterm (limit L) Empty 0) :
    CoordinateTerm.Eval C.point φ (fun i ↦ ⟨0, ts i⟩) ↔
      Formula.WeakEval H.weakQuantifier φ (fun i ↦ (ts i).val Fin.elim0 Empty.elim) := by
  have hv (p : H.FiniteCondition) (hs : ∀ i : Fin n, 0 ≤ 1 + p.1)
      (b : Fin (1 + p.1) → H.Domain) :
      (fun i ↦ (ts i).val (b ∘ Formula.rightEmbed (hs i)) Empty.elim) =
        (fun i ↦ (ts i).val Fin.elim0 Empty.elim) := by
    funext i
    congr 1
    exact Subsingleton.elim _ _
  constructor
  · rintro ⟨k, hs, hh⟩
    obtain ⟨b, hb⟩ := (C.point k).realizable
    simpa only [hv] using hh b hb
  · intro hh
    refine ⟨0, fun _ ↦ Nat.zero_le _, ?_⟩
    intro b _
    simpa only [hv] using hh

/-- The original embedding is elementary for the entire closed fragment,
including Q and represented infinitary conjunctions. -/
theorem extension_elementary {n} (φ : Formula (limit L) n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (b : Fin n → H.Domain) :
    Formula.WeakEval C.extensionQuantifier φ (C.oldEmbedding ∘ b) ↔
      Formula.WeakEval H.weakQuantifier φ b := by
  change Formula.WeakEval C.extensionQuantifier φ
    (fun i ↦ C.termClass ⟨0, (b i).out⟩) ↔ _
  rw [C.extension_truth φ hφ, C.eval_closedTuple_iff]
  have hv : (fun i ↦ ((b i).out).val (s := H.termStructure) Fin.elim0 Empty.elim) = b := by
    funext i
    rw [closedTerm_val]
    exact Quotient.out_eq (b i)
  rw [hv]

theorem initial_truth :
    Formula.WeakEval C.extensionQuantifier p₀.2.formula
      (fun i : Fin (1 + p₀.1) ↦ C.termClass ⟨1 + p₀.1, .bvar i⟩) := by
  apply (C.extension_truth p₀.2.formula p₀.2.in_fragment _).mpr
  refine ⟨0, ?_⟩
  rw [C.initial]
  refine ⟨fun _ ↦ le_refl _, ?_⟩
  intro b hb
  simpa only [Semiterm.val_bvar, Function.comp_apply, Formula.rightEmbed_refl] using hb

end HenkinConstruction.FragmentExtension.GenericConditionChain
end ZFVP.Infinitary
