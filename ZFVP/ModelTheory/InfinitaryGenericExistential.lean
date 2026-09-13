import ZFVP.ModelTheory.InfinitaryGenericSubstitution

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.GenericConditionChain
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

/-- Generic existential truth has a witness among the coordinate terms. -/
theorem eval_existential_iff {n} {φ : Formula (limit L) (n + 1)}
    (hφ : ⟨n, .exs φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (ts : Fin n → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point (.exs φ) ts ↔
      ∃ t : CoordinateTerm (limit L), CoordinateTerm.Eval C.point φ (t :> ts) := by
  constructor
  · intro he
    let σ := fun i ↦ Formula.liftRightTerm (CoordinateTerm.le_arity ts i) (ts i).2
    have hinst := subst_closed hφ σ
    have hh := (C.eval_iff_contains (.exs φ) ts).mp he
    change C.Contains (.exs (φ.subst (liftSubstitution σ))) at hh
    obtain ⟨k, h, i, hw⟩ := (C.existential_iff hinst).mp hh
    let t : CoordinateTerm (limit L) := ⟨1 + (C.point k).1, .bvar i⟩
    let hs : ∀ j : Fin (n + 1), ((t :> ts) j).1 ≤ 1 + (C.point k).1 :=
      Fin.cases (le_refl _) (fun j ↦ (CoordinateTerm.le_arity ts j).trans h)
    refine ⟨t, k, hs, ?_⟩
    intro b hb
    have hv := (Formula.weakEval_subst H.weakQuantifier (liftSubstitution σ) φ
      (b i :> b ∘ Formula.rightEmbed h)).mp (hw b hb)
    rw [val_liftSubstitution] at hv
    have ht : (fun j ↦ ((t :> ts) j).2.val (b ∘ Formula.rightEmbed (hs j)) Empty.elim) =
        b i :> (fun j ↦ (σ j).val (b ∘ Formula.rightEmbed h) Empty.elim) := by
      funext j
      cases j using Fin.cases with
      | zero =>
        change b (Formula.rightEmbed (le_refl (1 + (C.point k).1)) i) = b i
        rw [Formula.rightEmbed_refl]
      | succ j =>
        change (ts j).2.val
          (b ∘ Formula.rightEmbed ((CoordinateTerm.le_arity ts j).trans h)) Empty.elim =
            (σ j).val (b ∘ Formula.rightEmbed h) Empty.elim
        simp only [σ, Formula.val_liftRightTerm,
          Function.comp_def, Formula.rightEmbed_trans]
    exact ht ▸ hv
  · rintro ⟨t, k, hs, hh⟩
    refine ⟨k, fun j ↦ hs j.succ, ?_⟩
    intro b hb
    refine ⟨t.2.val (b ∘ Formula.rightEmbed (hs 0)) Empty.elim, ?_⟩
    have ht : (fun j ↦ ((t :> ts) j).2.val (b ∘ Formula.rightEmbed (hs j)) Empty.elim) =
        t.2.val (b ∘ Formula.rightEmbed (hs 0)) Empty.elim :>
          (fun j ↦ (ts j).2.val (b ∘ Formula.rightEmbed (hs j.succ)) Empty.elim) := by
      funext j
      cases j using Fin.cases <;> rfl
    exact ht ▸ hh b hb

end HenkinConstruction.FragmentExtension.GenericConditionChain
end ZFVP.Infinitary
