import ZFVP.ModelTheory.InfinitarySmallTermFreezing

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula
variable {L : Language} {M : Type*} [Structure L M] (Q : Set M → Prop)

theorem weakEval_unary_instance {n} (ψ : Formula L 1) (t : Semiterm L Empty n) (b : Fin n → M) :
    WeakEval Q (ψ.subst (fun _ : Fin 1 ↦ t)) b ↔ WeakEval Q ψ (t.val b Empty.elim :> Fin.elim0) := by
  rw [weakEval_subst]
  have he : (fun _ : Fin 1 ↦ t.val b Empty.elim) = (t.val b Empty.elim :> Fin.elim0) := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact i.elim0
  rw [he]

end Formula
namespace HenkinConstruction.FragmentExtension.LargeCondition
open HenkinLanguage FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}

theorem freeze_small_term {n} (p : H.LargeCondition n)
    (t : Semiterm (limit L) Empty (1 + n)) {ψ : Formula (limit L) 1}
    (hψ : ⟨1, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)) (hs : .q ψ ∉ H.carrier) :
    ∃ q : H.LargeCondition n, SameLevelRefines p q ∧
      ((∀ b, Formula.WeakEval H.weakQuantifier q.formula b →
        ¬Formula.WeakEval H.weakQuantifier ψ (t.val b Empty.elim :> Fin.elim0)) ∨
      ∃ u : Semiterm (limit L) Empty 0, ∀ b, Formula.WeakEval H.weakQuantifier q.formula b →
        t.val b Empty.elim = u.val Fin.elim0 Empty.elim) := by
  let θ := ψ.subst (fun _ : Fin 1 ↦ t)
  have hθ := subst_closed hψ (fun _ : Fin 1 ↦ t)
  rcases H.q_mem_projected_split n p.in_fragment hθ p.large with hp | hn
  · have hb : ∀ b : Fin (1 + n) → H.Domain, Formula.WeakEval H.weakQuantifier (p.formula.and θ) b →
        Formula.WeakEval H.weakQuantifier ψ (t.val b Empty.elim :> Fin.elim0) := by
      intro b h
      exact (Formula.weakEval_unary_instance _ ψ t b).mp ((Formula.weakEval_and _ _ _ _).mp h).2
    obtain ⟨u, hu⟩ := H.q_mem_fix_small_term n (and_closed p.in_fragment hθ) t hψ hp hs hb
    refine ⟨⟨(p.formula.and θ).and (Formula.termEqual t (Formula.liftClosedTerm u)),
      and_closed (and_closed p.in_fragment hθ) (fo_in_fragment _), hu⟩, ?_, Or.inr ⟨u, ?_⟩⟩
    · intro b h
      exact ((Formula.weakEval_and _ _ _ _).mp ((Formula.weakEval_and _ _ _ _).mp h).1).1
    · intro b h
      have he := (Formula.weakEval_and _ _ _ _).mp h |>.2
      simpa only [Formula.weakEval_termEqual, Formula.val_liftClosedTerm] using he
  · refine ⟨⟨p.formula.and (.neg θ), and_closed p.in_fragment (neg_closed hθ), hn⟩, ?_, Or.inl ?_⟩
    · intro b h
      exact (Formula.weakEval_and _ _ _ _).mp h |>.1
    · intro b h hh
      exact ((Formula.weakEval_and _ _ _ _).mp h).2 ((Formula.weakEval_unary_instance _ ψ t b).mpr hh)

/-- A large condition can keep its distinguished coordinate distinct from any
specified old closed-term value. -/
theorem avoid_old_value {n} (p : H.LargeCondition n) (u : Semiterm (limit L) Empty 0) :
    ∃ q : H.LargeCondition n, SameLevelRefines p q ∧
      ∀ b, Formula.WeakEval H.weakQuantifier q.formula b →
        b (Formula.lastCoordinate n) ≠ u.val Fin.elim0 Empty.elim := by
  let θ : Formula (limit L) (1 + n) :=
    Formula.termEqual (.bvar (Formula.lastCoordinate n)) (Formula.liftClosedTerm u)
  have hθ : ⟨1 + n, θ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) := fo_in_fragment _
  have hn : .q (Formula.exsN n (p.formula.and θ)) ∉ H.carrier := by
    intro hp
    have hf := exsN_closed n (and_closed p.in_fragment hθ)
    have hq := (H.weakQuantifier_fiber hf).mpr hp
    apply H.weakQuantifier_not_subset_twoPoints (u.val Fin.elim0 Empty.elim) (u.val Fin.elim0 Empty.elim) ?_ hq
    intro x hx
    rw [H.fiber_weakEval hf, Formula.weakEval_exsN_one_iff] at hx
    obtain ⟨e, he, hh⟩ := hx
    have ht := (Formula.weakEval_and _ _ _ _).mp hh |>.2
    have hv : e (Formula.lastCoordinate n) = u.val Fin.elim0 Empty.elim := by
      simpa only [θ, Formula.weakEval_termEqual, Formula.val_liftClosedTerm, Semiterm.val_bvar] using ht
    have hxv : x = u.val Fin.elim0 Empty.elim := he.symm.trans hv
    simp [hxv]
  have hq := (H.q_mem_projected_split n p.in_fragment hθ p.large).resolve_left hn
  refine ⟨⟨p.formula.and (.neg θ), and_closed p.in_fragment (neg_closed hθ), hq⟩, ?_, ?_⟩
  · intro b h
    exact (Formula.weakEval_and _ _ _ _).mp h |>.1
  · intro b h
    have ht := (Formula.weakEval_and _ _ _ _).mp h |>.2
    simpa only [θ, Formula.weakEval_neg, Formula.weakEval_termEqual,
      Formula.val_liftClosedTerm, Semiterm.val_bvar] using ht

end HenkinConstruction.FragmentExtension.LargeCondition
end ZFVP.Infinitary
