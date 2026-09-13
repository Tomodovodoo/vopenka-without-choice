import ZFVP.ModelTheory.InfinitaryAdequateQuantifier
import ZFVP.ModelTheory.InfinitaryAdequateParameterTruth

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel.AdequateGenericChain
open AdequateFiniteCondition
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}
  {p₀ : AdequateFiniteCondition M S} (C : AdequateGenericChain M S p₀)

theorem equal_of_names {i j a} (hi : C.Names i a) (hj : C.Names j a) : C.Equal i j := by
  obtain ⟨k, hk⟩ := (C.names_iff _ _).mp hi
  obtain ⟨l, hl⟩ := (C.names_iff _ _).mp hj
  obtain ⟨hti, hh⟩ := namesAt_persistent (C.refines (Nat.le_max_left k l)) hk
  obtain ⟨htj, hg⟩ := namesAt_persistent (C.refines (Nat.le_max_right k l)) hl
  exact ⟨max k l, hti, htj, fun b hb ↦ (hh b hb).trans (hg b hb).symm⟩

theorem eval_at_named_point (ψ : ParameterInstance M S 1) {t a} (hn : C.Names t a) :
    C.Eval ψ (t :> Fin.elim0) ↔ ψ.Eval (a :> Fin.elim0) := by
  apply C.eval_named_tuple
  intro i
  cases i using Fin.cases with
  | zero => exact hn
  | succ i => exact i.elim0

/-- A coordinate in an old negative named fiber equals an old point of that fiber. -/
theorem small_fiber_coordinate (ψ : ParameterInstance M S 1)
    (hs : ¬M.Q {x | ψ.Eval (x :> Fin.elim0)}) (t : ℕ)
    (ht : C.Eval ψ (t :> Fin.elim0)) :
    ∃ a : M.Domain, C.classOf t = C.oldEmbedding a ∧ ψ.Eval (a :> Fin.elim0) := by
  obtain ⟨k, hk⟩ := C.freezes (0 : Fin (t + 1)) ψ hs
  obtain ⟨l, hl⟩ := ht
  obtain ⟨hts, hh⟩ := evalAt_persistent (C.refines (Nat.le_max_right k l)) hl
  obtain ⟨h, hf⟩ := hk (max k l) (Nat.le_max_left _ _)
  have hi : Formula.rightEmbed h (0 : Fin (t + 1)) = RightCoordinate.index (hts 0) := by
    apply Fin.ext
    simp only [Formula.rightEmbed, Fin.val_zero, zero_add, RightCoordinate.index]
    rfl
  rcases hf with hn | ⟨a, ha⟩
  · obtain ⟨b, hb⟩ := (C.point (max k l)).2.nonempty C.adequate
    have hψ : ψ.Eval (b (RightCoordinate.index (hts 0)) :> Fin.elim0) := by
      have he : (fun j ↦ b (RightCoordinate.index (hts j))) =
          b (RightCoordinate.index (hts 0)) :> Fin.elim0 := by
        funext j
        cases j using Fin.cases with
        | zero => rfl
        | succ j => exact j.elim0
      exact he ▸ hh b hb
    exact (hn b hb (hi.symm ▸ hψ)).elim
  · have hname : C.Names t a := by
      apply (C.names_iff _ _).mpr
      refine ⟨max k l, hts 0, ?_⟩
      intro b hb
      exact hi ▸ ha b hb
    refine ⟨a, C.classOf_eq_iff.mpr (C.equal_of_names hname (C.oldCoordinate_names a)), ?_⟩
    exact (C.eval_at_named_point ψ hname).mp ⟨l, hl⟩

/-- Exact image equality already holds at the generic-label level. -/
theorem small_fiber_eq_oldImage (ψ : ParameterInstance M S 1)
    (hs : ¬M.Q {x | ψ.Eval (x :> Fin.elim0)}) :
    C.genericFiber ψ Fin.elim0 = C.oldEmbedding '' {x | ψ.Eval (x :> Fin.elim0)} := by
  ext y
  obtain ⟨t, rfl⟩ := C.classOf_surjective y
  constructor
  · intro h
    obtain ⟨a, he, ha⟩ := C.small_fiber_coordinate ψ hs t ((C.classOf_mem_genericFiber _ _ _).mp h)
    exact ⟨a, ha, he.symm⟩
  · rintro ⟨a, ha, he⟩
    rw [← he]
    apply (C.classOf_mem_genericFiber ψ Fin.elim0 (C.oldCoordinate a)).mpr
    exact (C.eval_at_named_point ψ (C.oldCoordinate_names a)).mpr ha

theorem initial_truth : C.Eval p₀.2.formula (fun i : Fin (1 + p₀.1) ↦ 1 + p₀.1 - (i.val + 1)) := by
  refine ⟨0, ?_⟩
  rw [C.initial]
  have ht (i : Fin (1 + p₀.1)) : 1 + p₀.1 - (i.val + 1) < 1 + p₀.1 := by omega
  refine ⟨ht, ?_⟩
  intro b hb
  have he : (fun i ↦ b (RightCoordinate.index (ht i))) = b := by
    funext i
    congr 1
    apply Fin.ext
    simp only [RightCoordinate.index]
    omega
  exact he.symm ▸ hb

end WeakModel.AdequateGenericChain
end ZFVP.Infinitary

