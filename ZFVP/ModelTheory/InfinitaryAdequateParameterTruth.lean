import ZFVP.ModelTheory.InfinitaryAdequateOldEmbedding

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel.AdequateGenericChain
open AdequateFiniteCondition
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}
  {p₀ : AdequateFiniteCondition M S} (C : AdequateGenericChain M S p₀)

/-- Naming finite old parameters agrees with placing their coordinate representatives
in the additional free slots of the original fragment template. -/
theorem eval_parameterInstance {n} (p : ParameterInstance M S n) (ts : Fin n → ℕ) :
    C.Eval p ts ↔ C.Eval (ParameterInstance.ofFormula p.2.1.1 p.2.1.2)
      (Fin.append ts (C.oldCoordinate ∘ p.2.2)) := by
  obtain ⟨k, hk⟩ := C.named_tuple_eventually (C.oldCoordinate ∘ p.2.2) p.2.2
    (fun i ↦ C.oldCoordinate_names (p.2.2 i))
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨hu, hnames⟩ := hk (max k l) (Nat.le_max_left _ _)
    obtain ⟨ht, hh⟩ := evalAt_persistent (C.refines (Nat.le_max_right k l)) hl
    have hfit : ∀ i, (Fin.append ts (C.oldCoordinate ∘ p.2.2)) i < 1 + (C.point (max k l)).1 := by
      intro i
      cases i using Fin.addCases with
      | left i => simpa only [Fin.append_left] using ht i
      | right i => simpa only [Fin.append_right] using hu i
    refine ⟨max k l, hfit, ?_⟩
    intro a ha
    apply (ParameterInstance.eval_ofFormula (M := M) (S := S) p.2.1.1 p.2.1.2 _).mpr
    have he : (fun i ↦ a (RightCoordinate.index (hfit i))) =
        Fin.append (fun i ↦ a (RightCoordinate.index (ht i))) p.2.2 := by
      funext i
      cases i using Fin.addCases with
      | left i => simp only [Fin.append_left]
      | right i => simpa only [Fin.append_right] using congrFun (hnames a ha) i
    exact he.symm ▸ hh a ha
  · rintro ⟨l, hl⟩
    obtain ⟨hu, hnames⟩ := hk (max k l) (Nat.le_max_left _ _)
    obtain ⟨hfit, hh⟩ := evalAt_persistent (C.refines (Nat.le_max_right k l)) hl
    have ht (i : Fin n) : ts i < 1 + (C.point (max k l)).1 := by
      simpa only [Fin.append_left] using hfit (Fin.castAdd p.1 i)
    refine ⟨max k l, ht, ?_⟩
    intro a ha
    have hh' := (ParameterInstance.eval_ofFormula (M := M) (S := S) p.2.1.1 p.2.1.2 _).mp (hh a ha)
    have he : (fun i ↦ a (RightCoordinate.index (hfit i))) =
        Fin.append (fun i ↦ a (RightCoordinate.index (ht i))) p.2.2 := by
      funext i
      cases i using Fin.addCases with
      | left i => simp only [Fin.append_left]
      | right i => simpa only [Fin.append_right] using congrFun (hnames a ha) i
    change Formula.WeakEval M.Q p.2.1.1 (Fin.append (fun i ↦ a (RightCoordinate.index (ht i))) p.2.2)
    exact he ▸ hh'

end WeakModel.AdequateGenericChain
end ZFVP.Infinitary

