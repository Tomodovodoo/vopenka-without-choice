import ZFVP.ModelTheory.LocalSelectedUnionBound
import ZFVP.ModelTheory.TwoStepSelectedUnion
import ZFVP.ModelTheory.WoodinIterationRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem localCanonicalName_comp {n : ℕ}
    {a b c d e f : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hb : Language.DefinableFunction ℒₛₑₜ b)
    (hc : Language.DefinableFunction ℒₛₑₜ c) (hd : Language.DefinableFunction ℒₛₑₜ d)
    (he : Language.DefinableFunction ℒₛₑₜ e) (hf : Language.DefinableFunction ℒₛₑₜ f) :
    Language.DefinableFunction ℒₛₑₜ
      (fun v ↦ forcingLocalCanonicalName (a v) (b v) (c v) (d v) (e v) (f v)) :=
  Language.DefinableFunction.substitution (f := ![a, b, c, d, e, f]) forcingLocalCanonicalName_definable
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hb, hc, hd, he, hf])

private theorem selectedUnion_comp {n : ℕ}
    {a b c d e f : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hb : Language.DefinableFunction ℒₛₑₜ b)
    (hc : Language.DefinableFunction ℒₛₑₜ c) (hd : Language.DefinableFunction ℒₛₑₜ d)
    (he : Language.DefinableFunction ℒₛₑₜ e) (hf : Language.DefinableFunction ℒₛₑₜ f) :
    Language.DefinableFunction ℒₛₑₜ
      (fun v ↦ forcingSelectedUnion (a v) (b v) (c v) (d v) (e v) (f v)) :=
  Language.DefinableFunction.substitution (f := ![a, b, c, d, e, f]) forcingSelectedUnion_definable
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hb, hc, hd, he, hf])

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

/-- The fourth component of x stores the normalization cutoff. -/
noncomputable def woodinBoundTailName (x p Q E f : V) : V :=
  forcingLocalCanonicalName (woodinStagePoset x) (woodinStageOrder x) (woodinStageTop x)
    (woodinStageCardinal x) p
    (forcingSelectedUnion (woodinStagePoset x) (woodinStageOrder x) (woodinStageTop x)
      (twoStepNames Q ∅) (twoStepTailSelector (woodinStagePoset x) (woodinStageOrder x) Q ∅)
      (nameAction E f))

instance woodinBoundTailName_definable : Language.DefinableFunction₅ ℒₛₑₜ (woodinBoundTailName (V := V)) := by
  unfold woodinBoundTailName
  apply localCanonicalName_comp
  · definability
  · definability
  · definability
  · definability
  · definability
  · apply selectedUnion_comp <;> definability

theorem woodinBoundTailName_isName (x p Q E f : V) :
    IsForcingName (woodinStagePoset x) (woodinBoundTailName x p Q E f) :=
  forcingLocalCanonicalName_isName _ _ _ _ _ _

theorem woodinBoundTailName_mem {x : V}
    (hR : IsForcingPreorder (woodinStagePoset x) (woodinStageOrder x))
    (ht : IsForcingTop (woodinStagePoset x) (woodinStageOrder x) (woodinStageTop x))
    (hδ : IsChoicelessInaccessible (woodinStageCardinal x))
    (hP : woodinStagePoset x ∈ hierarchy (woodinStageCardinal x)) (p Q E f : V) :
    woodinBoundTailName x p Q E f ∈ forcingNameHierarchy (woodinStagePoset x) (woodinStageCardinal x) :=
  forcingLocalCanonicalName_mem hR ht hδ hP _ _

theorem woodinBoundTailName_empty {x p Q E f : V}
    (hR : IsForcingPreorder (woodinStagePoset x) (woodinStageOrder x))
    (he : p ∈ atomicEquality (woodinStagePoset x) (woodinStageOrder x)
      (forcingSelectedUnion (woodinStagePoset x) (woodinStageOrder x) (woodinStageTop x)
        (twoStepNames Q ∅) (twoStepTailSelector (woodinStagePoset x) (woodinStageOrder x) Q ∅)
        (nameAction E f)) ∅) :
    woodinBoundTailName x p Q E f = ∅ :=
  forcingLocalCanonicalName_empty_of_forced hR he

end ZFVP

