import ZFVP.ModelTheory.SaturatedPrefixSpecification
import ZFVP.SetTheory.EquivalentRetractionForcing
import ZFVP.SetTheory.ForcingRetractionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingRetraction.unique_relation_equality {n : ℕ}
    (φ : SetTheorySemisentence (n + 1))
    (hunique : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ v : Fin n → W, ∀ x y : W, φ.Evalb (x :> v) → φ.Evalb (y :> v) → x = y)
    {P R N T m one p : V} (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R)
    (ht : IsForcingTop N T one) (hp : p ∈ P)
    (v : Fin n → ForcingName P) (w : Fin n → ForcingName N)
    (x : ForcingName P) (y : ForcingName N)
    (heq : ∀ i, m ‘ p ∈ atomicEquality N T (nameAction m (v i).val) (w i).val)
    (hx : p ∈ forcingFormula P R φ (standardTuple (fun i ↦ ((x :> v) i).val)))
    (hy : m ‘ p ∈ forcingFormula N T φ (standardTuple (fun i ↦ ((y :> w) i).val))) :
    m ‘ p ∈ atomicEquality N T (nameAction m x.val) y.val := by
  let v' : Fin n → ForcingName N := fun j ↦
    ⟨nameAction m (v j).val, nameAction_isName hr.maps (v j).property⟩
  let x' : ForcingName N := ⟨nameAction m x.val, nameAction_isName hr.maps x.property⟩
  have hh := (hr.forcingFormula_nameAction_iff hR hT he φ
    (fun i ↦ ((x :> v) i).val) (fun i ↦ ((x :> v) i).property) hp).mp hx
  have hev : (fun i ↦ nameAction m ((x :> v) i).val) =
      (fun i ↦ ((x' :> v') i).val) := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  rw [hev] at hh
  exact forcingFormula_unique_equality_congr φ hunique hT ht (function_value_mem hr.maps hp)
    v' w x' y heq hh hy

theorem IsForcingRetraction.saturated_prefix_equality {P R N T m one κ δ p : V}
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R)
    (ht : IsForcingTop P R one) (ho : one ∈ N)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκ : κ ⊆ δ) (hp : p ∈ P) :
    m ‘ p ∈ atomicEquality N T
      (nameAction m (saturatedWoodinPrefixPosetName P R one κ δ))
      (saturatedWoodinPrefixPosetName N T one κ δ) := by
  let := hδ.1
  have hN := subset_mem_hierarchy_limit hδ.rankCriterion.2.2.1 hP hr.inclusion
  have htN := hr.top_of_mem ht ho
  refine hr.unique_relation_equality totalWoodinCollapseFormula ?_ hR hT he htN hp
    ![⟨checkName one κ, checkName_isName ht.1 κ⟩, ⟨checkName one δ, checkName_isName ht.1 δ⟩]
    ![⟨checkName one κ, checkName_isName ho κ⟩, ⟨checkName one δ, checkName_isName ho δ⟩]
    ⟨_, saturatedWoodinPrefixPosetName_isName P R one κ δ⟩
    ⟨_, saturatedWoodinPrefixPosetName_isName N T one κ δ⟩ ?_ ?_ ?_
  · intro W _ _ _ v x y hx hy
    exact ((totalWoodinCollapseFormula_defined.iff _).mp hx).trans
      ((totalWoodinCollapseFormula_defined.iff _).mp hy).symm
  · have hc (a : V) : m ‘ p ∈ atomicEquality N T (nameAction m (checkName one a)) (checkName one a) := by
      rw [nameAction_checkName ht.1 (hr.fixes one ho), atomicEquality_refl hT]
      exact function_value_mem hr.maps hp
    intro i
    exact Fin.cases (hc κ) (fun j ↦ Fin.cases (hc δ) (fun k ↦ Fin.elim0 k) j) i
  · exact saturatedWoodinPrefixPosetName_forces hR ht hδ hP hκ hp
  · exact saturatedWoodinPrefixPosetName_forces hT htN hδ hN hκ (function_value_mem hr.maps hp)

theorem IsForcingRetraction.reverse_order_equality {P R N T m one p : V}
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R)
    (ht : IsForcingTop P R one) (ho : one ∈ N) (hp : p ∈ P)
    (U : ForcingName P) (W : ForcingName N)
    (hUW : m ‘ p ∈ atomicEquality N T (nameAction m U.val) W.val) :
    m ‘ p ∈ atomicEquality N T (nameAction m (reverseInclusionOrderName P R U.val))
      (reverseInclusionOrderName N T W.val) := by
  refine hr.unique_relation_equality piOneReverseInclusionOrderFormula ?_ hR hT he
    (hr.top_of_mem ht ho) hp ![U] ![W]
    ⟨_, reverseInclusionOrderName_isName P R U.val⟩
    ⟨_, reverseInclusionOrderName_isName N T W.val⟩ ?_ ?_ ?_
  · intro W _ _ _ v x y hx hy
    exact ((piOneReverseInclusionOrderFormula_defined.iff _).mp hx).trans
      ((piOneReverseInclusionOrderFormula_defined.iff _).mp hy).symm
  · intro i
    exact Fin.cases hUW (fun j ↦ Fin.elim0 j) i
  · exact reverseInclusionOrderName_forces hR ht hp U
  · exact reverseInclusionOrderName_forces hT (hr.top_of_mem ht ho) (function_value_mem hr.maps hp) W

end ZFVP
