import ZFVP.ModelTheory.WoodinSourceCutoff
import ZFVP.ModelTheory.ForcingIsomorphismTwoStep
import ZFVP.SetTheory.NameActionClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem twoStepOrder_eq_of_forced_equality {P R N T T' t : V}
    (hR : IsForcingPreorder P R) (he : ∀ p ∈ P, p ∈ atomicEquality P R T T') :
    twoStepOrder P R N T t = twoStepOrder P R N T' t := by
  apply mem_ext
  intro z
  simp only [twoStepOrder, mem_sep_iff]
  apply and_congr_right
  intro hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
  obtain ⟨p, hp, τ, _, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  apply and_congr Iff.rfl
  apply classForcingFormula_congr hR (IsForcingName P) (by definability)
    boundedPairMemberFormula _ _ hp
  intro i
  exact Fin.cases (he p hp) (fun j ↦ Fin.cases
    ((atomicEquality_refl hR τ).symm ▸ hp)
    (fun k ↦ Fin.cases ((atomicEquality_refl hR (kpair.π₂ b)).symm ▸ hp)
      (fun l ↦ Fin.elim0 l) k) j) i

theorem IsForcingIsomorphism.reverse_order_name_equality {P R Q S f one top p : V}
    (hf : IsForcingIsomorphism P R Q S f)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top) (hp : p ∈ P)
    (N : ForcingName P) (N' : ForcingName Q)
    (he : f ‘ p ∈ atomicEquality Q S (nameAction f N.val) N'.val) :
    f ‘ p ∈ atomicEquality Q S (nameAction f (reverseInclusionOrderName P R N.val))
      (reverseInclusionOrderName Q S N'.val) := by
  refine hf.unique_relation_equality piOneReverseInclusionOrderFormula ?_ hR hS ht' hp ![N] ![N']
    ⟨_, reverseInclusionOrderName_isName _ _ _⟩ ⟨_, reverseInclusionOrderName_isName _ _ _⟩ ?_ ?_ ?_
  · intro W _ _ _ v x y hx hy
    have hx' : x = reverseInclusionOrder (v 0) := (piOneReverseInclusionOrderFormula_defined.iff _).mp hx
    have hy' : y = reverseInclusionOrder (v 0) := (piOneReverseInclusionOrderFormula_defined.iff _).mp hy
    exact hx'.trans hy'.symm
  · intro i
    exact Fin.cases he (fun j ↦ Fin.elim0 j) i
  · exact reverseInclusionOrderName_forces hR ht hp N
  · exact reverseInclusionOrderName_forces hS ht' (function_value_mem hf.1 hp) N'

theorem twoStep_reverse_order_isomorphism {P R Q S f one top N : V}
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (hf : IsForcingIsomorphism P R Q S f)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top) (hN : IsForcingName P N) :
    IsForcingIsomorphism (twoStepConditions P R N ∅)
      (twoStepOrder P R N (reverseInclusionOrderName P R N) ∅)
      (twoStepConditions Q S (nameAction f N) ∅)
      (twoStepOrder Q S (nameAction f N) (reverseInclusionOrderName Q S (nameAction f N)) ∅)
      (twoStepIsomorphismMap P R N ∅ f) := by
  have hh := twoStep_isomorphism hR hS hf hN
    (reverseInclusionOrderName_isName P R N) (empty_forcingName P)
  rw [nameAction_empty] at hh
  have he : twoStepOrder Q S (nameAction f N) (nameAction f (reverseInclusionOrderName P R N)) ∅ =
      twoStepOrder Q S (nameAction f N) (reverseInclusionOrderName Q S (nameAction f N)) ∅ := by
    apply twoStepOrder_eq_of_forced_equality hS
    intro q hq
    have hp := function_value_mem hf.inverse_maps hq
    have he := hf.reverse_order_name_equality hR hS ht ht' hp
      ⟨N, hN⟩ ⟨nameAction f N, nameAction_isName hf.1 hN⟩
      ((atomicEquality_refl hS (nameAction f N)).symm ▸ function_value_mem hf.1 hp)
    simpa only [hf.value_inverse hq] using he
  rw [he] at hh
  exact hh

theorem saturatedHartogsCollapse_isomorphism {P R Q S f one top ζ : V} [IsOrdinal ζ]
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (hf : IsForcingIsomorphism P R Q S f)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top)
    (hft : f ‘ one = top) (γ δ : V) :
    let N := saturatedWoodinCollapseName P R ζ
      (hartogsNumberName P R (checkName one γ)) (checkName one δ)
    let N' := saturatedWoodinCollapseName Q S ζ
      (hartogsNumberName Q S (checkName top γ)) (checkName top δ)
    IsForcingIsomorphism (twoStepConditions P R N ∅)
      (twoStepOrder P R N (reverseInclusionOrderName P R N) ∅)
      (twoStepConditions Q S N' ∅)
      (twoStepOrder Q S N' (reverseInclusionOrderName Q S N') ∅)
      (twoStepIsomorphismMap P R N ∅ f) := by
  dsimp only
  have hn : IsForcingName P (saturatedWoodinCollapseName P R ζ
      (hartogsNumberName P R (checkName one γ)) (checkName one δ)) :=
    forcingSaturatedName_isName _ _ _ _
  have hh := twoStep_reverse_order_isomorphism hR hS hf ht ht' hn
  rw [hf.saturated_hartogs_collapse hR hS ht ht' hft γ δ] at hh
  exact hh

end ZFVP
