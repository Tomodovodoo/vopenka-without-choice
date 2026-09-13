import ZFVP.ModelTheory.ForcingUniqueRelation
import ZFVP.SetTheory.ClassForcingCongruence
import ZFVP.ModelTheory.ForcingHartogsName
import ZFVP.ModelTheory.SaturatedCollapseBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingFormula_unique_equality_congr {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (hunique : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ v : Fin n → W, ∀ x y : W, φ.Evalb (x :> v) → φ.Evalb (y :> v) → x = y)
    {P R one p : V} (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P)
    (v w : Fin n → ForcingName P) (x y : ForcingName P)
    (he : ∀ i, p ∈ atomicEquality P R (v i).val (w i).val)
    (hx : p ∈ forcingFormula P R φ (standardTuple (fun i ↦ ((x :> v) i).val)))
    (hy : p ∈ forcingFormula P R φ (standardTuple (fun i ↦ ((y :> w) i).val))) :
    p ∈ atomicEquality P R x.val y.val := by
  have hh := classForcingFormula_congr hR (IsForcingName P) (by definability) φ
    (fun i ↦ ((x :> v) i).val) (fun i ↦ ((x :> w) i).val) hp (by
      intro i
      exact Fin.cases ((atomicEquality_refl hR x.val).symm ▸ hp) he i)
  exact forcingFormula_unique_equality φ hunique hR ht hp w x y (hh.mp hx) hy

theorem IsForcingIsomorphism.unique_relation_equality {n : ℕ}
    (φ : SetTheorySemisentence (n + 1))
    (hunique : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ v : Fin n → W, ∀ x y : W, φ.Evalb (x :> v) → φ.Evalb (y :> v) → x = y)
    {P R Q S f one p : V} (hf : IsForcingIsomorphism P R Q S f)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop Q S one) (hp : p ∈ P)
    (v : Fin n → ForcingName P) (w : Fin n → ForcingName Q)
    (x : ForcingName P) (y : ForcingName Q)
    (he : ∀ i, f ‘ p ∈ atomicEquality Q S (nameAction f (v i).val) (w i).val)
    (hx : p ∈ forcingFormula P R φ (standardTuple (fun i ↦ ((x :> v) i).val)))
    (hy : f ‘ p ∈ forcingFormula Q S φ (standardTuple (fun i ↦ ((y :> w) i).val))) :
    f ‘ p ∈ atomicEquality Q S (nameAction f x.val) y.val := by
  let v' : Fin n → ForcingName Q := fun j ↦
    ⟨nameAction f (v j).val, nameAction_isName hf.1 (v j).property⟩
  let x' : ForcingName Q := ⟨nameAction f x.val, nameAction_isName hf.1 x.property⟩
  have hh := (forcingFormula_isomorphism_iff hR hS hf φ
    (fun i ↦ ((x :> v) i).val) (fun i ↦ ((x :> v) i).property) hp).mpr hx
  have hev : (fun i ↦ nameAction f ((x :> v) i).val) =
      (fun i ↦ ((x' :> v') i).val) := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  rw [hev] at hh
  exact forcingFormula_unique_equality_congr φ hunique hS ht (function_value_mem hf.1 hp)
    v' w x' y he hh hy

theorem IsForcingIsomorphism.hartogs_name_equality {P R Q S f one top p : V}
    (hf : IsForcingIsomorphism P R Q S f)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top) (hp : p ∈ P)
    (τ : ForcingName P) (υ : ForcingName Q)
    (he : f ‘ p ∈ atomicEquality Q S (nameAction f τ.val) υ.val) :
    f ‘ p ∈ atomicEquality Q S (nameAction f (hartogsNumberName P R τ.val))
      (hartogsNumberName Q S υ.val) := by
  refine hf.unique_relation_equality hartogsNumberFormula ?_ hR hS ht' hp ![τ] ![υ]
    ⟨_, hartogsNumberName_isName _ _ _⟩ ⟨_, hartogsNumberName_isName _ _ _⟩ ?_ ?_ ?_
  · intro W _ _ _ v x y hx hy
    have hx' : x = hartogsNumber (v 0) := (hartogsNumberFormula_defined.iff _).mp hx
    have hy' : y = hartogsNumber (v 0) := (hartogsNumberFormula_defined.iff _).mp hy
    exact hx'.trans hy'.symm
  · intro i
    exact Fin.cases he (fun j ↦ Fin.elim0 j) i
  · exact hartogsNumberName_forces hR ht hp τ
  · exact hartogsNumberName_forces hS ht' (function_value_mem hf.1 hp) υ

theorem IsForcingIsomorphism.collapse_name_equality {P R Q S f one top p : V}
    (hf : IsForcingIsomorphism P R Q S f)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top) (hp : p ∈ P)
    (κ δ : ForcingName P) (κ' δ' : ForcingName Q)
    (hκ : f ‘ p ∈ atomicEquality Q S (nameAction f κ.val) κ'.val)
    (hδ : f ‘ p ∈ atomicEquality Q S (nameAction f δ.val) δ'.val) :
    f ‘ p ∈ atomicEquality Q S (nameAction f (woodinCollapseName P R κ.val δ.val))
      (woodinCollapseName Q S κ'.val δ'.val) := by
  refine hf.unique_relation_equality totalWoodinCollapseFormula ?_ hR hS ht' hp ![κ, δ] ![κ', δ']
    ⟨_, woodinCollapseName_isName _ _ _ _⟩ ⟨_, woodinCollapseName_isName _ _ _ _⟩ ?_ ?_ ?_
  · intro W _ _ _ v x y hx hy
    have hx' : x = totalWoodinCollapse (v 0) (v 1) := (totalWoodinCollapseFormula_defined.iff _).mp hx
    have hy' : y = totalWoodinCollapse (v 0) (v 1) := (totalWoodinCollapseFormula_defined.iff _).mp hy
    exact hx'.trans hy'.symm
  · intro i
    exact Fin.cases hκ (fun j ↦ Fin.cases hδ (fun k ↦ Fin.elim0 k) j) i
  · exact woodinCollapseName_forces hR ht hp κ δ
  · exact woodinCollapseName_forces hS ht' (function_value_mem hf.1 hp) κ' δ'

theorem IsForcingIsomorphism.saturated_hartogs_collapse {P R Q S f one top ζ : V}
    [IsOrdinal ζ] (hf : IsForcingIsomorphism P R Q S f)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top)
    (hft : f ‘ one = top) (γ δ : V) :
    nameAction f (saturatedWoodinCollapseName P R ζ
      (hartogsNumberName P R (checkName one γ)) (checkName one δ)) =
      saturatedWoodinCollapseName Q S ζ
        (hartogsNumberName Q S (checkName top γ)) (checkName top δ) := by
  unfold saturatedWoodinCollapseName
  rw [hf.saturated_name (woodinCollapseName_isName _ _ _ _)]
  apply forcingSaturatedName_eq_of_forced_equality hS
  intro q hq
  have hp := function_value_mem hf.inverse_maps hq
  have hc (a : V) : (f ‘ ((converseGraph f) ‘ q)) ∈ atomicEquality Q S
      (nameAction f (checkName one a)) (checkName top a) := by
    rw [nameAction_checkName_map ht.1, hft, atomicEquality_refl hS, hf.value_inverse hq]
    exact hq
  have hh := hf.hartogs_name_equality hR hS ht ht' hp
    ⟨checkName one γ, checkName_isName ht.1 _⟩
    ⟨checkName top γ, checkName_isName ht'.1 _⟩ (hc γ)
  have he := hf.collapse_name_equality hR hS ht ht' hp
    ⟨_, hartogsNumberName_isName _ _ _⟩ ⟨_, checkName_isName ht.1 δ⟩
    ⟨_, hartogsNumberName_isName _ _ _⟩ ⟨_, checkName_isName ht'.1 δ⟩ hh (hc δ)
  simpa only [hf.value_inverse hq] using he

end ZFVP
