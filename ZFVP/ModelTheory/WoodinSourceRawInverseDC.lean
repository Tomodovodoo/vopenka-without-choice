import ZFVP.ModelTheory.WoodinSourceCompletedInverse
import ZFVP.ModelTheory.WoodinRawInverseDC

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def WoodinSourceRawInverseDC (θ : V) : Prop :=
  let θ' := woodinSourceIndex θ
  let s' := woodinSourceCode θ (woodinIterationPrefix θ)
  let γ := woodinLimitCardinal (woodinSourceCardinals θ (woodinIterationCardinalPrefix θ))
  ∀ p ∈ forcingInverseCodePoset θ' s',
    p ∈ forcingFormula (forcingInverseCodePoset θ' s') (forcingInverseCodeOrder θ' s')
      woodinStageCardinalFormula (standardTuple ![forcingInverseHartogsName θ' s' γ])

theorem woodinSourceRawInverseDC {δ θ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
    (hθ : θ ∈ δ) (hzero : θ ≠ ∅) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    WoodinSourceRawInverseDC θ := by
  let := hδ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have h0 : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left
    (fun he ↦ hzero he.symm)
  have hx := woodinIterationExit hδ hAC
  have hi := woodinIterationPrefix_of_stages
    (fun i hi ↦ (hx.2.1 i (IsOrdinal.toIsTransitive.mem_trans hi hθ)).1)
  have hc := hi.code.system.inverseColumn h0 hi.code.subset_universe
  have hs' := woodinSourceCode_valid hi.code
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hc' := hs'.system.inverseColumn hz hs'.subset_universe
  let P := forcingInverseCodePoset θ (woodinIterationPrefix θ)
  let R := forcingInverseCodeOrder θ (woodinIterationPrefix θ)
  let one := forcingInverseCodeTop θ (woodinIterationPrefix θ)
  let Q := forcingInverseCodePoset (woodinSourceIndex θ) (woodinSourceCode θ (woodinIterationPrefix θ))
  let S := forcingInverseCodeOrder (woodinSourceIndex θ) (woodinSourceCode θ (woodinIterationPrefix θ))
  let top := forcingInverseCodeTop (woodinSourceIndex θ) (woodinSourceCode θ (woodinIterationPrefix θ))
  let f := woodinSeedThreadMap θ P
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
  have hf : IsForcingIsomorphism P R Q S f := woodinSourceCode_inverse_isomorphism hi.code
  have hR : IsForcingPreorder P R := hc.order.preorder
  have hS : IsForcingPreorder Q S := hc'.order.preorder
  have ht : IsForcingTop P R one := hc.tops.top
  have ht' : IsForcingTop Q S top := hc'.tops.top
  have hft : f ‘ one = top := woodinSourceCode_inverse_top_value hi.code h0
  dsimp only [WoodinSourceRawInverseDC]
  rw [woodinSourceCardinals_actual_prefix_limit hδ hAC
    (IsOrdinal.toIsTransitive.transitive _ hθ) h0]
  intro q hq
  have hp := function_value_mem hf.inverse_maps hq
  have he := hf.hartogs_name_equality hR hS ht ht' hp
    ⟨checkName one γ, checkName_isName ht.1 _⟩
    ⟨checkName top γ, checkName_isName ht'.1 _⟩ (by
      change f ‘ ((converseGraph f) ‘ q) ∈ atomicEquality Q S
        (nameAction f (checkName one γ)) (checkName top γ)
      rw [nameAction_checkName_map ht.1, hft, atomicEquality_refl hS]
      exact function_value_mem hf.1 hp)
  let τ : ForcingName P := ⟨hartogsNumberName P R (checkName one γ), hartogsNumberName_isName _ _ _⟩
  let υ : ForcingName Q := ⟨hartogsNumberName Q S (checkName top γ), hartogsNumberName_isName _ _ _⟩
  have hh := (forcingFormula_isomorphism_congr_iff hR hS hf
    woodinStageCardinalFormula ![τ] ![υ] hp (fun i ↦ Fin.cases he (fun j ↦ Fin.elim0 j) i)).mpr
      (woodinRawInverseDC hδ hθ hzero hlim hn _ hp)
  have hw : (fun i : Fin 1 ↦ ((![υ] : Fin 1 → ForcingName Q) i).val) = ![υ.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [hw, hf.value_inverse hq] at hh
  exact hh

end ZFVP
