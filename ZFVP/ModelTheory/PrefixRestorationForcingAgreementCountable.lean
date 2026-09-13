import ZFVP.ModelTheory.PrefixLocalRestorationRankAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eventually_prefixRestoration_forcing_eq_countable [Countable V]
    {δ κ γ P R one : V} (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ)
    (hκδ : κ ∈ δ) (hγδ : γ ∈ δ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![checkName one κ])) :
    ∃ β ∈ δ, γ ∈ β ∧ ∀ ξ, β ∈ ξ → IsChoicelessInaccessible ξ → P ∈ hierarchy ξ →
      checkName one κ ∈ hierarchy ξ → checkName one γ ∈ hierarchy ξ →
      classForcingFormula P R (IsLowRankForcingName P ξ) (by definability)
        woodinLocalRestorationFormula (standardTuple ![checkName one κ, checkName one γ]) =
      forcingFormula P R woodinLocalRestorationFormula
        (standardTuple ![checkName one κ, checkName one γ]) := by
  obtain ⟨β, hβ, hγβ, hall⟩ := eventually_prefix_rank_localRestoration_iff_countable
    hδ hP hκδ hγδ hR ht hκ
  refine ⟨β, hβ, hγβ, ?_⟩
  intro ξ hβξ hξ hPξ hkξ hdξ
  apply IsForcingRegular.eq_of_all_generics hR
    (classForcingFormula_regular _ _ hR _ _) (forcingFormula_regular hR _ _)
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  let v : Fin 2 → ForcingName P :=
    ![⟨checkName one κ, checkName_isName ht.1 κ⟩, ⟨checkName one γ, checkName_isName ht.1 γ⟩]
  have hv : ∀ i, (v i).val ∈ hierarchy ξ := by
    intro i
    exact Fin.cases hkξ (fun j ↦ Fin.cases hdξ (fun z ↦ Fin.elim0 z) j) i
  have hi := A.check_inaccessible_of_small hξ hPξ
  let := hi.1
  let := rankDomain_nonempty hi.2.1
  let := hi.rankCriterion.models_zf
  let w : Fin 2 → SetDomain (hierarchy (A.check ξ)) := fun i ↦
    ⟨A.ofName (v i), (A.mem_checked_hierarchy_iff_low_name_of_inaccessible hξ hPξ _).mpr
      ⟨v i, hv i, rfl⟩⟩
  have hl := hall G hG (A.check ξ) ((A.check_mem_iff _ _).mpr hβξ) hi (w 0) (w 1) rfl rfl
  have he := A.rankName_formula_truth_of_inaccessible hξ hPξ woodinLocalRestorationFormula v hv
  have hf := A.formula_truth woodinLocalRestorationFormula v
  have hw : woodinLocalRestorationFormula.Evalb w ↔
      woodinLocalRestorationFormula.Evalb (fun i ↦ A.ofName (v i)) :=
    (Defined.eval_iff (φ := woodinLocalRestorationFormula) w).trans
      (hl.trans (Defined.eval_iff (φ := woodinLocalRestorationFormula)
        (fun i ↦ A.ofName (v i))).symm)
  have hn : (fun i ↦ (v i).val) = ![checkName one κ, checkName one γ] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun z ↦ Fin.elim0 z) j) i
  have hh := he.symm.trans (hw.trans hf)
  simpa only [hn] using hh

end ZFVP
