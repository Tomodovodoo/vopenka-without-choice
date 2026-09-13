import ZFVP.ModelTheory.HartogsRestorationForcingAgreementCountable
import ZFVP.ModelTheory.RankInternalHartogsName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eventually_rank_hartogsRestoration_forcing_eq_countable [Countable V]
    {δ κ γ P R one : V} (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ)
    (hκγ : κ ∈ γ) (hγδ : γ ∈ δ)
    (hγ : IsChoicelessInaccessible γ) (hPγ : P ∈ hierarchy γ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R (checkName one κ)])) :
    ∃ β ∈ δ, γ ∈ β ∧ ∀ ξ, β ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ p r o k d : SetDomain (hierarchy ξ),
        p.val = P → r.val = R → o.val = one → k.val = κ → d.val = γ →
        (forcingFormula p r woodinLocalRestorationFormula
          (standardTuple ![hartogsNumberName p r (checkName o k), checkName o d])).val =
        forcingFormula P R woodinLocalRestorationFormula
          (standardTuple ![hartogsNumberName P R (checkName one κ), checkName one γ]) := by
  obtain ⟨β, hβ, hγβ, hall⟩ := eventually_hartogs_rank_localRestoration_iff_countable
    hδ hP hκγ hγδ hγ hPγ hR ht hκ
  refine ⟨β, hβ, hγβ, ?_⟩
  intro ξ hβξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  intro p r o k d hp hr ho hk hd
  have htop : IsForcingTop p r o := (TransitiveZF.forcingTop_iff (hierarchy ξ) p r o).mpr
    (by simpa only [hp, hr, ho] using ht)
  let v : Fin 2 → ForcingName p :=
    ![⟨hartogsNumberName p r (checkName o k), hartogsNumberName_isName _ _ _⟩,
      ⟨checkName o d, checkName_isName htop.1 d⟩]
  have hn : (fun i ↦ (v i).val) =
      ![hartogsNumberName p r (checkName o k), checkName o d] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun z ↦ Fin.elim0 z) j) i
  have he := TransitiveZF.forcingFormula_standardTuple_val (hierarchy ξ) p r
    woodinLocalRestorationFormula (fun i ↦ (v i).val)
  rw [hn, hp, hr] at he
  have he' : (forcingFormula p r woodinLocalRestorationFormula
      (standardTuple ![hartogsNumberName p r (checkName o k), checkName o d])).val =
      classForcingFormula P R (IsLowRankForcingName P ξ) (by definability)
        woodinLocalRestorationFormula (standardTuple (fun i ↦ (v i).val.val)) := by
    convert he using 1
    rfl
  rw [he']
  apply IsForcingRegular.eq_of_all_generics hR
    (classForcingFormula_regular _ _ hR _ _) (forcingFormula_regular hR _ _)
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  let v' : Fin 2 → ForcingName P := fun i ↦ A.rankInternalName p hp (v i)
  have hv : ∀ i, (v' i).val ∈ hierarchy ξ := fun i ↦ (v i).val.property
  let u : Fin 2 → ForcingName P :=
    ![⟨hartogsNumberName P R (checkName one κ), hartogsNumberName_isName _ _ _⟩,
      ⟨checkName one γ, checkName_isName ht.1 γ⟩]
  have hun : (fun i ↦ (u i).val) =
      ![hartogsNumberName P R (checkName one κ), checkName one γ] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun z ↦ Fin.elim0 z) j) i
  have hi := A.check_inaccessible_of_small hξ (show P ∈ hierarchy ξ from hp ▸ p.property)
  let := hi.1
  let := rankDomain_nonempty hi.2.1
  let := hi.rankCriterion.models_zf
  let w : Fin 2 → SetDomain (hierarchy (A.check ξ)) := fun i ↦ A.rankInternalValue hξ p hp (v i)
  have hwk : (w 0).val = hartogsNumber (A.check κ) := by
    have h := A.rankInternalCheckedHartogs_value hξ p r o k hp hr ho htop.1
    simpa [w, v, ForcingContext.rankInternalValue, hk] using h
  have hwd : (w 1).val = A.check γ := by
    have h := A.rankInternalValue_check_val hξ p o d hp ho htop.1
    simpa [w, v, hd] using h
  have hl := hall G hG (A.check ξ) ((A.check_mem_iff _ _).mpr hβξ) hi (w 0) (w 1) hwk hwd
  let τ : ForcingName P := ⟨checkName one κ, checkName_isName ht.1 κ⟩
  have huk : A.ofName (u 0) = hartogsNumber (A.check κ) := A.hartogsName_value τ
  have hl' : IsWoodinLocalRestoration (w 0) (w 1) ↔
      IsWoodinLocalRestoration (A.ofName (u 0)) (A.ofName (u 1)) := by
    rw [huk]
    exact hl
  have hw : woodinLocalRestorationFormula.Evalb w ↔
      woodinLocalRestorationFormula.Evalb (fun i ↦ A.ofName (u i)) :=
    (Defined.eval_iff (φ := woodinLocalRestorationFormula) w).trans
      (hl'.trans (Defined.eval_iff (φ := woodinLocalRestorationFormula)
        (fun i ↦ A.ofName (u i))).symm)
  have ht' := A.rankName_formula_truth_of_inaccessible hξ (show P ∈ hierarchy ξ from hp ▸ p.property)
    woodinLocalRestorationFormula v' hv
  have hf := A.formula_truth woodinLocalRestorationFormula u
  have hh := ht'.symm.trans (hw.trans hf)
  simpa only [hun, v', A, ForcingContext.rankInternalName, IsLowRankForcingName] using hh

end ZFVP
