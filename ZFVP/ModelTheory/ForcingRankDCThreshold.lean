import ZFVP.SetTheory.RankDCThreshold
import ZFVP.ModelTheory.ForcingRankDependentChoiceAgreement
import ZFVP.ModelTheory.ForcingUniformOrdinalBound
import ZFVP.ModelTheory.ForcingFormulaName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def rankDCThresholdName (P R one γ : V) : ForcingName P :=
  ⟨formulaUniqueName P R leastRankDCThresholdFormula (standardTuple ![checkName one γ]),
    formulaUniqueName_isName _ _ _ _⟩

theorem ForcingContext.rankDCThresholdName_value (A : ForcingContext V) (γ : V) :
    A.ofName (rankDCThresholdName A.P A.R A.one γ) = leastRankDCThreshold (A.check γ) := by
  let v : Fin 1 → ForcingName A.P := ![⟨checkName A.one γ, checkName_isName A.top.1 γ⟩]
  have hv : (fun i ↦ A.ofName (v i)) = ![A.check γ] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  have he : ∀ x : A.Model, leastRankDCThresholdFormula.Evalb (x :> (fun i ↦ A.ofName (v i))) ↔
      x = leastRankDCThreshold (A.check γ) := by
    intro x
    rw [hv]
    exact eval_leastRankDCThresholdFormula x (A.check γ)
  have h := A.formulaName_value leastRankDCThresholdFormula v
    (fun x y hx hy ↦ ((he x).mp hx).trans ((he y).mp hy).symm)
    ((he _).mpr rfl)
  exact h

theorem ForcingContext.leastRankDCThreshold_mem (A : ForcingContext V)
    {δ γ : V} (hδ : IsWoodinSupercompact δ) (hP : A.P ∈ hierarchy δ) (hγ : γ ∈ δ) :
    leastRankDCThreshold (A.check γ) ∈ A.check δ ∧
      IsRankDCThreshold (A.check γ) (leastRankDCThreshold (A.check γ)) := by
  let := hδ.1.1
  obtain ⟨η, hη, hγη, hall⟩ := A.eventually_rank_dependentChoice_iff hδ hP hγ
  exact leastRankDCThreshold_spec ((A.check_mem_iff _ _).mpr hη)
    ((rankDCThreshold_iff _ _).mpr ⟨(A.check_mem_iff _ _).mpr hγη, hall⟩)

theorem uniform_rankDCThreshold_all_generics {δ γ P R one : V}
    (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ) (hγ : γ ∈ δ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) :
    ∃ β ∈ δ, γ ∈ β ∧ ∀ G : Set V, ∀ hG : IsExternalForcingGeneric P R G,
      let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
      IsRankDCThreshold (A.check γ) (A.check β) := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hγ
  obtain ⟨b, hb, hall⟩ := forcingName_ordinal_bound_all_generics hδ.inaccessible hP hR ht
    (rankDCThresholdName P R one γ)
  let := IsOrdinal.of_mem hb
  let := ordinal_union_ordinal b γ
  let β := succ (b ∪ γ)
  have hβ : β ∈ δ := regularCardinal_succ_closed hδ.inaccessible.regular (ordinal_union_mem hb hγ)
  have hbβ : b ∈ β := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (subset_union_left b γ))
  have hγβ : γ ∈ β := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (subset_union_right b γ))
  refine ⟨β, hβ, hγβ, ?_⟩
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  change IsRankDCThreshold (A.check γ) (A.check β)
  obtain ⟨hm, hs⟩ := A.leastRankDCThreshold_mem hδ hP hγ
  have he := A.rankDCThresholdName_value γ
  have hsmall : leastRankDCThreshold (A.check γ) ∈ A.check b := by
    rw [← he]
    exact hall G hG (he.symm ▸ hm)
  exact hs.mono (IsOrdinal.toIsTransitive.mem_trans hsmall ((A.check_mem_iff _ _).mpr hbβ))

end ZFVP
