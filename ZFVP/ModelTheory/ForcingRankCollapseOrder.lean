import ZFVP.ModelTheory.ForcingRankFormulaNames
import ZFVP.ModelTheory.ForcingSemanticConsequence
import ZFVP.SetTheory.WoodinCollapseProjection
import ZFVP.ModelTheory.TwoStepCombinationFilter

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedOrderRowFormula : SetTheorySemisentence 2 :=
  “z Q. ∃ p ∈ Q, ∃ q ∈ Q, !boundedKpairFormula z p q ∧ !isSubsetOf q p”

theorem boundedOrderRowFormula_bounded : IsBoundedSetFormula boundedOrderRowFormula :=
  .exs (.bvar 1) (.exs (.bvar 2) (.and (boundedKpairFormula_bounded.subst _)
    (isSubsetOf_bounded.subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedOrderRowFormula (z Q : V) :
    boundedOrderRowFormula.Evalb ![z, Q] ↔ z ∈ reverseInclusionOrder Q := by
  have hh : boundedOrderRowFormula.Evalb ![z, Q] ↔
      ∃ p ∈ Q, ∃ q ∈ Q, z = ⟨p, q⟩ₖ ∧ q ⊆ p := by simp [boundedOrderRowFormula]
  rw [hh]
  constructor
  · rintro ⟨p, hp, q, hq, rfl, hs⟩
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hp, hq, hs⟩
  · intro hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    exact ⟨p, hp, q, hq, rfl, ((pair_mem_reverseInclusionOrder _ _ _).mp hz).2.2⟩

noncomputable def rankOrderName (P R δ Q : V) : V :=
  rankFormulaName P R δ boundedOrderRowFormula ![Q]

theorem rankOrderName_isName (P R δ Q : V) : IsForcingName P (rankOrderName P R δ Q) :=
  rankFormulaName_isName _ _ _ _ _

theorem successorRankEmbedding_value_rankOrderName {ρ γ e P R δ Q : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hP : P ∈ hierarchy ρ) (hR : R ∈ hierarchy ρ) (hδ : IsOrdinal δ) (hδρ : δ ∈ hierarchy ρ)
    (hord : IsForcingPreorder P R) (hord' : IsForcingPreorder (e ‘ P) (e ‘ R))
    (hQ : Q ∈ hierarchy ρ) (hn : IsForcingName P Q) :
    e ‘ (rankOrderName P R δ Q) = rankOrderName (e ‘ P) (e ‘ R) (e ‘ δ) (e ‘ Q) := by
  unfold rankOrderName
  rw [successorRankEmbedding_value_rankFormulaName hρ hγ he hP hR hδ hδρ hord hord'
    (.bounded boundedOrderRowFormula_bounded) _ (by simpa using hQ) (by simpa using hn)]
  rfl

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def rankOrder (δ : V) (Q : ForcingName A.P) : ForcingName A.P :=
  ⟨rankOrderName A.P A.R δ Q.val, rankOrderName_isName _ _ _ _⟩

theorem rankOrder_value {δ : V} (hδ : IsChoicelessInaccessible δ)
    (hP : A.P ∈ hierarchy δ) (Q : ForcingName A.P) (hQ : A.ofName Q ⊆ hierarchy (A.check δ)) :
    A.ofName (A.rankOrder δ Q) = reverseInclusionOrder (A.ofName Q) := by
  have hn : A.rankOrder δ Q = A.rankSelectedName δ boundedOrderRowFormula ![Q] := rfl
  rw [hn]
  apply mem_ext
  intro z
  have hv : A.ofName ∘ (![Q] : Fin 1 → ForcingName A.P) = ![A.ofName Q] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [A.rankSelectedName_value hδ hP, hv, eval_boundedOrderRowFormula]
  refine ⟨And.right, fun hz ↦ ⟨?_, hz⟩⟩
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  have hi := A.check_inaccessible_of_small hδ hP
  let := hi.1
  exact kpair_mem_hierarchy_limit hi.rankCriterion.2.2.1 (hQ p hp) (hQ q hq)

theorem rankCollapseOrder_value {κ δ : V} (hδ : IsChoicelessInaccessible δ)
    (hP : A.P ∈ hierarchy δ) (hκ : κ ⊆ δ) :
    A.ofName (A.rankOrder δ (A.rankCollapse κ δ)) =
      reverseInclusionOrder (woodinCollapse (A.check κ) (A.check δ)) := by
  rw [A.rankOrder_value hδ hP, A.rankCollapse_value hδ hP hκ]
  rw [A.rankCollapse_value hδ hP hκ]
  exact fun _ hp ↦ woodinCollapse_condition_mem_hierarchy
    (A.check_inaccessible_of_small hδ hP).regular ((A.checkEmbedding.subset_iff _ _).mpr hκ) hp

end ForcingContext

theorem rankCollapse_iterand_countable [Countable V] {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκ : κ ⊆ δ) (hz : (∅ : V) ∈ κ) :
    IsForcingIterand P R (rankCollapseName P R one κ δ)
      (rankOrderName P R δ (rankCollapseName P R one κ δ)) ∅ := by
  let Q : ForcingName P := ⟨rankCollapseName P R one κ δ, rankCollapseName_isName _ _ _ _ _⟩
  let S : ForcingName P := ⟨rankOrderName P R δ Q.val, rankOrderName_isName _ _ _ _⟩
  let t : ForcingName P := ⟨∅, empty_forcingName P⟩
  have hval (G : Set V) (hG : IsExternalForcingGeneric P R G) :
      let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
      A.ofName Q = woodinCollapse (A.check κ) (A.check δ) ∧
        A.ofName S = reverseInclusionOrder (woodinCollapse (A.check κ) (A.check δ)) ∧
        A.ofName t = ∅ := by
    dsimp only
    let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
    refine ⟨A.rankCollapse_value hδ hP hκ, A.rankCollapseOrder_value hδ hP hκ, ?_⟩
    apply mem_ext
    intro x
    rw [A.mem_ofName_iff]
    simp [t]
  refine ⟨Q.property, S.property, t.property, ?_, ?_⟩
  · intro p hp
    have hh := forcingFormula_of_all_generics hR htop hp forcingPreorderFormula ![Q, S] (by
      intro G hG _
      let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
      have hv : (fun i ↦ A.ofName ((![Q, S] : Fin 2 → ForcingName P) i)) = ![A.ofName Q, A.ofName S] := by
        funext i
        exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
      rw [hv]
      apply (Defined.eval_iff _).mpr
      rw [(hval G hG).1, (hval G hG).2.1]
      exact (reverseInclusionOrder_poset _).1)
    exact hh
  · intro p hp
    have hh := forcingFormula_of_all_generics hR htop hp forcingTopFormula ![Q, S, t] (by
      intro G hG _
      let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
      have hv : (fun i ↦ A.ofName ((![Q, S, t] : Fin 3 → ForcingName P) i)) =
          ![A.ofName Q, A.ofName S, A.ofName t] := by
        funext i
        exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
      rw [hv]
      apply (Defined.eval_iff _).mpr
      rw [(hval G hG).1, (hval G hG).2.1, (hval G hG).2.2]
      apply woodinCollapse_top
      have h := (A.check_mem_iff _ _).mpr hz
      rwa [show A.check ∅ = ∅ from A.checkEmbedding.map_empty] at h)
    exact hh

theorem rankCollapseName_mono_countable [Countable V] {P R one κ c δ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hc : IsChoicelessInaccessible c) (hδ : IsChoicelessInaccessible δ)
    (hP : P ∈ hierarchy c) (hκ : κ ⊆ c) (hcδ : c ⊆ δ) :
    rankCollapseName P R one κ c ⊆ rankCollapseName P R one κ δ := by
  let := hc.1
  let := hδ.1
  have hPδ := hierarchy_mono hcδ P hP
  have hB : rankCollapseName P R one κ c ⊆ lowRankNameSet P c ×ˢ P := by
    unfold rankCollapseName rankFormulaName
    exact sep_subset
  intro z hz
  obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp (hB z hz)
  have hn := ((mem_lowRankNameSet _ _ _).mp hσ).2
  have hσδ := hierarchy_mono hcδ σ ((mem_lowRankNameSet _ _ _).mp hσ).1
  let u : ForcingName P := ⟨σ, hn⟩
  let v : Fin 4 → ForcingName P := ![u,
    ⟨checkName one κ, checkName_isName htop.1 κ⟩,
    ⟨checkName one δ, checkName_isName htop.1 δ⟩,
    ⟨rankUniverseName P δ, rankUniverseName_isName _ _⟩]
  have hf := forcingFormula_of_all_generics hR htop hp sigmaOneWoodinConditionFormula v (by
    intro G hG hpG
    let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
    have hu : A.ofName u ∈ A.ofName (A.rankCollapse κ c) :=
      (A.mem_ofName_iff _ _).mpr ⟨u, p, hpG, hz, rfl⟩
    rw [A.rankCollapse_value hc hP hκ] at hu
    have hsub : A.check c ⊆ A.check δ := (A.checkEmbedding.subset_iff _ _).mpr hcδ
    have huδ := woodinCollapse_mono hsub _ hu
    have hv : (fun i ↦ A.ofName (v i)) = ![A.ofName u, A.check κ, A.check δ, hierarchy (A.check δ)] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
        (fun l ↦ Fin.cases (A.rankUniverse_value hδ hPδ) (fun m ↦ Fin.elim0 m) l) k) j) i
    rw [hv, eval_sigmaOneWoodinConditionFormula]
    exact huδ)
  apply (pair_mem_rankFormulaName _ _ _ _ _ _ _).mpr
  refine ⟨(mem_lowRankNameSet _ _ _).mpr ⟨hσδ, hn⟩, hp, ?_⟩
  have hv : (fun i ↦ (v i).val) =
      σ :> ![checkName one κ, checkName one δ, rankUniverseName P δ] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.elim0 m) l) k) j) i
  rwa [hv] at hf

theorem atomicMembership_right_mono {P R σ Q Q' : V} (hQ : Q ⊆ Q') :
    atomicMembership P R σ Q ⊆ atomicMembership P R σ Q' := by
  intro p hp
  obtain ⟨hp, hh⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hp
  apply (mem_atomicMembership_iff _ _ _ _ _).mpr
  refine ⟨hp, fun q hq hqp ↦ ?_⟩
  obtain ⟨r, hr, hrq, ν, s, hνs, hrs, he⟩ := hh q hq hqp
  exact ⟨r, hr, hrq, ν, s, hQ _ hνs, hrs, he⟩

theorem twoStepConditions_posetName_mono {P R Q Q' t : V} (hQ : Q ⊆ Q') :
    twoStepConditions P R Q t ⊆ twoStepConditions P R Q' t := by
  intro z hz
  obtain ⟨p, hp, σ, hσ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp hz
  have hN : σ ∈ twoStepNames Q' t := by
    rcases mem_union_iff.mp hσ with hd | ht
    · obtain ⟨q, hq⟩ := mem_domain_iff.mp hd
      exact mem_union_iff.mpr (Or.inl (mem_domain_of_kpair_mem (hQ _ hq)))
    · exact mem_union_iff.mpr (Or.inr ht)
  exact (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hp, hN, atomicMembership_right_mono hQ p hm⟩

theorem twoStepCombinedFilter_restrict (A : ForcingContext V) {Q Q' t : V}
    (hn : IsForcingName A.P Q) (hQ : Q ⊆ Q') {H H' : Set A.Model}
    (hH : ∀ x, x ∈ H ↔ x ∈ H' ∧ x ∈ A.ofName ⟨Q, hn⟩) (z : V) :
    z ∈ twoStepCombinedFilter A Q t H ↔
      z ∈ twoStepCombinedFilter A Q' t H' ∧ z ∈ twoStepConditions A.P A.R Q t := by
  constructor
  · rintro ⟨p, σ, rfl, hc, hpG, hσH⟩
    exact ⟨⟨p, σ, rfl, twoStepConditions_posetName_mono hQ _ hc, hpG, (hH _).mp hσH |>.1⟩, hc⟩
  · rintro ⟨⟨p, σ, rfl, _, hpG, hσH⟩, hc⟩
    have hm := ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp hc).2.2
    have hσQ : A.ofName σ ∈ A.ofName ⟨Q, hn⟩ :=
      (forcingQuotientMk_mem_iff A.P A.R A.G A.order A.generic.1 σ ⟨Q, hn⟩).mpr ⟨p, hpG, hm⟩
    exact ⟨p, σ, rfl, hc, hpG, (hH _).mpr ⟨hσH, hσQ⟩⟩

end ZFVP
