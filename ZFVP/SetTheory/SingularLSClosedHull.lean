import ZFVP.SetTheory.SingularHullUnion
import ZFVP.SetTheory.SmallIndexedUnionSurjection
import ZFVP.SetTheory.RankSurjectionOperations
import ZFVP.SetTheory.WeaklyLSHullImageCover
import ZFVP.ModelTheory.ElementarySmallSubsetClosure
import ZFVP.ModelTheory.ElementaryUnionMembership

/-! The function-closure clauses of Usuba Lemma 4.3. A singular LS cardinal
supplies an elementary hull covered by Vλ and closed under lower-rank-domain
functions into a prescribed earlier rank. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def hullFunctionBound (ν α J : V) : V :=
  power ((hierarchy ν) ×ˢ ((hierarchy α) ∩ ⋃ˢ J))

instance hullFunctionBound_definable : ℒₛₑₜ-function₃[V] hullFunctionBound := by
  unfold hullFunctionBound
  definability

theorem IsLSCardinal.singular_closed_hull {lam ν α x : V}
    (hlam : IsLSCardinal lam) (hsing : internalCofinality lam ∈ lam)
    (hν : IsWeaklyLSCardinal ν) (hνcf : ν ⊆ internalCofinality lam)
    [IsOrdinal α] (hlamα : lam ∈ α) (hx : x ∈ hierarchy α) :
    ∃ τ X, IsOrdinal τ ∧ α ∈ τ ∧ IsElementaryInclusion X (hierarchy τ) ∧
      hierarchy lam ⊆ X ∧ x ∈ X ∧
      (∃ e ∈ X ^ (hierarchy lam), range e = X) ∧
      ∀ γ ∈ ν, (X ∩ hierarchy α) ^ (hierarchy γ) ⊆ X := by
  classical
  let := hlam.1.1
  let := hν.1.1
  have hlw := hlam.weaklyLSCardinal
  have hlsucc (δ : V) (hδ : δ ∈ lam) : succ δ ∈ lam :=
    initial_succ_mem hlam.1 (IsOrdinal.toIsTransitive.transitive _ hlam.2.1) hδ
  have hνsucc (δ : V) (hδ : δ ∈ ν) : succ δ ∈ ν :=
    initial_succ_mem hν.1 (IsOrdinal.toIsTransitive.transitive _ hν.2.1) hδ
  have hνlam : ν ∈ lam := ordinal_mem_of_subset_mem hνcf hsing
  let τ := ordinalAdd α (ω : V)
  have hατ : α ∈ τ := ordinalAdd_omega_gt α
  have hτsucc (δ : V) (hδ : δ ∈ τ) : succ δ ∈ τ := ordinalAdd_omega_succ_closed α hδ
  have hlamτ : lam ∈ τ := IsOrdinal.toIsTransitive.mem_trans hlamα hατ
  have hντ : ν ∈ τ := IsOrdinal.toIsTransitive.mem_trans hνlam hlamτ
  have hxτ : x ∈ hierarchy τ := mem_hierarchy_of_mem_stage hατ hx
  let F := weaklyLSHullFamily lam τ x
  obtain ⟨c, hc⟩ := cofinalMap_exists lam
  let r := definableGraph lam hierarchy (by definability)
  let O := definableGraph (power F) (hullFunctionBound ν α) (by definability)
  have hOfun := definableGraph_mem_function (power F) (hullFunctionBound ν α) (by definability)
  let := IsFunction.of_mem hOfun
  let p := ⟨⟨F, c⟩ₖ, ⟨r, O⟩ₖ⟩ₖ
  let ρ₀ := rank ({p, lam, power F, τ} : V)
  let ρ := ordinalAdd ρ₀ (ω : V)
  let := hierarchy_transitive ρ
  have hρ₀ρ : ρ₀ ∈ ρ := ordinalAdd_omega_gt ρ₀
  have hρsucc (δ : V) (hδ : δ ∈ ρ) : succ δ ∈ ρ := ordinalAdd_omega_succ_closed ρ₀ hδ
  have hpρ : p ∈ hierarchy ρ := mem_hierarchy_of_mem_stage hρ₀ρ
    ((mem_hierarchy_iff_rank_mem _ _).mpr (rank_mem (show p ∈ ({p, lam, power F, τ} : V) by simp)))
  have hpowρ : power F ∈ hierarchy ρ := mem_hierarchy_of_mem_stage hρ₀ρ
    ((mem_hierarchy_iff_rank_mem _ _).mpr (rank_mem (show power F ∈ ({p, lam, power F, τ} : V) by simp)))
  have hlamρ : lam ∈ ρ := by
    apply IsOrdinal.toIsTransitive.mem_trans (y := ρ₀) _ hρ₀ρ
    simpa only [rank_of_ordinal] using rank_mem (show lam ∈ ({p, lam, power F, τ} : V) by simp)
  have hτρ : τ ∈ ρ := by
    apply IsOrdinal.toIsTransitive.mem_trans (y := ρ₀) _ hρ₀ρ
    simpa only [rank_of_ordinal] using rank_mem (show τ ∈ ({p, lam, power F, τ} : V) by simp)
  let χ := succ (internalCofinality lam)
  have hχlam : χ ∈ lam := hlsucc _ hsing
  obtain ⟨β, Y, hβ, hρβ, hY, hχY, hpY, hsmallY, hclosedY⟩ :=
    hlam.2.2 χ hχlam ρ inferInstance (IsOrdinal.toIsTransitive.transitive _ hlamρ) p hpρ
  let := hβ
  let := hierarchy_transitive β
  have hρsub : hierarchy ρ ⊆ hierarchy β := hierarchy_mono hρβ
  obtain ⟨hFcY, hrOY⟩ := hY.kpair_components_mem hpY
  obtain ⟨hFY, hcY⟩ := hY.kpair_components_mem hFcY
  obtain ⟨hrY, hOY⟩ := hY.kpair_components_mem hrOY
  have hcfY : hierarchy (internalCofinality lam) ⊆ Y := subset_trans
    (hierarchy_mono (show internalCofinality lam ⊆ χ from fun z hz ↦ mem_succ_iff.mpr (Or.inr hz))) hχY
  let I := F ∩ Y
  let X := ⋃ˢ I
  obtain ⟨heX, hVX, hxX, eX, heXfun, hreX⟩ :=
    hlw.singular_hull_union (IsOrdinal.toIsTransitive.transitive _ hlamτ) hxτ hc hY hFY hcY hrY hcfY hsmallY
  refine ⟨τ, X, inferInstance, hατ, heX, hVX, hxX, ⟨eX, heXfun, hreX⟩, ?_⟩
  intro γ hγ f hf
  let := IsOrdinal.of_mem hγ
  let := IsFunction.of_mem hf
  have hγτ : γ ∈ τ := IsOrdinal.toIsTransitive.mem_trans hγ hντ
  have hfp : f ∈ power ((hierarchy γ) ×ˢ (hierarchy α)) := by
    apply mem_power_iff.mpr
    intro q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hf q hq)
    exact kpair_mem_iff.mpr ⟨ha, (mem_inter_iff.mp hb).2⟩
  have hfτ : f ∈ hierarchy τ := (hierarchy_transitive τ).mem_trans hfp
    (power_mem_hierarchy_limit hτsucc (prod_mem_hierarchy_limit hτsucc (hierarchy_mem hγτ) (hierarchy_mem hατ)))
  have hIρ : I ∈ hierarchy ρ := (hierarchy_transitive ρ).mem_trans
    (mem_power_iff.mpr (fun _ hz ↦ (mem_inter_iff.mp hz).1)) hpowρ
  have hpackβ : ⟨f, I⟩ₖ ∈ hierarchy β := hρsub _ (kpair_mem_hierarchy_limit hρsucc
    (mem_hierarchy_of_mem_stage hτρ hfτ) hIρ)
  have hνβ : ν ⊆ β := subset_trans (IsOrdinal.toIsTransitive.transitive _
    (IsOrdinal.toIsTransitive.mem_trans hνlam hlamρ)) hρβ
  obtain ⟨Y', hY', hγY', hpackY', hsmallY'⟩ := hν.2.2 γ hγ β inferInstance hνβ _ hpackβ
  obtain ⟨hfY', hIY'⟩ := hY'.kpair_components_mem hpackY'
  have hIne : IsNonempty I := hY.nonempty_inter_member hFY
    (hlw.hullFamily_nonempty (IsOrdinal.toIsTransitive.transitive _ hlamτ) hxτ)
  let J := I ∩ Y'
  have hJne : IsNonempty J := hY'.nonempty_inter_member hIY' hIne
  have hJF : J ⊆ F := fun z hz ↦ (mem_inter_iff.mp (mem_inter_iff.mp hz).1).1
  have hJY' : J ⊆ Y' := fun _ hz ↦ (mem_inter_iff.mp hz).2
  obtain ⟨σ, hσν, e', he', hre'⟩ := hsmallY'.rank_surjection hY'.source_nonempty hνsucc
  let := IsOrdinal.of_mem hσν
  have hidJ : range (identity J) = J := by
    apply mem_ext
    intro z
    simp [mem_range_iff]
  obtain ⟨q, hq, hrq⟩ := surjection_extension hJY' (identity_mem_function J) hidJ hJne
  let eJ := compose e' q
  have heJ : eJ ∈ J ^ (hierarchy σ) := compose_function he' hq
  have hreJ : range eJ = J := range_compose_surjective he' hq hre' hrq
  have hFρ : F ∈ hierarchy ρ := (kpair_components_mem_transitive
    (kpair_components_mem_transitive hpρ).1).1
  have hJsub : J ⊆ Y ∩ hierarchy ρ := by
    intro Z hZ
    exact mem_inter_iff.mpr ⟨(mem_inter_iff.mp (mem_inter_iff.mp hZ).1).2,
      (hierarchy_transitive ρ).mem_trans (hJF Z hZ) hFρ⟩
  have hJβ : J ∈ hierarchy β := hρsub _ ((hierarchy_transitive ρ).mem_trans (mem_power_iff.mpr hJF) hpowρ)
  have hσχ : σ ∈ χ := mem_succ_iff.mpr (Or.inr (hνcf σ hσν))
  have hJY : J ∈ Y := hY.rank_surjective_subset_mem hclosedY hJsub hJβ heJ hreJ hσχ hJne
  have hDJY : hullFunctionBound ν α J ∈ Y := by
    have hJdom : J ∈ domain O := (domain_eq_of_mem_function hOfun).symm ▸ mem_power_iff.mpr hJF
    have hh := hY.function_value_mem hOY hJY hJdom
    rwa [value_definableGraph _ _ _ (mem_power_iff.mpr hJF)] at hh
  have hsmallJ : ∀ Z ∈ J, HasSmallTransitiveCollapse lam Z :=
    fun Z hZ ↦ ((mem_weaklyLSHullFamily _ _ _ _).mp (hJF Z hZ)).2.2
  have hxJ : ∀ Z ∈ J, x ∈ Z :=
    fun Z hZ ↦ ((mem_weaklyLSHullFamily _ _ _ _).mp (hJF Z hZ)).2.1
  obtain ⟨δ, hδlam, eu, heu, hreu⟩ :=
    smallIndexedUnion_rank_surjection hlsucc hν hνcf hσν heJ hreJ hJne hsmallJ hxJ
  let A := (hierarchy α) ∩ ⋃ˢ J
  have hrange : range f ⊆ A := by
    intro z hz
    obtain ⟨a, haz⟩ := mem_range_iff.mp hz
    have ha : a ∈ hierarchy γ := domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem haz
    have hzX := function_value_mem hf ha
    have hzY' := hY'.function_value_mem hfY' (hγY' a ha) (mem_domain_of_kpair_mem haz)
    obtain ⟨Z, hZ, hzZ⟩ := hY'.union_member_witness hIY'
      (value_eq_of_kpair_mem haz ▸ hzY') ((mem_inter_iff.mp (value_eq_of_kpair_mem haz ▸ hzX)).1)
    exact mem_inter_iff.mpr ⟨(mem_inter_iff.mp (value_eq_of_kpair_mem haz ▸ hzX)).2,
      mem_sUnion_iff.mpr ⟨Z, hZ, hzZ⟩⟩
  by_cases hAne : IsNonempty A
  · have hAunion : A ⊆ ⋃ˢ J := fun _ hz ↦ (mem_inter_iff.mp hz).2
    have hidA : range (identity A) = A := by
      apply mem_ext
      intro z
      simp [mem_range_iff]
    obtain ⟨a, ha, hra⟩ := surjection_extension hAunion (identity_mem_function A) hidA hAne
    have heA := compose_function heu ha
    have hreA := range_compose_surjective heu ha hreu hra
    obtain ⟨ε, hεlam, ep, hep, hrep⟩ := rank_product_power_surjection hlsucc hνlam hδlam heA hreA
    have hAτ : A ∈ hierarchy τ := mem_hierarchy_of_mem_stage (hτsucc α hατ) (by
      rw [hierarchy_succ, mem_power_iff]
      exact fun _ hz ↦ (mem_inter_iff.mp hz).1)
    have hDbτ : hullFunctionBound ν α J ∈ hierarchy τ := power_mem_hierarchy_limit hτsucc
      (prod_mem_hierarchy_limit hτsucc (hierarchy_mem hντ) hAτ)
    have hDsub : hullFunctionBound ν α J ⊆ hierarchy τ :=
      (hierarchy_transitive τ).transitive _ hDbτ
    obtain ⟨Z, hZ, hDZ⟩ := hY.containing_member hFY hDJY
      (hlw.hullFamily_cover_surjection (IsOrdinal.toIsTransitive.transitive _ hlamτ) hxτ hεlam hep hrep hDsub)
    have hfD : f ∈ hullFunctionBound ν α J := by
      apply mem_power_iff.mpr
      intro t ht
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hf t ht)
      exact kpair_mem_iff.mpr ⟨hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hγ) a ha,
        hrange b (mem_range_of_kpair_mem ht)⟩
    exact mem_sUnion_iff.mpr ⟨Z, hZ, hDZ f hfD⟩
  · have hfempty : f = ∅ := by
      apply mem_ext
      intro t
      simp only [not_mem_empty, iff_false]
      intro ht
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hf t ht)
      exact hAne ⟨b, hrange b (mem_range_of_kpair_mem ht)⟩
    rw [hfempty]
    exact hVX _ (ordinal_subset_hierarchy lam ∅ (IsOrdinal.toIsTransitive.mem_trans empty_mem_ω hlam.2.1))

end ZFVP


