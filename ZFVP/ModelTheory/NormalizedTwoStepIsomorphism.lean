import ZFVP.ModelTheory.NormalizedIsomorphismPools

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def normalizedTwoStepIsoValue (A B top f z : V) : V :=
  ⟨f ‘ (kpair.π₁ z), normalizedIsomorphismName A B top f (kpair.π₂ z)⟩ₖ

instance normalizedTwoStepIsoValue_definable (A B top f : V) :
    ℒₛₑₜ-function₁[V] (normalizedTwoStepIsoValue A B top f) := by
  unfold normalizedTwoStepIsoValue
  apply Language.DefinableFunction₂.comp
  · definability
  · apply Language.DefinableFunction₅.comp <;> definability

noncomputable def normalizedTwoStepIsoMap (P R one δ U A B top f : V) : V :=
  definableGraph (normalizedNameTwoStep P R one δ U) (normalizedTwoStepIsoValue A B top f) (by infer_instance)

theorem normalizedTwoStepIsoMap_value {P R one δ U A B top f z : V}
    (hz : z ∈ normalizedNameTwoStep P R one δ U) :
    (normalizedTwoStepIsoMap P R one δ U A B top f) ‘ z = normalizedTwoStepIsoValue A B top f z :=
  value_definableGraph _ _ _ hz

theorem normalizedTwoStepIsoValue_mem {P R A B one top δ U f z : V}
    (hf : IsForcingIsomorphism P R A B f) (hB : IsForcingPreorder A B)
    (ht : top ∈ A) (hft : f ‘ one = top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hA : A ∈ hierarchy δ)
    (hU : IsForcingName P U) (hz : z ∈ normalizedNameTwoStep P R one δ U) :
    normalizedTwoStepIsoValue A B top f z ∈ normalizedNameTwoStep A B top δ (nameAction f U) := by
  obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp hz
  simp only [normalizedTwoStepIsoValue, kpair.π₁_kpair, kpair.π₂_kpair, normalizedNameTwoStep, kpair_mem_iff]
  exact ⟨function_value_mem hf.1 hp, normalizedIsomorphismName_mem_pool hf hB ht hft hδ hP hA hU hτ⟩

theorem normalizedTwoStepIsoValue_inverse {P R A B one top δ U f z : V}
    (hf : IsForcingIsomorphism P R A B f) (hR : IsForcingPreorder P R) (hB : IsForcingPreorder A B)
    (ho : one ∈ P) (ht : top ∈ A) (hft : f ‘ one = top)
    (hz : z ∈ normalizedNameTwoStep P R one δ U) :
    normalizedTwoStepIsoValue P R one (converseGraph f) (normalizedTwoStepIsoValue A B top f z) = z := by
  obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp hz
  have hτ' := mem_sep_iff.mp hτ
  simp only [normalizedTwoStepIsoValue, kpair.π₁_kpair, kpair.π₂_kpair, hf.inverse_value hp,
    normalizedIsomorphismName_inverse hf hR hB ho ht hft hτ'.2.1 hτ'.2.2.1]

theorem normalizedTwoStepIsoMap_isomorphism {P R A B one top δ U S f : V}
    (hf : IsForcingIsomorphism P R A B f) (hR : IsForcingPreorder P R) (hB : IsForcingPreorder A B)
    (ho : one ∈ P) (ht : IsForcingTop A B top) (hft : f ‘ one = top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hA : A ∈ hierarchy δ)
    (hU : IsForcingName P U) (hS : IsForcingName P S) :
    IsForcingIsomorphism (normalizedNameTwoStep P R one δ U)
      (nameTwoStepOrderOn P R S (normalizedNameTwoStep P R one δ U))
      (normalizedNameTwoStep A B top δ (nameAction f U))
      (nameTwoStepOrderOn A B (nameAction f S) (normalizedNameTwoStep A B top δ (nameAction f U)))
      (normalizedTwoStepIsoMap P R one δ U A B top f) := by
  have hmem {z : V} (hz : z ∈ normalizedNameTwoStep P R one δ U) :=
    normalizedTwoStepIsoValue_mem hf hB ht.1 hft hδ hP hA hU hz
  have hm : normalizedTwoStepIsoMap P R one δ U A B top f ∈
      (normalizedNameTwoStep A B top δ (nameAction f U)) ^ (normalizedNameTwoStep P R one δ U) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hz ↦ hmem hz)
  refine ⟨hm, ?_, ?_, ?_⟩
  · intro a b z ha hb
    obtain ⟨ha', hza⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp ha
    obtain ⟨hb', hzb⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hb
    have he := congrArg (normalizedTwoStepIsoValue P R one (converseGraph f)) (hza.symm.trans hzb)
    simpa only [normalizedTwoStepIsoValue_inverse hf hR hB ho ht.1 hft ha',
      normalizedTwoStepIsoValue_inverse hf hR hB ho ht.1 hft hb'] using he
  · apply subset_antisymm (range_subset_of_mem_function hm)
    intro z hz
    have hback : (converseGraph f) ‘ top = one := by rw [← hft, hf.inverse_value ho]
    let a := normalizedTwoStepIsoValue P R one (converseGraph f) z
    have ha : a ∈ normalizedNameTwoStep P R one δ U := by
      simpa only [hf.name_inverse_cancel hU] using
        normalizedTwoStepIsoValue_mem hf.inverse hR ho hback hδ hA hP (nameAction_isName hf.1 hU) hz
    have he : normalizedTwoStepIsoValue A B top f a = z := by
      obtain ⟨q, hq, σ, hσ, rfl⟩ := mem_prod_iff.mp hz
      have hσ' := mem_sep_iff.mp hσ
      dsimp only [a]
      simp only [normalizedTwoStepIsoValue, kpair.π₁_kpair, kpair.π₂_kpair, hf.value_inverse hq]
      rw [normalizedIsomorphismName_comp hf.inverse hf hR hB ho ht.1 hft hσ'.2.1, hf.inverse_compose]
      unfold normalizedIsomorphismName
      rw [nameAction_identity hσ'.2.1, hσ'.2.2.1]
    have hv := value_mem_range hm ha
    rwa [normalizedTwoStepIsoMap_value ha, he] at hv
  · intro a ha b hb
    have ha' := hmem ha
    have hb' := hmem hb
    rw [normalizedTwoStepIsoMap_value ha, normalizedTwoStepIsoMap_value hb]
    obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp ha
    obtain ⟨q, hq, σ, hσ, rfl⟩ := mem_prod_iff.mp hb
    have hτ' := mem_sep_iff.mp hτ
    have hσ' := mem_sep_iff.mp hσ
    have hp' := function_value_mem hf.1 hp
    have heτ := atomicEquality_mono hB (normalizedIsomorphismName_equal hf hB ht.1 hτ'.2.1) hp' (ht.2 _ hp')
    have heσ := atomicEquality_mono hB (normalizedIsomorphismName_equal hf hB ht.1 hσ'.2.1) hp' (ht.2 _ hp')
    have he := forcingPairMember_congr_names (S := nameAction f S) hB hp' heτ heσ
    have hform := forcingFormula_isomorphism_iff hR hB hf boundedPairMemberFormula ![S, τ, σ]
      (by simp [Fin.forall_fin_succ, hS, hτ'.2.1, hσ'.2.1]) hp
    have hform' : p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S, τ, σ]) ↔
        f ‘ p ∈ forcingFormula A B boundedPairMemberFormula
          (standardTuple ![nameAction f S, nameAction f τ, nameAction f σ]) := by
      have hv : (fun i : Fin 3 ↦ nameAction f (![S, τ, σ] i)) =
          ![nameAction f S, nameAction f τ, nameAction f σ] := by
        funext i
        exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
      rw [hv] at hform
      exact hform.symm
    simp only [normalizedTwoStepIsoValue, kpair.π₁_kpair, kpair.π₂_kpair] at ha' hb' ⊢
    rw [pair_mem_nameTwoStepOrderOn, pair_mem_nameTwoStepOrderOn]
    simp only [normalizedNameTwoStep, kpair_mem_iff] at ha' hb'
    simp only [show ⟨p, τ⟩ₖ ∈ normalizedNameTwoStep P R one δ U from kpair_mem_iff.mpr ⟨hp, hτ⟩,
      show ⟨q, σ⟩ₖ ∈ normalizedNameTwoStep P R one δ U from kpair_mem_iff.mpr ⟨hq, hσ⟩,
      show ⟨f ‘ p, normalizedIsomorphismName A B top f τ⟩ₖ ∈ normalizedNameTwoStep A B top δ (nameAction f U)
        from kpair_mem_iff.mpr ha',
      show ⟨f ‘ q, normalizedIsomorphismName A B top f σ⟩ₖ ∈ normalizedNameTwoStep A B top δ (nameAction f U)
        from kpair_mem_iff.mpr hb', true_and]
    apply and_congr (hf.2.2.2 p hp q hq)
    exact hform'.trans he

theorem normalizedTwoStepIsoValue_prefix (A B top f z : V) :
    kpair.π₁ (normalizedTwoStepIsoValue A B top f z) = f ‘ (kpair.π₁ z) := by
  simp only [normalizedTwoStepIsoValue, kpair.π₁_kpair]

theorem normalizedTwoStepIsoValue_empty_tail {A B top f p : V}
    (hB : IsForcingPreorder A B) (ht : top ∈ A) :
    normalizedTwoStepIsoValue A B top f ⟨p, ∅⟩ₖ = ⟨f ‘ p, ∅⟩ₖ := by
  simp only [normalizedTwoStepIsoValue, kpair.π₁_kpair, kpair.π₂_kpair,
    normalizedIsomorphismName_empty hB ht]

theorem normalizedTwoStepIsoValue_comp {P R A B C D one top u δ U f g z : V}
    (hf : IsForcingIsomorphism P R A B f) (hg : IsForcingIsomorphism A B C D g)
    (hB : IsForcingPreorder A B) (hD : IsForcingPreorder C D)
    (ht : top ∈ A) (hu : u ∈ C) (hgu : g ‘ top = u)
    (hz : z ∈ normalizedNameTwoStep P R one δ U) :
    normalizedTwoStepIsoValue C D u g (normalizedTwoStepIsoValue A B top f z) =
      normalizedTwoStepIsoValue C D u (compose f g) z := by
  obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp hz
  have hτ' := mem_sep_iff.mp hτ
  simp only [normalizedTwoStepIsoValue, kpair.π₁_kpair, kpair.π₂_kpair,
    value_compose_of_mem_function hf.1 hg.1 hp,
    normalizedIsomorphismName_comp hf hg hB hD ht hu hgu hτ'.2.1]

end ZFVP
