import ZFVP.ModelTheory.ForcingGuardedNormalization
import ZFVP.SetTheory.ClassForcingCongruence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def boundedNameTwoStep (P R δ Q : V) : V :=
  {z ∈ P ×ˢ hierarchy δ ; IsForcingName P (kpair.π₂ z) ∧
    kpair.π₁ z ∈ atomicMembership P R (kpair.π₂ z) Q}

noncomputable def normalizedNamePool (P R one δ Q : V) : V :=
  {τ ∈ hierarchy δ ; IsForcingName P τ ∧ forcingLeastRankName P R one τ = τ ∧
    one ∈ atomicMembership P R τ Q}

noncomputable def normalizedNameTwoStep (P R one δ Q : V) : V :=
  P ×ˢ normalizedNamePool P R one δ Q

/-- The ordinary two-step order restricted to a supplied carrier. -/
noncomputable def nameTwoStepOrderOn (P R S C : V) : V :=
  {z ∈ C ×ˢ C ; ⟨kpair.π₁ (kpair.π₁ z), kpair.π₁ (kpair.π₂ z)⟩ₖ ∈ R ∧
    kpair.π₁ (kpair.π₁ z) ∈ forcingFormula P R boundedPairMemberFormula
      (standardTuple ![S, kpair.π₂ (kpair.π₁ z), kpair.π₂ (kpair.π₂ z)])}

noncomputable def guardedTwoStepCode (P R one z : V) : V :=
  ⟨kpair.π₁ z, forcingGuardedNormalization P R one (kpair.π₁ z) (kpair.π₂ z)⟩ₖ

instance guardedTwoStepCode_definable (P R one : V) :
    ℒₛₑₜ-function₁[V] (guardedTwoStepCode P R one) := by
  unfold guardedTwoStepCode forcingGuardedNormalization
  apply Language.DefinableFunction₂.comp (F := kpair)
  · definability
  · apply Language.DefinableFunction₁.comp (F := forcingLeastRankName P R one)
    exact Language.DefinableFunction₄.comp (F := forcingRestrictedName)
      (by definability) (by definability) (by definability) (by definability)

theorem pair_mem_boundedNameTwoStep (P R δ Q p τ : V) :
    ⟨p, τ⟩ₖ ∈ boundedNameTwoStep P R δ Q ↔ p ∈ P ∧ τ ∈ hierarchy δ ∧
      IsForcingName P τ ∧ p ∈ atomicMembership P R τ Q := by
  simp [boundedNameTwoStep, and_assoc]

theorem pair_mem_normalizedNameTwoStep (P R one δ Q p τ : V) :
    ⟨p, τ⟩ₖ ∈ normalizedNameTwoStep P R one δ Q ↔ p ∈ P ∧ τ ∈ hierarchy δ ∧
      IsForcingName P τ ∧ forcingLeastRankName P R one τ = τ ∧
      one ∈ atomicMembership P R τ Q := by
  simp [normalizedNameTwoStep, normalizedNamePool]

theorem pair_mem_nameTwoStepOrderOn (P R S C p τ q σ : V) :
    ⟨⟨p, τ⟩ₖ, ⟨q, σ⟩ₖ⟩ₖ ∈ nameTwoStepOrderOn P R S C ↔
      ⟨p, τ⟩ₖ ∈ C ∧ ⟨q, σ⟩ₖ ∈ C ∧ ⟨p, q⟩ₖ ∈ R ∧
      p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S, τ, σ]) := by
  simp [nameTwoStepOrderOn, and_assoc]

@[simp] theorem guardedTwoStepCode_pair (P R one p τ : V) :
    guardedTwoStepCode P R one ⟨p, τ⟩ₖ = ⟨p, forcingGuardedNormalization P R one p τ⟩ₖ := by
  simp [guardedTwoStepCode]

theorem normalizedNameTwoStep_subset {P R one δ Q : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) :
    normalizedNameTwoStep P R one δ Q ⊆ boundedNameTwoStep P R δ Q := by
  intro z hz
  obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp hz
  obtain ⟨hp, hτδ, hτ, _, hm⟩ := (pair_mem_normalizedNameTwoStep _ _ _ _ _ _ _).mp hz
  exact (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mpr
    ⟨hp, hτδ, hτ, atomicMembership_mono hR hm hp (ht.2 p hp)⟩

theorem guardedTwoStepCode_mem {P R one δ Q z : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ)
    (h0 : one ∈ atomicMembership P R ∅ Q) (hz : z ∈ boundedNameTwoStep P R δ Q) :
    guardedTwoStepCode P R one z ∈ normalizedNameTwoStep P R one δ Q := by
  obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨hp, hτδ, hτ, hm⟩ := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hz
  rw [guardedTwoStepCode_pair, pair_mem_normalizedNameTwoStep]
  exact ⟨hp, forcingGuardedNormalization_mem_hierarchy hR ht hδ hP hτ hτδ,
    forcingGuardedNormalization_isName hR ht hτ,
    forcingGuardedNormalization_normalized hR ht hτ,
    forcingGuardedNormalization_forces_member hR ht hp hτ hm h0⟩

theorem forcingGuardedNormalization_order_iff {P R one p q τ σ S : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hp : p ∈ P) (hq : q ∈ P) (hpq : ⟨p, q⟩ₖ ∈ R)
    (hτ : IsForcingName P τ) (hσ : IsForcingName P σ) :
    p ∈ forcingFormula P R boundedPairMemberFormula
      (standardTuple ![S, forcingGuardedNormalization P R one p τ,
        forcingGuardedNormalization P R one q σ]) ↔
    p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S, τ, σ]) := by
  apply classForcingFormula_congr hR (IsForcingName P) (by definability)
    boundedPairMemberFormula _ _ hp
  intro i
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ Fin.elim0 l) k) j) i
  · exact (atomicEquality_refl hR S).symm ▸ hp
  · exact forcingGuardedNormalization_forces_equal hR ht hp hτ
  · exact atomicEquality_mono hR (forcingGuardedNormalization_forces_equal hR ht hq hσ) hp hpq

theorem guardedTwoStepCode_order_iff {P R one δ Q S z w : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ)
    (h0 : one ∈ atomicMembership P R ∅ Q)
    (hz : z ∈ boundedNameTwoStep P R δ Q) (hw : w ∈ boundedNameTwoStep P R δ Q) :
    ⟨guardedTwoStepCode P R one z, guardedTwoStepCode P R one w⟩ₖ ∈
      nameTwoStepOrderOn P R S (normalizedNameTwoStep P R one δ Q) ↔
    ⟨z, w⟩ₖ ∈ nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q) := by
  have hnz := guardedTwoStepCode_mem hR ht hδ hP h0 hz
  have hnw := guardedTwoStepCode_mem hR ht hδ hP h0 hw
  obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨q, _, σ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hw).1
  have hz' := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hz
  have hw' := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hw
  simp only [guardedTwoStepCode_pair] at hnz hnw ⊢
  rw [pair_mem_nameTwoStepOrderOn, pair_mem_nameTwoStepOrderOn]
  simp only [hnz, hnw, hz, hw, true_and]
  apply and_congr_right
  intro hpq
  exact forcingGuardedNormalization_order_iff hR ht hz'.1 hw'.1 hpq hz'.2.2.1 hw'.2.2.1

theorem normalizedNameTwoStep_inclusion_order_iff {P R one δ Q S z w : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hz : z ∈ normalizedNameTwoStep P R one δ Q)
    (hw : w ∈ normalizedNameTwoStep P R one δ Q) :
    ⟨z, w⟩ₖ ∈ nameTwoStepOrderOn P R S (normalizedNameTwoStep P R one δ Q) ↔
    ⟨z, w⟩ₖ ∈ nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q) := by
  have hz' := normalizedNameTwoStep_subset hR ht z hz
  have hw' := normalizedNameTwoStep_subset hR ht w hw
  simp only [nameTwoStepOrderOn, mem_sep_iff, kpair_mem_iff, hz, hw, hz', hw', true_and]

theorem guardedTwoStepCode_prefix (P R one z : V) :
    kpair.π₁ (guardedTwoStepCode P R one z) = kpair.π₁ z := by
  simp [guardedTwoStepCode]

theorem forcingPairMember_congr_names {P R p S τ τ' σ σ' : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P)
    (hτ : p ∈ atomicEquality P R τ τ') (hσ : p ∈ atomicEquality P R σ σ') :
    p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S, τ, σ]) ↔
    p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S, τ', σ']) := by
  apply classForcingFormula_congr hR (IsForcingName P) (by definability)
    boundedPairMemberFormula _ _ hp
  intro i
  exact Fin.cases ((atomicEquality_refl hR S).symm ▸ hp)
    (fun j ↦ Fin.cases hτ (fun k ↦ Fin.cases hσ (fun l ↦ Fin.elim0 l) k) j) i

/-- The composite of inclusion with normalization is order-equivalent to the
identity; equality here is deliberately a forcing-order statement. -/
theorem guardedTwoStepCode_equivalent {P R one δ Q S z : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ)
    (hQ : IsForcingName P Q) (hS : IsForcingName P S)
    (h0 : one ∈ atomicMembership P R ∅ Q)
    (hpre : kpair.π₁ z ∈ forcingFormula P R forcingPreorderFormula (standardTuple ![Q, S]))
    (hz : z ∈ boundedNameTwoStep P R δ Q) :
    ⟨guardedTwoStepCode P R one z, z⟩ₖ ∈ nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q) ∧
    ⟨z, guardedTwoStepCode P R one z⟩ₖ ∈ nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q) := by
  have hn := normalizedNameTwoStep_subset hR ht _ (guardedTwoStepCode_mem hR ht hδ hP h0 hz)
  obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨hp, _, hτ, hm⟩ := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hz
  simp only [kpair.π₁_kpair] at hpre
  have hrefl := forcedPreorder_refl hR ht hp ⟨Q, hQ⟩ ⟨S, hS⟩ ⟨τ, hτ⟩ hpre hm
  have he := forcingGuardedNormalization_forces_equal hR ht hp hτ
  have heτ : p ∈ atomicEquality P R τ τ := (atomicEquality_refl hR τ).symm ▸ hp
  simp only [guardedTwoStepCode_pair] at hn ⊢
  rw [pair_mem_nameTwoStepOrderOn, pair_mem_nameTwoStepOrderOn]
  exact ⟨⟨hn, hz, hR.2.1 p hp, (forcingPairMember_congr_names hR hp he heτ).mpr hrefl⟩,
    ⟨hz, hn, hR.2.1 p hp, (forcingPairMember_congr_names hR hp heτ he).mpr hrefl⟩⟩

theorem guardedTwoStepCode_normalized_equivalent {P R one δ Q S z : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ)
    (hQ : IsForcingName P Q) (hS : IsForcingName P S)
    (h0 : one ∈ atomicMembership P R ∅ Q)
    (hpre : kpair.π₁ z ∈ forcingFormula P R forcingPreorderFormula (standardTuple ![Q, S]))
    (hz : z ∈ normalizedNameTwoStep P R one δ Q) :
    ⟨guardedTwoStepCode P R one z, z⟩ₖ ∈ nameTwoStepOrderOn P R S (normalizedNameTwoStep P R one δ Q) ∧
    ⟨z, guardedTwoStepCode P R one z⟩ₖ ∈ nameTwoStepOrderOn P R S (normalizedNameTwoStep P R one δ Q) := by
  have hs := normalizedNameTwoStep_subset hR ht z hz
  have hn := guardedTwoStepCode_mem hR ht hδ hP h0 hs
  have he := guardedTwoStepCode_equivalent hR ht hδ hP hQ hS h0 hpre hs
  exact ⟨(normalizedNameTwoStep_inclusion_order_iff hR ht hn hz).mpr he.1,
    (normalizedNameTwoStep_inclusion_order_iff hR ht hz hn).mpr he.2⟩

noncomputable def guardedTwoStepMap (P R one δ Q : V) : V :=
  definableGraph (boundedNameTwoStep P R δ Q) (guardedTwoStepCode P R one) (by infer_instance)

theorem guardedTwoStepMap_function {P R one δ Q : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ)
    (h0 : one ∈ atomicMembership P R ∅ Q) :
    guardedTwoStepMap P R one δ Q ∈ normalizedNameTwoStep P R one δ Q ^ boundedNameTwoStep P R δ Q :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hz ↦ guardedTwoStepCode_mem hR ht hδ hP h0 hz)

theorem guardedTwoStepMap_value {P R one δ Q z : V} (hz : z ∈ boundedNameTwoStep P R δ Q) :
    (guardedTwoStepMap P R one δ Q) ‘ z = guardedTwoStepCode P R one z :=
  value_definableGraph _ _ _ hz

end ZFVP
