import ZFVP.ModelTheory.WoodinCollapseRankWitnessForcing
import ZFVP.ModelTheory.ForcingAtomicSemanticConsequence
import ZFVP.ModelTheory.SaturatedHartogsSpecification

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

private def collapseRankWitnessFormula : SetTheorySemisentence 2 :=
  f“q b. ∀ z, z ∈ q ↔ z = !kpair.dfn
    (!kpair.dfn (!isEmpty) (!succ.dfn (!succ.dfn b))) b”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private instance collapseRankWitnessFormula_defined :
    ℒₛₑₜ-function₁[V] woodinCollapseRankWitness via collapseRankWitnessFormula := by
  refine ⟨fun v ↦ ?_⟩
  change collapseRankWitnessFormula.Evalb v ↔ v 0 = woodinCollapseRankWitness (v 1)
  rw [mem_ext_iff]
  simp [collapseRankWitnessFormula, woodinCollapseRankWitness]

private def saturatedPrefixRankWitnessFormula : SetTheorySemisentence 6 :=
  f“P R o κ δ b. !forcingPreorderFormula P R → !forcingTopFormula P R o →
    !choicelessInaccessibleFormula δ → P ∈ !hierarchyFormula δ →
    !IsOrdinal.dfn κ → (!(numeralFormula 1)) ∈ κ → κ ⊆ δ → b ∈ δ →
    o ∈ !atomicMembershipFormula P R (!checkNameFormula o (!collapseRankWitnessFormula b))
      (!saturatedWoodinPrefixPosetNameFormula P R o κ δ)”

private def saturatedHartogsRankWitnessFormula : SetTheorySemisentence 6 :=
  f“P R o γ δ b. !forcingPreorderFormula P R → !forcingTopFormula P R o →
    !choicelessInaccessibleFormula δ → P ∈ !hierarchyFormula δ →
    γ ∈ δ → (!(numeralFormula 1)) ⊆ γ → b ∈ δ →
    o ∈ !atomicMembershipFormula P R (!checkNameFormula o (!collapseRankWitnessFormula b))
      (!saturatedHartogsPosetNameFormula P R o γ δ)”

private theorem prefix_countable [Countable V] {P R one κ δ β : V} [IsOrdinal κ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (h1 : (1 : V) ∈ κ) (hκ : κ ⊆ δ) (hβ : β ∈ δ) :
    one ∈ atomicMembership P R (checkName one (woodinCollapseRankWitness β))
      (saturatedWoodinPrefixPosetName P R one κ δ) := by
  apply atomicMembership_of_all_generics hR ht ht.1
    ⟨checkName one (woodinCollapseRankWitness β), checkName_isName ht.1 _⟩
    ⟨saturatedWoodinPrefixPosetName P R one κ δ, saturatedWoodinPrefixPosetName_isName _ _ _ _ _⟩
  intro G hG _
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  change A.check (woodinCollapseRankWitness β) ∈ A.ofName (A.saturatedWoodinPosetName κ δ)
  rw [A.saturatedWoodinPosetName_value hδ hP hκ]
  let := hδ.1
  apply A.check_woodinCollapseRankWitness_mem _ hδ.rankCriterion.2.2.1 hβ
  have hh := (A.check_mem_iff (1 : V) κ).mpr h1
  rwa [show A.check (1 : V) = (1 : A.Model) from A.checkEmbedding.map_numeral 1] at hh

private theorem hartogs_countable [Countable V] {P R one γ δ β : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hγ : γ ∈ δ) (h1 : (1 : V) ⊆ γ) (hβ : β ∈ δ) :
    one ∈ atomicMembership P R (checkName one (woodinCollapseRankWitness β))
      (saturatedHartogsPosetName P R one γ δ) := by
  apply atomicMembership_of_all_generics hR ht ht.1
    ⟨checkName one (woodinCollapseRankWitness β), checkName_isName ht.1 _⟩
    ⟨saturatedHartogsPosetName P R one γ δ, saturatedHartogsPosetName_isName _ _ _ _ _⟩
  intro G hG _
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  change A.check (woodinCollapseRankWitness β) ∈ A.ofName (A.saturatedHartogsCollapseName γ δ)
  rw [A.saturatedHartogsCollapseName_value hδ hP hγ]
  let := hδ.1
  apply A.check_woodinCollapseRankWitness_mem _ hδ.rankCriterion.2.2.1 hβ
  have hh := (A.checkEmbedding.subset_iff (1 : V) γ).mpr h1
  change A.check (1 : V) ⊆ A.check γ at hh
  rw [show A.check (1 : V) = (1 : A.Model) from A.checkEmbedding.map_numeral 1] at hh
  have : IsOrdinal (1 : A.Model) := by change IsOrdinal (succ (∅ : A.Model)); infer_instance
  exact ordinal_cardLE_iff_mem_hartogsNumber.mp (cardLE_of_subset hh)

private theorem eval_prefix (v : Fin 6 → V) :
    saturatedPrefixRankWitnessFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsChoicelessInaccessible (v 4) → v 0 ∈ hierarchy (v 4) →
        IsOrdinal (v 3) → (1 : V) ∈ v 3 → v 3 ⊆ v 4 → v 5 ∈ v 4 →
        v 2 ∈ atomicMembership (v 0) (v 1) (checkName (v 2) (woodinCollapseRankWitness (v 5)))
          (saturatedWoodinPrefixPosetName (v 0) (v 1) (v 2) (v 3) (v 4))) := by
  simp [saturatedPrefixRankWitnessFormula]

private theorem eval_hartogs (v : Fin 6 → V) :
    saturatedHartogsRankWitnessFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsChoicelessInaccessible (v 4) → v 0 ∈ hierarchy (v 4) →
        v 3 ∈ v 4 → (1 : V) ⊆ v 3 → v 5 ∈ v 4 →
        v 2 ∈ atomicMembership (v 0) (v 1) (checkName (v 2) (woodinCollapseRankWitness (v 5)))
          (saturatedHartogsPosetName (v 0) (v 1) (v 2) (v 3) (v 4))) := by
  simp [saturatedHartogsRankWitnessFormula]

theorem saturatedWoodinPrefixPosetName_rankWitness {P R one κ δ β : V} [IsOrdinal κ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (h1 : (1 : V) ∈ κ) (hκ : κ ⊆ δ) (hβ : β ∈ δ) :
    one ∈ atomicMembership P R (checkName one (woodinCollapseRankWitness β))
      (saturatedWoodinPrefixPosetName P R one κ δ) := by
  have hh := eval_of_countable_zf saturatedPrefixRankWitnessFormula (by
    intro W _ _ _ _ v
    apply (eval_prefix v).mpr
    intro hR ht hδ hP hκord h1 hκ hβ
    let := hκord
    exact prefix_countable hR ht hδ hP h1 hκ hβ) ![P, R, one, κ, δ, β]
  exact (eval_prefix _).mp hh hR ht hδ hP (show IsOrdinal κ from inferInstance) h1 hκ hβ

theorem saturatedHartogsPosetName_rankWitness {P R one γ δ β : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hγ : γ ∈ δ) (h1 : (1 : V) ⊆ γ) (hβ : β ∈ δ) :
    one ∈ atomicMembership P R (checkName one (woodinCollapseRankWitness β))
      (saturatedHartogsPosetName P R one γ δ) := by
  have hh := eval_of_countable_zf saturatedHartogsRankWitnessFormula (by
    intro W _ _ _ _ v
    exact (eval_hartogs v).mpr (fun hR ht hδ hP hγ h1 hβ ↦
      hartogs_countable hR ht hδ hP hγ h1 hβ)) ![P, R, one, γ, δ, β]
  exact (eval_hartogs _).mp hh hR ht hδ hP hγ h1 hβ

end ZFVP
