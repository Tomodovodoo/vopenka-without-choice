import ZFVP.ModelTheory.NormalizedTwoStepForcing
import ZFVP.ModelTheory.EquivalentSuborderRetraction
import ZFVP.ModelTheory.EquivalentRetractionModel

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R one δ Q S : V}

local notation "Cₛ" => boundedNameTwoStep P R δ Q
local notation "Cₙ" => normalizedNameTwoStep P R one δ Q
local notation "Rₛ" => nameTwoStepOrderOn P R S Cₛ
local notation "Rₙ" => nameTwoStepOrderOn P R S Cₙ

noncomputable def normalizedTwoStepRetraction (P R one δ Q : V) : V :=
  equivalentSuborderRetraction (boundedNameTwoStep P R δ Q) (normalizedNameTwoStep P R one δ Q)
    (guardedTwoStepMap P R one δ Q)

theorem normalizedTwoStepRetraction_spec [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅) :
    IsForcingRetraction Cₙ Rₙ Cₛ Rₛ (normalizedTwoStepRetraction P R one δ Q) := by
  have h0 := forcedTop_mem hR ht ht.1 ⟨Q, hI.posetName⟩ ⟨S, hI.orderName⟩ ⟨∅, hI.topName⟩ (hI.top one ht.1)
  apply equivalentSuborderRetraction_spec (boundedNameTwoStep_preorder hR ht hI.posetName hI.orderName hI.preorder)
    (normalizedNameTwoStep_subset hR ht)
    (fun _ hn _ hm ↦ normalizedNameTwoStep_inclusion_order_iff hR ht hn hm)
    (guardedTwoStepMap_function hR ht hδ hP h0)
  intro z hz
  rw [guardedTwoStepMap_value hz]
  have hp : kpair.π₁ z ∈ P := by
    obtain ⟨p, hp, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    simpa using hp
  exact guardedTwoStepCode_equivalent hR ht hδ hP hI.posetName hI.orderName h0 (hI.preorder _ hp) hz

theorem normalizedTwoStepRetraction_below [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅) :
    ∀ z ∈ Cₛ, ⟨(normalizedTwoStepRetraction P R one δ Q) ‘ z, z⟩ₖ ∈ Rₛ := by
  have h0 := forcedTop_mem hR ht ht.1 ⟨Q, hI.posetName⟩ ⟨S, hI.orderName⟩ ⟨∅, hI.topName⟩ (hI.top one ht.1)
  intro z hz
  apply (equivalentSuborderRetraction_equivalent
    (boundedNameTwoStep_preorder hR ht hI.posetName hI.orderName hI.preorder) ?_ hz).1
  intro w hw
  rw [guardedTwoStepMap_value hw]
  have hp : kpair.π₁ w ∈ P := by
    obtain ⟨p, hp, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hw).1
    simpa using hp
  exact guardedTwoStepCode_equivalent hR ht hδ hP hI.posetName hI.orderName h0 (hI.preorder _ hp) hw

theorem nameTwoStepOrderOn_top {C : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hI : IsForcingIterand P R Q S ∅)
    (hC : C ⊆ Cₛ) (hroot : ⟨one, ∅⟩ₖ ∈ C) :
    IsForcingTop C (nameTwoStepOrderOn P R S C) ⟨one, ∅⟩ₖ := by
  refine ⟨hroot, ?_⟩
  intro z hz
  have hb := hC z hz
  obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hb).1
  obtain ⟨hp, _, hτ, hm⟩ := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hb
  exact (pair_mem_nameTwoStepOrderOn _ _ _ _ _ _ _ _).mpr ⟨hz, hroot, ht.2 p hp,
    forcedTop_above hR ht hp ⟨Q, hI.posetName⟩ ⟨S, hI.orderName⟩ ⟨∅, hI.topName⟩ ⟨τ, hτ⟩ (hI.top p hp) hm⟩

theorem normalizedNameTwoStep_top [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅) :
    IsForcingTop Cₙ Rₙ ⟨one, ∅⟩ₖ := by
  apply nameTwoStepOrderOn_top hR ht hI (normalizedNameTwoStep_subset hR ht)
  rw [pair_mem_normalizedNameTwoStep]
  have h0δ : (∅ : V) ∈ hierarchy δ := by
    apply (mem_hierarchy_iff_rank_mem _ _).mpr
    rw [rank_empty]
    exact ordinal_mem_of_subset_mem (empty_subset (rank P)) ((mem_hierarchy_iff_rank_mem _ _).mp hP)
  exact ⟨ht.1, h0δ, empty_forcingName P, forcingLeastRankName_empty hR ht.1,
    forcedTop_mem hR ht ht.1 ⟨Q, hI.posetName⟩ ⟨S, hI.orderName⟩ ⟨∅, hI.topName⟩ (hI.top one ht.1)⟩

theorem boundedNameTwoStep_top [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hP : P ∈ hierarchy δ) (hI : IsForcingIterand P R Q S ∅) :
    IsForcingTop Cₛ Rₛ ⟨one, ∅⟩ₖ :=
  nameTwoStepOrderOn_top hR ht hI (fun _ hz ↦ hz)
    (normalizedNameTwoStep_subset hR ht _ (normalizedNameTwoStep_top hR ht hP hI).1)

theorem normalizedTwoStepRetraction_prefix {z : V} (hz : z ∈ Cₛ) :
    kpair.π₁ ((normalizedTwoStepRetraction P R one δ Q) ‘ z) = kpair.π₁ z := by
  change kpair.π₁ ((equivalentSuborderRetraction Cₛ Cₙ (guardedTwoStepMap P R one δ Q)) ‘ z) = _
  rw [equivalentSuborderRetraction_value hz]
  classical
  by_cases hn : z ∈ Cₙ
  · simp [equivalentSuborderFix, hn]
  · simp only [equivalentSuborderFix, hn, ↓reduceIte, guardedTwoStepMap_value hz,
      guardedTwoStepCode_prefix]

end ZFVP
