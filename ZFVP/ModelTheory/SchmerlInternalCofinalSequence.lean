import ZFVP.ModelTheory.SchmerlCodedCofinalSuccessor
import ZFVP.ModelTheory.SchmerlInternalCodedChainElementarity
import ZFVP.SetTheory.RegularOrdinalAddition
import ZFVP.SetTheory.OrdinalLeftOne

/-! Choose actual least ordinal upper bounds at successive stages, then
shift past a parameter stage to obtain an actual cofinal strict sequence. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def stageUpperCandidates (C P R β : V) : V :=
  {d ∈ structureDomain (C ‘ (succ β)) ; d ∈ P ∧
    ∀ x ∈ structureDomain (C ‘ β), x ∈ P → ⟨x, d⟩ₖ ∈ R ∧ x ≠ d}

theorem mem_stageUpperCandidates (C P R β d : V) :
    d ∈ stageUpperCandidates C P R β ↔ d ∈ structureDomain (C ‘ (succ β)) ∧ d ∈ P ∧
      ∀ x ∈ structureDomain (C ‘ β), x ∈ P → ⟨x, d⟩ₖ ∈ R ∧ x ≠ d := mem_sep_iff

instance stageUpperCandidates_definable : ℒₛₑₜ-function₄[V] stageUpperCandidates := by
  have hh : ℒₛₑₜ-relation₅[V] (fun X C P R β ↦ ∀ d, d ∈ X ↔
      d ∈ structureDomain (C ‘ (succ β)) ∧ d ∈ P ∧
      ∀ x ∈ structureDomain (C ‘ β), x ∈ P → ⟨x, d⟩ₖ ∈ R ∧ x ≠ d) := by definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [mem_stageUpperCandidates]
  rfl

noncomputable def leastStageUpperPoint (C P R β : V) : V := ⋂ˢ stageUpperCandidates C P R β

instance leastStageUpperPoint_definable : ℒₛₑₜ-function₄[V] leastStageUpperPoint := by
  unfold leastStageUpperPoint
  definability

attribute [local irreducible] stageUpperCandidates leastStageUpperPoint

theorem leastStageUpperPoint_spec {κ C P R β : V} [IsOrdinal κ]
    (hsub : structureDomain (C ‘ (succ β)) ⊆ κ)
    (hne : IsNonempty (stageUpperCandidates C P R β)) :
    leastStageUpperPoint C P R β ∈ structureDomain (C ‘ (succ β)) ∧
      leastStageUpperPoint C P R β ∈ P ∧
      ∀ x ∈ structureDomain (C ‘ β), x ∈ P →
        ⟨x, leastStageUpperPoint C P R β⟩ₖ ∈ R ∧ x ≠ leastStageUpperPoint C P R β := by
  let := hne
  apply (mem_stageUpperCandidates C P R β _).mp
  rw [leastStageUpperPoint]
  exact IsOrdinal.sInter_mem (fun d hd ↦
    IsOrdinal.of_mem (hsub d ((mem_stageUpperCandidates C P R β d).mp hd).1))

theorem exists_internalCofinalStrictChain_of_stageBounds {κ C P R β₀ : V}
    (hκ : IsRegularCardinal κ) (hC : IsInternalRelationalChain membershipLanguageCode κ C)
    (hcarrier : codedChainCarrier κ C = κ) (hβ₀ : β₀ ∈ κ)
    (hP : P ⊆ κ)
    (hbound : ∀ β ∈ κ, β₀ ⊆ β → IsNonempty (stageUpperCandidates C P R β)) :
    ∃ c : V, IsInternalCofinalStrictChain κ P R c := by
  let : IsOrdinal κ := hκ.1.1
  let : IsOrdinal β₀ := IsOrdinal.of_mem hβ₀
  let σ : V → V := ordinalAdd β₀
  have hσ (i : V) (hi : i ∈ κ) : σ i ∈ κ := regularCardinal_ordinalAdd_closed hκ hβ₀ hi
  have hD (i : V) (hi : i ∈ κ) : structureDomain (C ‘ i) ⊆ κ :=
    hcarrier ▸ codedChainCarrier_includes hi
  have hs (i : V) (hi : i ∈ κ) :
      leastStageUpperPoint C P R (σ i) ∈ structureDomain (C ‘ (succ (σ i))) ∧
      leastStageUpperPoint C P R (σ i) ∈ P ∧
      ∀ x ∈ structureDomain (C ‘ (σ i)), x ∈ P →
        ⟨x, leastStageUpperPoint C P R (σ i)⟩ₖ ∈ R ∧ x ≠ leastStageUpperPoint C P R (σ i) := by
    let : IsOrdinal i := IsOrdinal.of_mem hi
    exact leastStageUpperPoint_spec (hD _ (regularCardinal_succ_closed hκ (hσ i hi)))
      (hbound (σ i) (hσ i hi) (subset_ordinalAdd β₀ i))
  let c := definableGraph κ (fun i ↦ leastStageUpperPoint C P R (σ i)) (by
    dsimp only [σ]
    definability)
  have hc : c ∈ P ^ κ := definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦ (hs i hi).2.1)
  have hv (i : V) (hi : i ∈ κ) : c ‘ i = leastStageUpperPoint C P R (σ i) :=
    value_definableGraph _ _ _ hi
  refine ⟨c, hc, ?_, ?_⟩
  · intro i hi j hj hij
    let : IsOrdinal j := IsOrdinal.of_mem hj
    let : IsOrdinal (σ j) := IsOrdinal.of_mem (hσ j hj)
    have hijσ : σ i ∈ σ j := ordinalAdd_mem hij
    have hsucc : succ (σ i) ⊆ σ j := by
      intro x hx
      rcases mem_succ_iff.mp hx with rfl | hx
      · exact hijσ
      · exact IsTransitive.transitive _ hijσ x hx
    rw [hv i hi, hv j hj]
    exact (hs j hj).2.2 _
      (hC.increasing _ (regularCardinal_succ_closed hκ (hσ i hi)) _ (hσ j hj) hsucc _ (hs i hi).1)
      (hs i hi).2.1
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := (mem_codedChainCarrier κ C x).mp (hcarrier.symm ▸ hP x hx)
    let : IsOrdinal i := IsOrdinal.of_mem hi
    refine ⟨i, hi, ?_⟩
    rw [hv i hi]
    exact ((hs i hi).2.2 x
      (hC.increasing i hi (σ i) (hσ i hi) (ordinal_subset_add_right β₀ i) x hxi) hx).1

end ZFVP.Schmerl
