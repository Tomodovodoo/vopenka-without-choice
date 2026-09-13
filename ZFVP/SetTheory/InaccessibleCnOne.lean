import ZFVP.SetTheory.InaccessibleSmallRanks
import ZFVP.ModelTheory.ElementaryInclusionCollapse
import ZFVP.ModelTheory.CollapsedElementarySubmodel
import ZFVP.ModelTheory.TransitiveZFCoding
import ZFVP.SetTheory.FormulaFamilyRank
import ZFVP.Syntax.LevyCodeAbsoluteness
import ZFVP.ModelTheory.InternalElementaryHull

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsChoicelessInaccessible.cn_one_of_small_hulls (hAC : InternalChoice V)
    (hHull : ∀ lam A B : V, IsInitialOrdinal lam → (ω : V) ⊆ lam →
      IsNonempty A → A ⊆ B → A ≤# lam →
      (formulaFamily membershipLanguageCode ∅ : V) ≤# lam →
      ∃ X, A ⊆ X ∧ IsElementaryInclusion X B ∧ X ≤# lam)
    {κ : V} (hκ : IsChoicelessInaccessible κ) : Cn 1 κ := by
  let := hκ.1
  let := hierarchy_transitive κ
  let := rankDomain_nonempty hκ.2.1
  let := hκ.rankCriterion.models_zf
  let := TransitiveZF.sequenceSupport (hierarchy κ)
  refine ⟨hκ.1, ?_⟩
  intro n φ hφ b hb
  constructor
  · rintro ⟨S, hS, hbS, hs⟩
    let : IsSequenceSupport S := hS
    have hbmem : b ∈ hierarchy κ := function_mem_sequenceSupport (subset_refl _) hφ.context hb
    have hrb : rank b ∈ κ := (mem_hierarchy_iff_rank_mem _ _).mp hbmem
    let α := succ (rank b ∪ (ω : V))
    let := union_isOrdinal (rank b) (ω : V)
    let : IsOrdinal α := inferInstanceAs (IsOrdinal (succ (rank b ∪ (ω : V))))
    have hακ : α ∈ κ := hκ.rankCriterion.2.2.1 _ (ordinal_union_mem hrb hκ.2.1)
    have hωα : (ω : V) ∈ α := mem_succ_of_subset (subset_union_right _ _)
    have hbα : b ∈ hierarchy α := (mem_hierarchy_iff_rank_mem _ _).mpr
      (mem_succ_of_subset (subset_union_left _ _))
    let D := hierarchy α
    let : IsTransitive D := hierarchy_transitive α
    have hDκ : D ∈ hierarchy κ := hierarchy_mem hακ
    have hDne : IsNonempty D := ⟨ω, ordinal_mem_hierarchy_iff.mpr hωα⟩
    have hbD : b ∈ D ^ n := by
      let := IsFunction.of_mem hb
      have hbr : b ∈ range b ^ n := by
        rw [← domain_eq_of_mem_function hb]
        exact IsFunction.mem_function b
      apply mem_function_of_mem_function_of_subset hbr
      intro y hy
      obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
      exact (kpair_components_mem_transitive ((inferInstance : IsTransitive D).mem_trans hxy hbα)).2
    obtain ⟨lam, hlamκ, hlam, hDlam⟩ := hκ.small_cardinal_bound hAC hDκ
    let := hlam.1
    have hωlam : (ω : V) ⊆ lam := (initialOrdinal_cardLE_iff
      (show IsInitialOrdinal (ω : V) from omega_regular.1)).mp
      ((cardLE_of_subset (fun x hx ↦ ordinal_subset_hierarchy α x
        (IsOrdinal.toIsTransitive.mem_trans hx hωα))).trans hDlam)
    have hcod : (formulaFamily membershipLanguageCode ∅ : V) ≤# lam :=
      (cardLE_of_subset ((inferInstance : IsTransitive D).transitive _
        (formulaFamily_mem_hierarchy_of_mem_omega hωα))).trans hDlam
    let B := hierarchy (rank (D ∪ S))
    let : IsTransitive B := hierarchy_transitive _
    have hDB : D ⊆ B := subset_trans (subset_union_left D S) (subset_hierarchy_rank (D ∪ S))
    have hSB : S ⊆ B := subset_trans (subset_union_right D S) (subset_hierarchy_rank (D ∪ S))
    obtain ⟨X, hDX, hXB, hXlam⟩ := hHull lam D B hlam hωlam hDne hDB hDlam hcod
    have hsB : MembershipSatisfies B n φ b := membershipSatisfies_sigmaOne_upward hφ
      (show IsNonempty S from ⟨ω, (show IsSequenceSupport S from hS).omega_mem⟩) hXB.target_nonempty hSB hbS hs
    obtain ⟨C, hCκ, f, hf⟩ := hXB.smallTransitiveCollapse (inferInstance : IsTransitive B) hκ
      (ordinal_mem_hierarchy_iff.mpr hlamκ) hXlam
    let := hf.1
    have hi := transitiveCollapse_inverse_elementary hXB hf
    have hDC : D ⊆ C := fun x hx ↦ (transitiveCollapse_inverse_fixes hf hDX hx).1
    have hbC : b ∈ C ^ n := mem_function_of_mem_function_of_subset hbD hDC
    have hbB : b ∈ B ^ n := mem_function_of_mem_function_of_subset hbD hDB
    have hcomp : compose b (converseGraph f) = b := by
      apply function_eq_of_values (compose_function hbC hi.function) hbB
      intro i hiN
      rw [value_compose_of_mem_function hbC hi.function hiN]
      exact (transitiveCollapse_inverse_fixes hf hDX (function_value_mem hbD hiN)).2
    have he := hi.satisfies_iff hφ.context hφ.valid
      (by simpa using hbC)
    change MembershipSatisfies C n φ b ↔ MembershipSatisfies B n φ (compose b (converseGraph f)) at he
    rw [hcomp] at he
    exact membershipSatisfies_sigmaOne_upward hφ hi.source_nonempty
      (show IsNonempty (hierarchy κ) from ⟨ω, ordinal_mem_hierarchy_iff.mpr hκ.2.1⟩)
      ((hierarchy_transitive κ).transitive _ hCκ) hbC (he.mpr hsB)
  · intro hs
    exact ⟨hierarchy κ, inferInstanceAs (IsSequenceSupport (hierarchy κ)), hb, hs⟩

theorem IsChoicelessInaccessible.cn_one (hAC : InternalChoice V)
    {κ : V} (hκ : IsChoicelessInaccessible κ) : Cn 1 κ :=
  hκ.cn_one_of_small_hulls hAC
    (fun lam A B hLam hOmega hne hAB hA hcode ↦
      exists_small_internal_elementary_hull (lam := lam) (A := A) (B := B)
        hAC hLam hOmega hne hAB hA hcode)

end ZFVP
