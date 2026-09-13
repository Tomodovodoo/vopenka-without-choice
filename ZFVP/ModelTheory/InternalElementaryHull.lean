import ZFVP.ModelTheory.InternalSkolemStep
import ZFVP.ModelTheory.InternalTarskiVaughtCriterion

/-! Internal elementary hulls of bounded cardinality, constructed using Choice. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem naturalIteration_subset_of_mem (F : V → V) (hF : ℒₛₑₜ-function₁ F) (A : V)
    (hinc : ∀ X, X ⊆ F X) :
    ∀ n ∈ (ω : V), ∀ m ∈ n, naturalIteration F hF A m ⊆ naturalIteration F hF A n := by
  apply naturalNumber_induction
    (fun n ↦ ∀ m ∈ n, naturalIteration F hF A m ⊆ naturalIteration F hF A n) (by definability)
  · intro m hm
    simp [zero_def] at hm
  · intro n hn ih m hm
    rw [naturalIteration_succ F hF A hn]
    rcases mem_succ_iff.mp hm with rfl | hm
    · exact hinc _
    · exact subset_trans (ih m hm) (hinc _)

theorem naturalIteration_directed (F : V → V) (hF : ℒₛₑₜ-function₁ F) (A : V)
    (hinc : ∀ X, X ⊆ F X) :
    ∀ i ∈ (ω : V), ∀ j ∈ (ω : V), ∃ k ∈ (ω : V),
      naturalIteration F hF A i ⊆ naturalIteration F hF A k ∧
      naturalIteration F hF A j ⊆ naturalIteration F hF A k := by
  intro i hi j hj
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  rcases IsOrdinal.mem_trichotomy i j with hij | hij | hji
  · exact ⟨j, hj, naturalIteration_subset_of_mem F hF A hinc j hj i hij, subset_refl _⟩
  · exact ⟨j, hj, hij ▸ subset_refl _, subset_refl _⟩
  · exact ⟨i, hi, subset_refl _, naturalIteration_subset_of_mem F hF A hinc i hi j hji⟩

theorem mem_naturalIterationUnion_iff (F : V → V) (hF : ℒₛₑₜ-function₁ F) (A x : V) :
    x ∈ ⋃ˢ range (naturalIterationGraph F hF A) ↔
      ∃ n ∈ (ω : V), x ∈ naturalIteration F hF A n := by
  constructor
  · intro hx
    obtain ⟨Y, hY, hxY⟩ := mem_sUnion_iff.mp hx
    obtain ⟨n, hnY⟩ := mem_range_iff.mp hY
    have hn : n ∈ (ω : V) := by simpa using mem_domain_of_kpair_mem hnY
    have he : naturalIteration F hF A n = Y :=
      (naturalIterationGraph_value F hF A hn).symm.trans (value_eq_of_kpair_mem hnY)
    exact ⟨n, hn, he.symm ▸ hxY⟩
  · rintro ⟨n, hn, hx⟩
    refine mem_sUnion_iff.mpr ⟨naturalIteration F hF A n, ?_, hx⟩
    rw [← naturalIterationGraph_value F hF A hn]
    exact value_mem_range (IsFunction.mem_function (naturalIterationGraph F hF A)) (by simpa using hn)

theorem exists_small_internal_elementary_hull (hAC : InternalChoice V) {lam A B : V}
    (hlam : IsInitialOrdinal lam) (hω : (ω : V) ⊆ lam) (hAne : IsNonempty A)
    (hAB : A ⊆ B) (hA : A ≤# lam)
    (hcode : (formulaFamily membershipLanguageCode ∅ : V) ≤# lam) :
    ∃ X, A ⊆ X ∧ IsElementaryInclusion X B ∧ X ≤# lam := by
  classical
  obtain ⟨α, hα, w, hw, hwi⟩ :=
    (wellOrderable_iff_cardLE_ordinal B).mp (wellOrderable_of_internalChoice hAC B)
  let := hα
  let C : V := formulaFamily membershipLanguageCode ∅
  let F := internalSkolemStep B w C
  have hF : ℒₛₑₜ-function₁ F :=
    Language.DefinableFunction.substitution
      (f := ![fun _ : Fin 1 → V ↦ B, fun _ ↦ w, fun _ ↦ C, fun v ↦ v 0])
      internalSkolemStep_definable
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ]; all_goals definability)
  let X := ⋃ˢ range (naturalIterationGraph F hF A)
  have hx (x : V) : x ∈ X ↔ ∃ n ∈ (ω : V), x ∈ naturalIteration F hF A n :=
    mem_naturalIterationUnion_iff F hF A x
  have hsub : ∀ n ∈ (ω : V), naturalIteration F hF A n ⊆ B :=
    naturalIteration_invariant F hF A (fun Y ↦ Y ⊆ B) (by definability) hAB
      (fun _ hY ↦ internalSkolemStep_subset hY)
  have hXB : X ⊆ B := by
    intro x hxX
    obtain ⟨n, hn, hxn⟩ := (hx x).mp hxX
    exact hsub n hn x hxn
  have hAX : A ⊆ X := by
    intro a ha
    exact (hx a).mpr ⟨0, by simp, (naturalIteration_zero F hF A).symm ▸ ha⟩
  have hXne : IsNonempty X := by
    obtain ⟨a, ha⟩ := hAne.nonempty
    exact ⟨a, hAX a ha⟩
  have hBne : IsNonempty B := by
    obtain ⟨a, ha⟩ := hAne.nonempty
    exact ⟨a, hAB a ha⟩
  have hsize : X ≤# lam := naturalIteration_union_cardLE hAC hlam hω F hF hA
    (fun Y hY ↦ internalSkolemStep_cardLE hAC hlam hω hcode hY)
  have hdir := naturalIteration_directed F hF A (subset_internalSkolemStep B w C)
  have hcapture {n b : V} (hn : n ∈ (ω : V)) (hb : b ∈ X ^ n) :
      ∃ i ∈ (ω : V), b ∈ naturalIteration F hF A i ^ n :=
    directedUnion_assignment_capture (naturalIteration F hF A) (by definability)
      (show IsNonempty (ω : V) from ⟨0, by simp⟩) hdir hx hn hb
  have hclosed {n φ b d : V} (hn : n ∈ (ω : V)) (hd : d ∈ (ω : V))
      (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ X ^ n)
      (hex : ∃ x ∈ B, MembershipSatisfies B (succ n) φ (assignmentPrepend n b x) ↔ d = 0) :
      ∃ x ∈ X, MembershipSatisfies B (succ n) φ (assignmentPrepend n b x) ↔ d = 0 := by
    obtain ⟨i, hi, hbi⟩ := hcapture hn hb
    have hc : ⟨succ n, φ⟩ₖ ∈ C := (mem_formulaSet_iff _ _ _ _).mp hφ
    obtain ⟨x, hxstep, hs⟩ := internalSkolemStep_witness hw hwi hn hd hc hbi hex
    refine ⟨x, (hx x).mpr ⟨succ i, ω_succ_closed hi, ?_⟩, hs⟩
    rw [naturalIteration_succ F hF A hi]
    exact hxstep
  refine ⟨X, hAX, elementaryInclusion_of_witness_closure hXne hBne hXB ?_ ?_, hsize⟩
  · intro n hn φ hφ b hb hex
    obtain ⟨x, hxB, hs⟩ := hex
    obtain ⟨y, hy, hs'⟩ := hclosed hn (by simp : (0 : V) ∈ ω) hφ hb
      ⟨x, hxB, by simpa using hs⟩
    exact ⟨y, hy, hs'.mpr rfl⟩
  · intro n hn φ hφ b hb hex
    obtain ⟨x, hxB, hs⟩ := hex
    obtain ⟨y, hy, hs'⟩ := hclosed hn (by simp : (succ (0 : V)) ∈ ω) hφ hb
      ⟨x, hxB, ⟨fun ht ↦ (hs ht).elim,
        fun he ↦ (succ_empty_ne_empty (by simpa [zero_def] using he)).elim⟩⟩
    exact ⟨y, hy, fun ht ↦ succ_empty_ne_empty (by simpa [zero_def] using hs'.mp ht)⟩

end ZFVP
