import ZFVP.ModelTheory.ElementaryForcingTableWitness
import ZFVP.ModelTheory.InternalGenericTruth
import ZFVP.ModelTheory.InternalTarskiVaughtCriterion
import ZFVP.SetTheory.FormulaFamilyRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem elementaryInclusion_of_positive_witness_closure {X B : V}
    (hX : IsNonempty X) (hB : IsNonempty B) (hsub : X ⊆ B)
    (hpos : ∀ n ∈ (ω : V), ∀ φ ∈ formulaSet membershipLanguageCode ∅ (succ n),
      ∀ b ∈ X ^ n,
      (∃ x ∈ B, MembershipSatisfies B (succ n) φ (assignmentPrepend n b x)) →
      ∃ x ∈ X, MembershipSatisfies B (succ n) φ (assignmentPrepend n b x)) :
    IsElementaryInclusion X B := by
  apply elementaryInclusion_of_witness_closure hX hB hsub hpos
  intro n hn φ hφ b hb hex
  have hbB := mem_function_of_mem_function_of_subset hb hsub
  have hψ := negateFormula_mem membershipLanguageCode_valid hφ
  obtain ⟨x, hx, ht⟩ := hpos n hn _ hψ b hb (by
    obtain ⟨x, hx, ht⟩ := hex
    exact ⟨x, hx, (membershipSatisfies_negate hφ (assignmentPrepend_mem_function hn hbB hx)).mpr ht⟩)
  exact ⟨x, hx, (membershipSatisfies_negate hφ
    (assignmentPrepend_mem_function hn hbB (hsub x hx))).mp ht⟩

namespace ForcingContext

noncomputable def hullImage (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) (X : V) : A.Model :=
  range (A.evaluationGraph (X ∩ D) (fun τ hτ ↦ hD τ (mem_inter_iff.mp hτ).2))

theorem mem_hullImage_iff (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) (X : V) (x : A.Model) :
    x ∈ A.hullImage D hD X ↔
      ∃ τ : V, ∃ hτ : τ ∈ X ∩ D, x = A.ofName ⟨τ, hD τ (mem_inter_iff.mp hτ).2⟩ :=
  A.mem_range_evaluationGraph_iff _ _ _

theorem hullImage_subset (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) (X : V) :
    A.hullImage D hD X ⊆ range (A.evaluationGraph D hD) := by
  intro x hx
  obtain ⟨τ, hτ, rfl⟩ := (A.mem_hullImage_iff D hD X x).mp hx
  exact (A.mem_range_evaluationGraph_iff D hD _).mpr ⟨τ, (mem_inter_iff.mp hτ).2, rfl⟩

theorem hullImage_nonempty (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) {X B : V} [IsTransitive B]
    (hX : IsElementaryInclusion X B) (hDX : D ∈ X) (hne : IsNonempty D) :
    IsNonempty (A.hullImage D hD X) := by
  obtain ⟨τ, hτ⟩ := (hX.nonempty_inter_member hDX hne).nonempty
  have hτ' : τ ∈ X ∩ D := mem_inter_iff.mpr ⟨(mem_inter_iff.mp hτ).2, (mem_inter_iff.mp hτ).1⟩
  exact ⟨_, (A.mem_hullImage_iff D hD X _).mpr ⟨τ, hτ', rfl⟩⟩

theorem hullImage_ground_witness (A : ForcingContext V) {D X B U n φ s : V}
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) [IsTransitive B] [IsSequenceSupport U]
    (hX : IsElementaryInclusion X B) (hlow : hierarchy (succ (ω : V)) ⊆ X)
    (hUX : U ∈ X) (hDX : D ∈ X) (hDU : D ⊆ U) (hPU : A.P ⊆ U) (hPX : A.P ⊆ X)
    (hTX : internalForcingTruthTable A.P A.R D ∈ X)
    (hn : n ∈ (ω : V)) (hφ : IsMembershipFormulaCode (succ n) φ)
    (hs : s ∈ (X ∩ D) ^ n)
    (hex : ∃ x ∈ range (A.evaluationGraph D hD),
      MembershipSatisfies (range (A.evaluationGraph D hD)) (succ (A.check n)) (A.check φ)
        (assignmentPrepend (A.check n)
          (A.sequenceValue s (A.nameSequence_of_mem_function
            (fun τ hτ ↦ hD τ (mem_inter_iff.mp hτ).2) hs)) x)) :
    ∃ x ∈ A.hullImage D hD X,
      MembershipSatisfies (range (A.evaluationGraph D hD)) (succ (A.check n)) (A.check φ)
        (assignmentPrepend (A.check n)
          (A.sequenceValue s (A.nameSequence_of_mem_function
            (fun τ hτ ↦ hD τ (mem_inter_iff.mp hτ).2) hs)) x) := by
  let := hierarchy_transitive (ω : V)
  have hωX : (ω : V) ∈ X := hlow _ (ordinal_subset_hierarchy _ _ (mem_succ_self _))
  have hωsub : (ω : V) ⊆ X := fun i hi ↦ hlow i
    (hierarchy_transitive _ |>.mem_trans (ordinal_subset_hierarchy _ i hi)
      (hierarchy_mem (mem_succ_self (ω : V))))
  have hsD := mem_function_of_mem_function_of_subset hs (fun τ hτ ↦ (mem_inter_iff.mp hτ).2)
  have hsX := hX.finite_function_mem_of_support hUX hωsub hn
    (mem_function_of_mem_function_of_subset hs (fun τ hτ ↦
      mem_inter_iff.mpr ⟨(mem_inter_iff.mp hτ).1, hDU τ (mem_inter_iff.mp hτ).2⟩))
  have hφU : φ ∈ U := membershipFormulaCode_formula_mem_support hφ
  have hφX : φ ∈ X := hlow φ
    ((hierarchy_transitive _).mem_trans
      ((kpair_components_mem_transitive (formulaFamily_subset_hierarchy_omega _ hφ)).2)
      (hierarchy_mem (mem_succ_self (ω : V))))
  obtain ⟨x, hx, ht⟩ := hex
  obtain ⟨τ, hτ, rfl⟩ := (A.mem_range_evaluationGraph_iff D hD x).mp hx
  have htruth := A.groundGenericTruth D hD hφ (assignmentPrepend n s τ)
    (assignmentPrepend_mem_function hn hsD hτ)
  rw [A.check_succ, A.sequenceValue_prepend hD hn hsD hτ] at htruth
  obtain ⟨p, hpG, hpforce⟩ := htruth.mp ht
  have hpP := A.generic.1.1 p hpG
  obtain ⟨ν, hν, hforce⟩ := hX.forcing_table_witness hUX hωX hDX hTX
    (hωsub n hn) hsX (hPX p hpP) hφX hDU (hPU p hpP) hφU hn hφ hsD hpP
    ⟨τ, hτ, (mem_internalForcingSet hφ).mp hpforce⟩
  refine ⟨A.ofName ⟨ν, hD ν (mem_inter_iff.mp hν).2⟩,
    (A.mem_hullImage_iff D hD X _).mpr ⟨ν, hν, rfl⟩, ?_⟩
  have htν := (A.groundGenericTruth D hD hφ (assignmentPrepend n s ν)
    (assignmentPrepend_mem_function hn hsD (mem_inter_iff.mp hν).2)).mpr
      ⟨p, hpG, (mem_internalForcingSet hφ).mpr hforce⟩
  rwa [A.check_succ, A.sequenceValue_prepend hD hn hsD (mem_inter_iff.mp hν).2] at htν

theorem hullImage_elementary (A : ForcingContext V) {D X B U : V}
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) [IsTransitive B] [IsSequenceSupport U]
    (hX : IsElementaryInclusion X B) (hlow : hierarchy (succ (ω : V)) ⊆ X)
    (hUX : U ∈ X) (hDX : D ∈ X) (hDU : D ⊆ U) (hPU : A.P ⊆ U) (hPX : A.P ⊆ X)
    (hTX : internalForcingTruthTable A.P A.R D ∈ X) (hne : IsNonempty D) :
    IsElementaryInclusion (A.hullImage D hD X) (range (A.evaluationGraph D hD)) := by
  have himgne := A.hullImage_nonempty D hD hX hDX hne
  have himgsub := A.hullImage_subset D hD X
  have hrne : IsNonempty (range (A.evaluationGraph D hD)) := by
    obtain ⟨x, hx⟩ := himgne.nonempty
    exact ⟨x, himgsub x hx⟩
  apply elementaryInclusion_of_positive_witness_closure himgne hrne himgsub
  intro m hm φ hφ b hb hex
  have hmcheck : m ∈ A.check (ω : V) := by
    change m ∈ A.checkEmbedding (ω : V)
    rwa [A.checkEmbedding.map_omega]
  obtain ⟨n, hn, rfl⟩ := (A.mem_check_iff (ω : V) m).mp hmcheck
  have hc : IsMembershipFormulaCode (A.check (succ n)) φ := by
    rw [A.check_succ]
    exact (mem_formulaSet_iff _ _ _ _).mp hφ
  obtain ⟨l, ψ, hl, hψ, hground⟩ := A.checkEmbedding.membershipFormulaCode_preimages hc
  have hel : succ n = l := (A.check_eq_iff _ _).mp hl
  subst l
  change φ = A.check ψ at hψ
  subst φ
  obtain ⟨s, hsN, hs, rfl⟩ := A.finite_sequenceValue_surjective (X ∩ D)
    (fun τ hτ ↦ hD τ (mem_inter_iff.mp hτ).2) hn hb
  exact A.hullImage_ground_witness hD hX hlow hUX hDX hDU hPU hPX hTX hn hground hs hex

theorem lowRank_hullImage_elementary (A : ForcingContext V) {β X B : V}
    (hβ : Cn 1 β) [IsTransitive B] (hX : IsElementaryInclusion X B)
    (hlow : hierarchy (succ (ω : V)) ⊆ X)
    (hβX : hierarchy β ∈ X) (hDX : lowRankNameSet A.P β ∈ X)
    (hP : A.P ∈ hierarchy β) (hPX : A.P ⊆ X)
    (hTX : internalForcingTruthTable A.P A.R (lowRankNameSet A.P β) ∈ X) :
    IsElementaryInclusion (A.hullImage (lowRankNameSet A.P β) (A.lowRankNameSet_names β) X)
      (hierarchy (A.check β)) := by
  let := hβ.ordinal
  let : IsSequenceSupport (hierarchy β) := ((cn_successor_iff 0 β).mp hβ).2.support
  rw [← A.lowRankEvaluation_range hβ hP]
  apply A.hullImage_elementary (A.lowRankNameSet_names β) hX hlow hβX hDX
    (lowRankNameSet_subset A.P β) ((hierarchy_transitive β).transitive _ hP) hPX hTX
  exact ⟨∅, (mem_lowRankNameSet A.P β ∅).mpr ⟨IsCodingSupport.empty_mem, empty_forcingName A.P⟩⟩

end ForcingContext
end ZFVP
