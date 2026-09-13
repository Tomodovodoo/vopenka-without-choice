import ZFVP.ModelTheory.ClosedEvaluatedHullDC
import ZFVP.ModelTheory.ElementaryOrdinalSequenceClosure
import ZFVP.ModelTheory.UsubaCollapseModel
import ZFVP.SetTheory.SingularLSClosedHull
import ZFVP.SetTheory.UsubaCollapseRank

/-! Usuba Proposition 4.7, the actual DCκ conclusion. Strong LS closure
captures short sequences of names. Bounded forcing tables reflect dense
successor witnesses, yielding a path in a well-orderable evaluated hull. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace UsubaCollapseModel

theorem dependentChoiceAt_of_singular_LS [Countable V] {κ lam ν : V}
    (hκ : IsRegularCardinal κ) (hDC : ∀ γ ∈ κ, InternalDependentChoiceAt γ)
    (hlam : IsLSCardinal lam) (hsing : internalCofinality lam ∈ lam)
    (hκcf : κ ∈ internalCofinality lam)
    (hν : IsWeaklyLSCardinal ν) (hκν : κ ⊆ ν) (hνcf : ν ⊆ internalCofinality lam)
    {G : Set V} (hG : IsExternalForcingGeneric (usubaCollapse κ (hierarchy lam))
      (usubaCollapseOrder κ (hierarchy lam)) G) :
    InternalDependentChoiceAt ((usubaCollapseContext hκ (hierarchy lam) G hG).check κ) := by
  let M := usubaCollapseContext hκ (hierarchy lam) G hG
  let := hκ.1.1
  let := hlam.1.1
  let := hν.1.1
  have hlamSucc (δ : V) (hδ : δ ∈ lam) : succ δ ∈ lam :=
    initial_succ_mem hlam.1 (IsOrdinal.toIsTransitive.transitive _ hlam.2.1) hδ
  have hκlam : κ ∈ lam := IsOrdinal.toIsTransitive.mem_trans hκcf hsing
  have hVlamNe : IsNonempty (hierarchy lam) := ⟨ω, ordinal_subset_hierarchy lam ω hlam.2.1⟩
  intro A R hA hR
  obtain ⟨AN, rfl⟩ := M.ofName_surjective A
  obtain ⟨RN, rfl⟩ := M.ofName_surjective R
  let KN : ForcingName M.P := ⟨checkName M.one κ, checkName_isName M.top.1 κ⟩
  have hserial := (eval_dependentChoiceSerialFormula (fun i ↦ M.ofName (![KN, AN, RN] i))).mpr ⟨hA, hR⟩
  obtain ⟨p, hpG, hp⟩ := (M.formula_truth dependentChoiceSerialFormula ![KN, AN, RN]).mp hserial
  let D := domain AN.val
  let T := shortSequenceWitnessTable M.P M.R M.one κ AN.val RN.val
  let L := shorterSequences κ D
  let Q := M.P ×ˢ L
  let pack := ⟨D, T⟩ₖ
  let α₀ := rank ({pack, lam, Q, L} : V)
  let α := ordinalAdd α₀ (ω : V)
  let := hierarchy_transitive α
  have hα₀α : α₀ ∈ α := ordinalAdd_omega_gt α₀
  have hpackα : pack ∈ hierarchy α := mem_hierarchy_of_mem_stage hα₀α
    ((mem_hierarchy_iff_rank_mem _ _).mpr (rank_mem (show pack ∈ ({pack, lam, Q, L} : V) by simp)))
  have hQα : Q ∈ hierarchy α := mem_hierarchy_of_mem_stage hα₀α
    ((mem_hierarchy_iff_rank_mem _ _).mpr (rank_mem (show Q ∈ ({pack, lam, Q, L} : V) by simp)))
  have hLα : L ∈ hierarchy α := mem_hierarchy_of_mem_stage hα₀α
    ((mem_hierarchy_iff_rank_mem _ _).mpr (rank_mem (show L ∈ ({pack, lam, Q, L} : V) by simp)))
  have hlamα : lam ∈ α := by
    apply IsOrdinal.toIsTransitive.mem_trans (y := α₀) _ hα₀α
    simpa only [rank_of_ordinal] using rank_mem (show lam ∈ ({pack, lam, Q, L} : V) by simp)
  obtain ⟨τ, X, hτ, hατ, hX, hVlamX, hpackX, ⟨e, he, hre⟩, hclosed⟩ :=
    hlam.singular_closed_hull hsing hν hνcf hlamα hpackα
  let := hτ
  let := hierarchy_transitive τ
  obtain ⟨hDX, hTX⟩ := hX.kpair_components_mem hpackX
  have hDα : D ∈ hierarchy α := (kpair_components_mem_transitive hpackα).1
  have hDsub : D ⊆ hierarchy α := (hierarchy_transitive α).transitive _ hDα
  have hPX : M.P ⊆ X := subset_trans (usubaCollapse_subset_hierarchy hκ hκcf hlamSucc) hVlamX
  have hpairs : ∀ q ∈ M.P, ∀ t ∈ L, ⟨q, t⟩ₖ ∈ hierarchy τ := by
    intro q hq t ht
    exact mem_hierarchy_of_mem_stage hατ ((hierarchy_transitive α).mem_trans
      (show ⟨q, t⟩ₖ ∈ Q from kpair_mem_iff.mpr ⟨hq, ht⟩) hQα)
  let C := X ∩ D
  have hC : ∀ σ ∈ C, IsForcingName M.P σ := by
    intro σ hσ
    obtain ⟨u, hσu⟩ := mem_domain_iff.mp (mem_inter_iff.mp hσ).2
    exact forcingName_subname AN.property hσu
  let := IsFunction.of_mem he
  have hwX : IsWellOrderable (M.check X) := wellOrderable_of_surjective_function
    (check_wellOrderable hκ hG hVlamNe) ((M.check_function_iff _ _ _).mpr he)
    ((M.checkEmbedding.map_range e).symm.trans (congrArg M.check hre))
  have hwC : IsWellOrderable (M.check C) := wellOrderable_of_cardLE
    (cardLE_of_subset ((M.checkEmbedding.subset_iff C X).mpr (fun _ hz ↦ (mem_inter_iff.mp hz).1))) hwX
  have h0X : (∅ : V) ∈ X := hVlamX _ (ordinal_subset_hierarchy lam ∅
    (IsOrdinal.toIsTransitive.mem_trans empty_mem_ω hlam.2.1))
  apply M.dependentChoicePath_of_dense_short_name_witnesses AN RN hC hwC hpG
  · intro η hη s hs
    let := IsOrdinal.of_mem hη
    exact M.sequenceValue_representative_of_noNewSequences hC (shortDependentChoice hκ hG hDC hη)
      (fun g hg ↦ shortFunction_eq_check hκ hG hDC hη hg) hs
  · intro t ht q hq hqp hinput
    obtain ⟨η, hη, htη⟩ := (mem_shorterSequences _ _ _).mp ht
    let := IsOrdinal.of_mem hη
    have htL : t ∈ L := (mem_shorterSequences _ _ _).mpr ⟨η, hη,
      mem_function_of_mem_function_of_subset htη (fun _ hz ↦ (mem_inter_iff.mp hz).2)⟩
    have htB : t ∈ hierarchy τ := mem_hierarchy_of_mem_stage hατ
      ((hierarchy_transitive α).mem_trans htL hLα)
    have hηX : η ∈ X := hVlamX _ (ordinal_subset_hierarchy lam η
      (IsOrdinal.toIsTransitive.mem_trans hη hκlam))
    have htX : t ∈ X := hX.ordinal_sequence_mem h0X hηX hDX (hclosed η (hκν η hη)) hDsub htη htB
    exact hX.short_sequence_witness_dense hPX M.order M.top AN RN hTX hpairs hp
      t (mem_inter_iff.mpr ⟨htX, htL⟩) q hq hqp hinput

end UsubaCollapseModel
end ZFVP
