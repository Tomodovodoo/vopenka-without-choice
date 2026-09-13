import ZFVP.ModelTheory.SerialEvaluatedHull
import ZFVP.ModelTheory.SerialHullTableReflection
import ZFVP.SetTheory.SingularWeaklyLSHull
import ZFVP.SetTheory.FiniteCollapseRank

/-! Usuba Proposition 3.6, the dependent-choice conclusion. A singular weakly
LS cardinal supplies a hull containing every finite collapse condition. Bounded
forcing witness tables give a countable serial subset in its generic extension. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CollapseModel

theorem dependentChoice_of_singular_weaklyLS [Countable V] {κ : V}
    (hκ : IsWeaklyLSCardinal κ) (hsing : internalCofinality κ ∈ κ)
    {G : Set V} (hG : IsExternalForcingGeneric (collapseConditions (hierarchy κ))
      (collapseOrder (hierarchy κ)) G) :
    InternalDependentChoice (collapseContext (hierarchy κ) G hG).Model := by
  let M := collapseContext (hierarchy κ) G hG
  let := hκ.1.1
  have hsucc (δ : V) (hδ : δ ∈ κ) : succ δ ∈ κ :=
    initial_succ_mem hκ.1 (IsOrdinal.toIsTransitive.transitive _ hκ.2.1) hδ
  have hPV : M.P ⊆ hierarchy κ := collapseConditions_subset_hierarchy hκ.2.1 hsucc
  have hD : IsNonempty (hierarchy κ) := ⟨(ω : V), ordinal_subset_hierarchy κ ω hκ.2.1⟩
  intro A S hA hS
  obtain ⟨AN, rfl⟩ := M.ofName_surjective A
  obtain ⟨SN, rfl⟩ := M.ofName_surjective S
  have hprem := (eval_serialHullPremiseFormula
    (fun i ↦ M.ofName (![AN, SN] i))).mpr ⟨hA, hS⟩
  obtain ⟨p, hpG, hp⟩ := (M.formula_truth serialHullPremiseFormula ![AN, SN]).mp hprem
  let T0 := serialInitialWitnessTable M.P M.R AN.val
  let T1 := serialNextWitnessTable M.P M.R AN.val SN.val
  let I := M.P ×ˢ domain AN.val
  let z := ⟨T0, ⟨T1, I⟩ₖ⟩ₖ
  let α := rank ({z, κ} : V)
  let := hierarchy_transitive α
  have hzα : z ∈ hierarchy α := (mem_hierarchy_iff_rank_mem _ _).mpr
    (rank_mem (show z ∈ ({z, κ} : V) by simp))
  have hκα : κ ∈ α := by
    simpa only [rank_of_ordinal] using rank_mem (show κ ∈ ({z, κ} : V) by simp)
  obtain ⟨X, hX, hVX, hzX, e, he, hre⟩ := hκ.singular_hull hsing
    (IsOrdinal.toIsTransitive.transitive _ hκα) hzα
  have h0 := hX.kpair_components_mem hzX
  have h1 := hX.kpair_components_mem h0.2
  have hPX : M.P ⊆ X := subset_trans hPV hVX
  have hpairs : ∀ q ∈ M.P, ∀ τ ∈ domain AN.val, ⟨q, τ⟩ₖ ∈ hierarchy α := by
    intro q hq τ hτ
    exact (hierarchy_transitive α).mem_trans (show ⟨q, τ⟩ₖ ∈ I by simp [I, hq, hτ])
      (hX.subset _ h1.2)
  let C := X ∩ domain AN.val
  have hC : ∀ ν ∈ C, IsForcingName M.P ν := by
    intro ν hν
    obtain ⟨t, hνt⟩ := mem_domain_iff.mp (mem_inter_iff.mp hν).2
    exact forcingName_subname AN.property hνt
  have hcX : IsInternallyCountable (M.check X) := M.internallyCountable_checked_of_surjection
    (check_internallyCountable hG hD) he hre
  have hc : IsInternallyCountable (M.check C) := internallyCountable_subset hcX (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := (M.mem_check_iff C x).mp hx
    exact (M.check_mem_iff ν X).mpr (mem_inter_iff.mp hν).1)
  exact M.serialPath_of_dense_name_witnesses AN SN hC hc hpG
    (hX.serial_initial_dense hPX M.order M.top AN SN h0.1 hp)
    (hX.serial_next_dense hPX M.order M.top AN SN h1.1 hpairs hp)

end CollapseModel
end ZFVP
