import ZFVP.ModelTheory.ForcingLowRankNames
import ZFVP.ModelTheory.SuccessorRankNameDomain
import ZFVP.ModelTheory.SuccessorRankSetOperations
import ZFVP.SetTheory.DeltaOneAtomicForcing
import ZFVP.SetTheory.AtomicForcingDictionary
import ZFVP.SetTheory.TwoStepForcing
import ZFVP.SetTheory.WoodinCollapseRank
import ZFVP.ModelTheory.ForcingSmallInaccessible
import ZFVP.ModelTheory.SuccessorRankCriticalPoint
import ZFVP.ModelTheory.SuccessorRankForcing
import ZFVP.Syntax.LevyForcingMeaning

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance lowRankNameSet_definable : ℒₛₑₜ-function₂[V] lowRankNameSet := by
  have h : ℒₛₑₜ-relation₃[V] (fun D P δ ↦ ∀ τ, τ ∈ D ↔ τ ∈ hierarchy δ ∧ IsForcingName P τ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = lowRankNameSet (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp [lowRankNameSet]

noncomputable def rankRestrictedName (P R δ τ : V) : V :=
  {z ∈ lowRankNameSet P δ ×ˢ P ; kpair.π₂ z ∈ atomicMembership P R (kpair.π₁ z) τ}

theorem pair_mem_rankRestrictedName (P R δ τ σ p : V) :
    ⟨σ, p⟩ₖ ∈ rankRestrictedName P R δ τ ↔
      σ ∈ lowRankNameSet P δ ∧ p ∈ P ∧ p ∈ atomicMembership P R σ τ := by
  simp [rankRestrictedName, and_assoc]

theorem rankRestrictedName_isName (P R δ τ : V) : IsForcingName P (rankRestrictedName P R δ τ) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  exact ⟨σ, p, hp, rfl, (mem_lowRankNameSet P δ σ).mp hσ |>.2⟩

theorem rankRestrictedName_subset {P R δ τ : V} [IsOrdinal δ]
    (hlim : ∀ α ∈ δ, succ α ∈ δ) (hP : P ∈ hierarchy δ) :
    rankRestrictedName P R δ τ ⊆ hierarchy δ := by
  intro z hz
  obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  exact kpair_mem_hierarchy_limit hlim ((mem_lowRankNameSet P δ σ).mp hσ).1
    ((hierarchy_transitive δ).mem_trans hp hP)

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def rankRestriction (δ : V) (τ : ForcingName A.P) : ForcingName A.P :=
  ⟨rankRestrictedName A.P A.R δ τ.val, rankRestrictedName_isName _ _ _ _⟩

theorem mem_rankRestriction (δ : V) (τ : ForcingName A.P) (x : A.Model) :
    x ∈ A.ofName (A.rankRestriction δ τ) ↔ x ∈ A.ofName τ ∧
      ∃ σ : ForcingName A.P, σ.val ∈ hierarchy δ ∧ x = A.ofName σ := by
  rw [A.mem_ofName_iff]
  constructor
  · rintro ⟨σ, p, hpG, hp, he⟩
    obtain ⟨hσ, _, hpτ⟩ := (pair_mem_rankRestrictedName _ _ _ _ _ _).mp hp
    have hx : A.ofName σ ∈ A.ofName τ :=
      (forcingQuotientMk_mem_iff A.P A.R A.G A.order A.generic.1 σ τ).mpr ⟨p, hpG, hpτ⟩
    exact ⟨he.symm ▸ hx, σ, ((mem_lowRankNameSet _ _ _).mp hσ).1, he⟩
  · rintro ⟨hx, σ, hσ, rfl⟩
    obtain ⟨p, hpG, hp⟩ := (forcingQuotientMk_mem_iff A.P A.R A.G A.order A.generic.1 σ τ).mp hx
    exact ⟨σ, p, hpG, (pair_mem_rankRestrictedName _ _ _ _ _ _).mpr
      ⟨(mem_lowRankNameSet _ _ _).mpr ⟨hσ, σ.property⟩, A.generic.1.1 p hpG, hp⟩, rfl⟩

theorem rankRestriction_value_of_inaccessible {δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (τ : ForcingName A.P) :
    A.ofName (A.rankRestriction δ τ) = A.ofName τ ∩ hierarchy (A.check δ) := by
  apply mem_ext
  intro x
  rw [A.mem_rankRestriction, mem_inter_iff, A.mem_checked_hierarchy_iff_low_name_of_inaccessible hδ hP]

theorem rankRestriction_value {δ : V} (hδ : IsChoicelessInaccessible δ)
    (hP : A.P ∈ hierarchy δ) (τ : ForcingName A.P) (hτ : A.ofName τ ⊆ hierarchy (A.check δ)) :
    A.ofName (A.rankRestriction δ τ) = A.ofName τ := by
  apply mem_ext
  intro x
  rw [A.rankRestriction_value_of_inaccessible hδ hP, mem_inter_iff]
  exact ⟨And.left, fun hx ↦ ⟨hx, hτ x hx⟩⟩

theorem rankRestriction_collapse_value {κ δ : V} (hδ : IsChoicelessInaccessible δ)
    (hP : A.P ∈ hierarchy δ) (hκ : κ ⊆ δ) (τ : ForcingName A.P)
    (hτ : A.ofName τ = woodinCollapse (A.check κ) (A.check δ)) :
    A.ofName (A.rankRestriction δ τ) = woodinCollapse (A.check κ) (A.check δ) := by
  rw [A.rankRestriction_value hδ hP τ, hτ]
  rw [hτ]
  exact fun _ hp ↦ woodinCollapse_condition_mem_hierarchy
    (A.check_inaccessible_of_small hδ hP).regular ((A.checkEmbedding.subset_iff _ _).mpr hκ) hp

end ForcingContext

theorem twoStep_rankRestricted_conditions_subset {P R δ τ : V} (hδ : IsChoicelessInaccessible δ)
    (hP : P ∈ hierarchy δ) :
    twoStepConditions P R (rankRestrictedName P R δ τ) ∅ ⊆ hierarchy δ := by
  let := hδ.1
  have hlim := hδ.rankCriterion.2.2.1
  intro z hz
  obtain ⟨p, hp, σ, hσ, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  have hσV : σ ∈ hierarchy δ := by
    rcases mem_union_iff.mp hσ with hdom | hempty
    · obtain ⟨q, hq⟩ := mem_domain_iff.mp hdom
      exact ((mem_lowRankNameSet _ _ _).mp ((pair_mem_rankRestrictedName _ _ _ _ _ _).mp hq).1).1
    · have he : σ = ∅ := mem_singleton_iff.mp hempty
      rw [he]
      exact ordinal_mem_hierarchy_iff.mpr (IsOrdinal.toIsTransitive.mem_trans empty_mem_ω hδ.2.1)
  exact kpair_mem_hierarchy_limit hlim ((hierarchy_transitive δ).mem_trans hp hP) hσV

theorem successorRankEmbedding_fixes_rankRestricted_conditions {ρ γ e c P R τ : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hc : IsCriticalPoint (hierarchy (succ ρ)) e c) (hcρ : c ∈ ρ)
    (hci : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c) :
    ∀ z ∈ twoStepConditions P R (rankRestrictedName P R c τ) ∅, e ‘ z = z :=
  fun z hz ↦ successorRankEmbedding_fixed_below_criticalPoint hρ hγ he hc hcρ z
    (twoStep_rankRestricted_conditions_subset hci hP z hz)

def piOneNameSetFormula : SetTheorySemisentence 3 :=
  “U P D. !isSubsetOf D U ∧
    (∀ τ ∈ D, !piOneForcingNameFormula P τ) ∧
    ∀ τ ∈ U, ¬!sigmaOneForcingNameFormula P τ ∨ τ ∈ D”

theorem piOneNameSetFormula_piOne : IsPiFormula 1 piOneNameSetFormula :=
  .and (.bounded (isSubsetOf_bounded.subst _))
    (.and (.boundedAll (.bvar 2) (piOneForcingNameFormula_piOne.subst _))
      (.boundedAll (.bvar 0) (.or (sigmaOneForcingNameFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))))

theorem eval_piOneNameSetFormula (U P D : V) : piOneNameSetFormula.Evalb ![U, P, D] ↔
    D = {τ ∈ U ; IsForcingName P τ} := by
  have he : piOneNameSetFormula.Evalb ![U, P, D] ↔ D ⊆ U ∧
      (∀ τ ∈ D, IsForcingName P τ) ∧ ∀ τ ∈ U, ¬IsForcingName P τ ∨ τ ∈ D := by
    simp [piOneNameSetFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [he]
  constructor
  · rintro ⟨hsub, hn, h⟩
    apply mem_ext
    intro τ
    rw [mem_sep_iff]
    exact ⟨fun hτ ↦ ⟨hsub τ hτ, hn τ hτ⟩, fun ⟨hτ, hN⟩ ↦ (h τ hτ).resolve_left (fun h ↦ h hN)⟩
  · rintro rfl
    refine ⟨sep_subset, fun _ h ↦ (mem_sep_iff.mp h).2, ?_⟩
    intro τ hτ
    by_cases hn : IsForcingName P τ
    · exact Or.inr (mem_sep_iff.mpr ⟨hτ, hn⟩)
    · exact Or.inl hn

theorem successorRankEmbedding_value_lower_nameSet {ρ γ e P α : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hP : P ∈ hierarchy ρ) (hα : IsOrdinal α) (hαρ : α ∈ hierarchy ρ) :
    e ‘ (lowRankNameSet P α) = lowRankNameSet (e ‘ P) (e ‘ α) := by
  let := hρ.ordinal
  have hH := hρ.hierarchy_closed hα hαρ
  have hN := subset_mem_hierarchy_limit hρ.successor_closed hH (lowRankNameSet_subset P α)
  have ht := (successorRankEmbedding_pi_iff hρ hγ he piOneNameSetFormula_piOne
    ![hierarchy α, P, lowRankNameSet P α]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hH, hP, hN])).mp
      ((eval_piOneNameSetFormula _ _ _).mpr rfl)
  have hv : (fun i ↦ e ‘ (![hierarchy α, P, lowRankNameSet P α] i)) =
      ![hierarchy (e ‘ α), e ‘ P, e ‘ (lowRankNameSet P α)] := by
    funext i
    exact Fin.cases (successorRankEmbedding_value_lower_hierarchy hρ hγ he hα hαρ).2
      (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
  rw [hv] at ht
  exact (eval_piOneNameSetFormula _ _ _).mp ht

def piOneAtomicSelectionFormula : SetTheorySemisentence 5 :=
  “ν N P R τ.
    (∀ z ∈ ν, ∃ σ ∈ N, ∃ p ∈ P,
      !boundedKpairFormula z σ p ∧ !piOneAtomicMembershipFormula P R σ τ p) ∧
    (∀ σ ∈ N, ∀ p ∈ P, ¬!(sigmaOneAtomicMembershipFormula true) P R σ τ p ∨
      ∃ z ∈ ν, !boundedKpairFormula z σ p)”

theorem piOneAtomicSelectionFormula_piOne : IsPiFormula 1 piOneAtomicSelectionFormula :=
  .and (.boundedAll (.bvar 0) (.boundedExs (.bvar 2) (.boundedExs (.bvar 4)
    (.and (.bounded (boundedKpairFormula_bounded.subst _)) (piOneAtomicMembershipFormula_piOne.subst _)))))
    (.boundedAll (.bvar 1) (.boundedAll (.bvar 3)
      (.or ((sigmaOneAtomicMembershipFormula_sigmaOne true).subst _).neg
        (.boundedExs (.bvar 2) (.bounded (boundedKpairFormula_bounded.subst _))))))

theorem eval_piOneAtomicSelectionFormula (ν N P R τ : V) :
    piOneAtomicSelectionFormula.Evalb ![ν, N, P, R, τ] ↔
      ν = {z ∈ N ×ˢ P ; kpair.π₂ z ∈ atomicMembership P R (kpair.π₁ z) τ} := by
  have he : piOneAtomicSelectionFormula.Evalb ![ν, N, P, R, τ] ↔
      (∀ z ∈ ν, ∃ σ ∈ N, ∃ p ∈ P, z = ⟨σ, p⟩ₖ ∧ p ∈ atomicMembership P R σ τ) ∧
      (∀ σ ∈ N, ∀ p ∈ P, ¬p ∈ atomicMembership P R σ τ ∨ ⟨σ, p⟩ₖ ∈ ν) := by
    simp [piOneAtomicSelectionFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
      TruthAnswer]
  rw [he]
  constructor
  · rintro ⟨hsub, hcover⟩
    apply mem_ext
    intro z
    rw [mem_sep_iff]
    constructor
    · intro hz
      obtain ⟨σ, hσ, p, hp, rfl, hm⟩ := hsub z hz
      exact ⟨kpair_mem_iff.mpr ⟨hσ, hp⟩, by simpa using hm⟩
    · rintro ⟨hz, hm⟩
      obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp hz
      have hm' : p ∈ atomicMembership P R σ τ := by simpa using hm
      exact (hcover σ hσ p hp).resolve_left (fun h ↦ h hm')
  · rintro rfl
    constructor
    · intro z hz
      obtain ⟨hz, hm⟩ := mem_sep_iff.mp hz
      obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp hz
      exact ⟨σ, hσ, p, hp, rfl, by simpa using hm⟩
    · intro σ hσ p hp
      by_cases hm : p ∈ atomicMembership P R σ τ
      · exact Or.inr (mem_sep_iff.mpr ⟨kpair_mem_iff.mpr ⟨hσ, hp⟩, by simpa using hm⟩)
      · exact Or.inl hm

theorem successorRankEmbedding_value_rankRestrictedName {ρ γ e P R α τ : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hP : P ∈ hierarchy ρ) (hR : R ∈ hierarchy ρ) (hα : IsOrdinal α)
    (hαρ : α ∈ hierarchy ρ) (hτ : τ ∈ hierarchy ρ) :
    e ‘ (rankRestrictedName P R α τ) = rankRestrictedName (e ‘ P) (e ‘ R) (e ‘ α) (e ‘ τ) := by
  let := hρ.ordinal
  have hH := hρ.hierarchy_closed hα hαρ
  have hN := subset_mem_hierarchy_limit hρ.successor_closed hH (lowRankNameSet_subset P α)
  have hν : rankRestrictedName P R α τ ∈ hierarchy ρ := subset_mem_hierarchy_limit hρ.successor_closed
    (prod_mem_hierarchy_limit hρ.successor_closed hN hP) (show rankRestrictedName P R α τ ⊆ _ from sep_subset)
  have ht := (successorRankEmbedding_pi_iff hρ hγ he piOneAtomicSelectionFormula_piOne
    ![rankRestrictedName P R α τ, lowRankNameSet P α, P, R, τ]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hν, hN, hP, hR, hτ])).mp
      ((eval_piOneAtomicSelectionFormula _ _ _ _ _).mpr rfl)
  have hv : (fun i ↦ e ‘ (![rankRestrictedName P R α τ, lowRankNameSet P α, P, R, τ] i)) =
      ![e ‘ (rankRestrictedName P R α τ), lowRankNameSet (e ‘ P) (e ‘ α), e ‘ P, e ‘ R, e ‘ τ] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases
      (successorRankEmbedding_value_lower_nameSet hρ hγ he hP hα hαρ)
      (fun k ↦ Fin.cases rfl (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl
        (fun n ↦ Fin.elim0 n) m) l) k) j) i
  rw [hv] at ht
  exact (eval_piOneAtomicSelectionFormula _ _ _ _ _).mp ht

theorem successorRankEmbedding_levyOneForcing_iff {ρ γ e P R p : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hP : P ∈ hierarchy ρ) (hR : R ∈ hierarchy ρ) (hp : p ∈ hierarchy ρ)
    (hord : IsForcingPreorder P R) (hord' : IsForcingPreorder (e ‘ P) (e ‘ R))
    {n : ℕ} {pol : LevyPolarity} {φ : SetTheorySemisentence n} (hφ : IsLevyFormula pol 1 φ)
    (v : Fin n → V) (hv : ∀ i, v i ∈ hierarchy ρ) (hn : ∀ i, IsForcingName P (v i)) :
    p ∈ forcingFormula P R φ (standardTuple v) ↔
      e ‘ p ∈ forcingFormula (e ‘ P) (e ‘ R) φ (standardTuple (fun i ↦ e ‘ (v i))) := by
  let := hρ.ordinal
  let := hγ.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  have h0 : (∅ : V) ∈ hierarchy ρ := (hierarchy_transitive ρ).mem_trans empty_mem_ω
    (ordinal_mem_hierarchy_iff.mpr hρ.omega_lt)
  have he0 : e ‘ (∅ : V) = ∅ := he.value_empty
    (hierarchy_mono (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz)) _ h0)
  obtain ⟨θ, hθ, hm⟩ := hφ.forcing_translation (V := V) false (by decide)
  have hpar : ∀ i, (P :> R :> ∅ :> ∅ :> p :> v) i ∈ hierarchy ρ := by
    intro i
    exact Fin.cases hP (fun j ↦ Fin.cases hR (fun k ↦ Fin.cases h0
      (fun l ↦ Fin.cases h0 (fun m ↦ Fin.cases hp hv m) l) k) j) i
  have ht : θ.Evalb (P :> R :> ∅ :> ∅ :> p :> v) ↔
      θ.Evalb (fun i ↦ e ‘ ((P :> R :> ∅ :> ∅ :> p :> v) i)) := by
    cases pol
    · exact successorRankEmbedding_sigma_iff hρ hγ he hθ _ hpar
    · exact successorRankEmbedding_pi_iff hρ hγ he hθ _ hpar
  have hevec : (fun i ↦ e ‘ ((P :> R :> ∅ :> ∅ :> p :> v) i)) =
      (e ‘ P :> e ‘ R :> ∅ :> ∅ :> e ‘ p :> (fun i ↦ e ‘ (v i))) := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases he0
      (fun l ↦ Fin.cases he0 (fun m ↦ Fin.cases rfl (fun _ ↦ rfl) m) l) k) j) i
  rw [hevec] at ht
  have hs := hm P R ∅ ∅ hord (by simp) v hn p
  have hi := hm (e ‘ P) (e ‘ R) ∅ ∅ hord' (by simp) (fun i ↦ e ‘ (v i))
    (fun i ↦ (successorRankEmbedding_forcingName_iff hρ hγ he hP (hv i)).mp (hn i)) (e ‘ p)
  exact hs.symm.trans (ht.trans hi)

end ZFVP
