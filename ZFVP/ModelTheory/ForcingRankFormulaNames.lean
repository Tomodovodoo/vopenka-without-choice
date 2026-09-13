import ZFVP.ModelTheory.ForcingRankRestrictedNames
import ZFVP.ModelTheory.SuccessorRankSeparation
import ZFVP.SetTheory.WoodinCollapseFormula
import ZFVP.ModelTheory.SuccessorRankLiftChecks

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def rankFormulaName (P R δ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → V) : V :=
  {z ∈ lowRankNameSet P δ ×ˢ P ; kpair.π₂ z ∈ forcingFormula P R φ
    (assignmentPrepend (n : V) (standardTuple v) (kpair.π₁ z))}

theorem pair_mem_rankFormulaName (P R δ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → V) (σ p : V) :
    ⟨σ, p⟩ₖ ∈ rankFormulaName P R δ φ v ↔ σ ∈ lowRankNameSet P δ ∧ p ∈ P ∧
      p ∈ forcingFormula P R φ (standardTuple (σ :> v)) := by
  simp [rankFormulaName, standardTuple, and_assoc]

theorem rankFormulaName_isName (P R δ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → V) : IsForcingName P (rankFormulaName P R δ φ v) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  exact ⟨σ, p, hp, rfl, ((mem_lowRankNameSet _ _ _).mp hσ).2⟩

theorem rankFormulaName_subset {P R δ : V} [IsOrdinal δ]
    (hlim : ∀ α ∈ δ, succ α ∈ δ) (hP : P ∈ hierarchy δ)
    {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    rankFormulaName P R δ φ v ⊆ hierarchy δ := by
  intro z hz
  obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  exact kpair_mem_hierarchy_limit hlim ((mem_lowRankNameSet _ _ _).mp hσ).1
    ((hierarchy_transitive δ).mem_trans hp hP)

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def rankSelectedName (δ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → ForcingName A.P) : ForcingName A.P :=
  ⟨rankFormulaName A.P A.R δ φ (fun i ↦ (v i).val), rankFormulaName_isName _ _ _ _ _⟩

theorem mem_rankSelectedName (δ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → ForcingName A.P) (x : A.Model) :
    x ∈ A.ofName (A.rankSelectedName δ φ v) ↔
      φ.Evalb (x :> (A.ofName ∘ v)) ∧
        ∃ σ : ForcingName A.P, σ.val ∈ hierarchy δ ∧ x = A.ofName σ := by
  have htruth (σ : ForcingName A.P) :
      φ.Evalb (A.ofName σ :> (A.ofName ∘ v)) ↔
        ∃ p ∈ A.G, p ∈ forcingFormula A.P A.R φ (standardTuple (σ.val :> fun i ↦ (v i).val)) := by
    have hv : (fun i ↦ A.ofName ((σ :> v) i)) = A.ofName σ :> (A.ofName ∘ v) := by
      funext i
      exact Fin.cases rfl (fun _ ↦ rfl) i
    have hb : (fun i ↦ ((σ :> v) i).val) = (σ.val :> fun i ↦ (v i).val) := by
      funext i
      exact Fin.cases rfl (fun _ ↦ rfl) i
    have hh := A.formula_truth φ (σ :> v)
    rw [hv, hb] at hh
    exact hh
  rw [A.mem_ofName_iff]
  constructor
  · rintro ⟨σ, p, hpG, hp, he⟩
    obtain ⟨hσ, _, hpφ⟩ := (pair_mem_rankFormulaName _ _ _ _ _ _ _).mp hp
    exact ⟨he.symm ▸ (htruth σ).mpr ⟨p, hpG, hpφ⟩, σ,
      ((mem_lowRankNameSet _ _ _).mp hσ).1, he⟩
  · rintro ⟨ht, σ, hσ, rfl⟩
    obtain ⟨p, hpG, hp⟩ := (htruth σ).mp ht
    exact ⟨σ, p, hpG, (pair_mem_rankFormulaName _ _ _ _ _ _ _).mpr
      ⟨(mem_lowRankNameSet _ _ _).mpr ⟨hσ, σ.property⟩, A.generic.1.1 p hpG, hp⟩, rfl⟩

theorem rankSelectedName_value {δ : V} (hδ : IsChoicelessInaccessible δ)
    (hP : A.P ∈ hierarchy δ) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → ForcingName A.P) (x : A.Model) :
    x ∈ A.ofName (A.rankSelectedName δ φ v) ↔
      x ∈ hierarchy (A.check δ) ∧ φ.Evalb (x :> (A.ofName ∘ v)) := by
  rw [A.mem_rankSelectedName, A.mem_checked_hierarchy_iff_low_name_of_inaccessible hδ hP]
  exact and_comm

end ForcingContext

def rankSelectionPredicate {n : ℕ} (θ : SetTheorySemisentence (n + 1 + 5)) :
    SetTheorySemisentence (n + 5) :=
  .exs (.exs ((boundedKpairFormula.subst ![.bvar 2, .bvar 1, .bvar 0]).and
    (forcingSystemSubst θ (.bvar 3) (.bvar 4) (.bvar 5) (.bvar 6) (.bvar 0)
      (.bvar 1 :> forcingParameterTerms 7 rfl))))

theorem rankSelectionPredicate_sigmaOne {n : ℕ} {θ : SetTheorySemisentence (n + 1 + 5)}
    (hθ : IsSigmaFormula 1 θ) : IsSigmaFormula 1 (rankSelectionPredicate θ) :=
  .exs (.exs (.and (.bounded (boundedKpairFormula_bounded.subst _)) (hθ.subst _)))

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem rankEvalExs {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    φ.exs.Evalb v ↔ ∃ x, φ.Evalb (x :> v) := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem rankEvalAnd {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

theorem eval_rankSelectionPredicate {n : ℕ} (θ : SetTheorySemisentence (n + 1 + 5))
    (z P R Γ F : V) (v : Fin n → V) :
    (rankSelectionPredicate θ).Evalb (z :> P :> R :> Γ :> F :> v) ↔
      ∃ σ p : V, z = ⟨σ, p⟩ₖ ∧ θ.Evalb (P :> R :> Γ :> F :> p :> σ :> v) := by
  simp [rankSelectionPredicate, rankEvalExs, rankEvalAnd, forcingSystemSubst, Semiformula.eval_substs, forcingParameterTerms,
    Matrix.comp_vecCons', Function.comp_def]

theorem rankFormulaName_separation {P R δ : V} (hR : IsForcingPreorder P R)
    {n : ℕ} {φ : SetTheorySemisentence (n + 1)} {θ : SetTheorySemisentence (n + 1 + 5)}
    (hm : IsForcingTranslation (V := V) false φ θ) (v : Fin n → V)
    (hn : ∀ i, IsForcingName P (v i)) (z : V) :
    z ∈ rankFormulaName P R δ φ v ↔ z ∈ lowRankNameSet P δ ×ˢ P ∧
      (rankSelectionPredicate θ).Evalb (z :> P :> R :> ∅ :> ∅ :> v) := by
  rw [eval_rankSelectionPredicate]
  constructor
  · intro hz
    obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    have hf := ((pair_mem_rankFormulaName _ _ _ _ _ _ _).mp hz).2.2
    exact ⟨kpair_mem_iff.mpr ⟨hσ, hp⟩, σ, p, rfl,
      (hm P R ∅ ∅ hR (by simp) (σ :> v)
        (fun i ↦ Fin.cases ((mem_lowRankNameSet _ _ _).mp hσ).2 hn i) p).mpr hf⟩
  · rintro ⟨hz, σ, p, rfl, ht⟩
    obtain ⟨hσ, hp⟩ := kpair_mem_iff.mp hz
    exact (pair_mem_rankFormulaName _ _ _ _ _ _ _).mpr ⟨hσ, hp,
      (hm P R ∅ ∅ hR (by simp) (σ :> v)
        (fun i ↦ Fin.cases ((mem_lowRankNameSet _ _ _).mp hσ).2 hn i) p).mp ht⟩

theorem successorRankEmbedding_value_rankFormulaName {ρ γ e P R α : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hP : P ∈ hierarchy ρ) (hR : R ∈ hierarchy ρ) (hα : IsOrdinal α) (hαρ : α ∈ hierarchy ρ)
    (hord : IsForcingPreorder P R) (hord' : IsForcingPreorder (e ‘ P) (e ‘ R))
    {n : ℕ} {φ : SetTheorySemisentence (n + 1)} (hφ : IsSigmaFormula 1 φ)
    (v : Fin n → V) (hv : ∀ i, v i ∈ hierarchy ρ) (hn : ∀ i, IsForcingName P (v i)) :
    e ‘ (rankFormulaName P R α φ v) = rankFormulaName (e ‘ P) (e ‘ R) (e ‘ α) φ (fun i ↦ e ‘ (v i)) := by
  let := hρ.ordinal
  let := hγ.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  have hH := hρ.hierarchy_closed hα hαρ
  have hN := subset_mem_hierarchy_limit hρ.successor_closed hH (lowRankNameSet_subset P α)
  have hB := prod_mem_hierarchy_limit hρ.successor_closed hN hP
  have hν : rankFormulaName P R α φ v ∈ hierarchy ρ :=
    subset_mem_hierarchy_limit hρ.successor_closed hB sep_subset
  have h0 : (∅ : V) ∈ hierarchy ρ := (hierarchy_transitive ρ).mem_trans empty_mem_ω
    (ordinal_mem_hierarchy_iff.mpr hρ.omega_lt)
  have he0 : e ‘ (∅ : V) = ∅ := he.value_empty
    (hierarchy_mono (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz)) _ h0)
  obtain ⟨θ, hθ, hm⟩ := hφ.forcing_translation (V := V) false (by decide)
  have hs := successorRankEmbedding_separation hρ hγ he (rankSelectionPredicate_sigmaOne hθ)
    (P :> R :> ∅ :> ∅ :> v)
    (by intro i; exact Fin.cases hP (fun j ↦ Fin.cases hR
      (fun k ↦ Fin.cases h0 (fun l ↦ Fin.cases h0 hv l) k) j) i) hν hB
    (rankFormulaName_separation hord hm v hn)
  have hepar : (fun i ↦ e ‘ ((P :> R :> ∅ :> ∅ :> v) i)) =
      (e ‘ P :> e ‘ R :> ∅ :> ∅ :> fun i ↦ e ‘ (v i)) := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl
      (fun k ↦ Fin.cases he0 (fun l ↦ Fin.cases he0 (fun _ ↦ rfl) l) k) j) i
  have heB : e ‘ (lowRankNameSet P α ×ˢ P) = lowRankNameSet (e ‘ P) (e ‘ α) ×ˢ (e ‘ P) := by
    rw [successorRankEmbedding_value_product hρ hγ he hN hP,
      successorRankEmbedding_value_lower_nameSet hρ hγ he hP hα hαρ]
  rw [hepar, heB] at hs
  apply mem_ext
  intro z
  exact (hs z).trans (rankFormulaName_separation hord' hm (fun i ↦ e ‘ (v i))
    (fun i ↦ (successorRankEmbedding_forcingName_iff hρ hγ he hP (hv i)).mp (hn i)) z).symm

noncomputable def rankUniverseName (P δ : V) : V := lowRankNameSet P δ ×ˢ P

theorem rankUniverseName_isName (P δ : V) : IsForcingName P (rankUniverseName P δ) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp hz
  exact ⟨σ, p, hp, rfl, ((mem_lowRankNameSet _ _ _).mp hσ).2⟩

theorem rankUniverseName_mem {ρ P δ : V} (hρ : Cn 1 ρ)
    (hP : P ∈ hierarchy ρ) (hδ : IsOrdinal δ) (hδρ : δ ∈ hierarchy ρ) :
    rankUniverseName P δ ∈ hierarchy ρ := by
  let := hρ.ordinal
  exact prod_mem_hierarchy_limit hρ.successor_closed
    (subset_mem_hierarchy_limit hρ.successor_closed (hρ.hierarchy_closed hδ hδρ)
      (lowRankNameSet_subset P δ)) hP

theorem successorRankEmbedding_value_rankUniverseName {ρ γ e P δ : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hP : P ∈ hierarchy ρ) (hδ : IsOrdinal δ) (hδρ : δ ∈ hierarchy ρ) :
    e ‘ (rankUniverseName P δ) = rankUniverseName (e ‘ P) (e ‘ δ) := by
  let := hρ.ordinal
  have hN := subset_mem_hierarchy_limit hρ.successor_closed (hρ.hierarchy_closed hδ hδρ)
    (lowRankNameSet_subset P δ)
  rw [rankUniverseName, successorRankEmbedding_value_product hρ hγ he hN hP,
    successorRankEmbedding_value_lower_nameSet hρ hγ he hP hδ hδρ]
  rfl

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def rankUniverse (δ : V) : ForcingName A.P :=
  ⟨rankUniverseName A.P δ, rankUniverseName_isName _ _⟩

theorem rankUniverse_value {δ : V} (hδ : IsChoicelessInaccessible δ)
    (hP : A.P ∈ hierarchy δ) : A.ofName (A.rankUniverse δ) = hierarchy (A.check δ) := by
  apply mem_ext
  intro x
  rw [A.mem_ofName_iff, A.mem_checked_hierarchy_iff_low_name_of_inaccessible hδ hP]
  constructor
  · rintro ⟨σ, p, hpG, hp, he⟩
    exact ⟨σ, ((mem_lowRankNameSet _ _ _).mp (kpair_mem_iff.mp hp).1).1, he⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, A.one, externalForcingFilter_top A.generic.1 A.top,
      kpair_mem_iff.mpr ⟨(mem_lowRankNameSet _ _ _).mpr ⟨hσ, σ.property⟩, A.top.1⟩, rfl⟩

end ForcingContext

noncomputable def rankCollapseName (P R one κ δ : V) : V :=
  rankFormulaName P R δ sigmaOneWoodinConditionFormula
    ![checkName one κ, checkName one δ, rankUniverseName P δ]

theorem rankCollapseName_isName (P R one κ δ : V) :
    IsForcingName P (rankCollapseName P R one κ δ) := rankFormulaName_isName _ _ _ _ _

theorem twoStep_rankFormula_conditions_subset {P R δ : V} (hδ : IsChoicelessInaccessible δ)
    (hP : P ∈ hierarchy δ) {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    twoStepConditions P R (rankFormulaName P R δ φ v) ∅ ⊆ hierarchy δ := by
  let := hδ.1
  intro z hz
  obtain ⟨p, hp, σ, hσ, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  have hσV : σ ∈ hierarchy δ := by
    rcases mem_union_iff.mp hσ with hdom | hempty
    · obtain ⟨q, hq⟩ := mem_domain_iff.mp hdom
      exact ((mem_lowRankNameSet _ _ _).mp ((pair_mem_rankFormulaName _ _ _ _ _ _ _).mp hq).1).1
    · rw [mem_singleton_iff.mp hempty]
      exact ordinal_mem_hierarchy_iff.mpr (IsOrdinal.toIsTransitive.mem_trans empty_mem_ω hδ.2.1)
  exact kpair_mem_hierarchy_limit hδ.rankCriterion.2.2.1
    ((hierarchy_transitive δ).mem_trans hp hP) hσV

theorem successorRankEmbedding_fixes_rankCollapse_conditions {ρ γ e c P R one κ : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hc : IsCriticalPoint (hierarchy (succ ρ)) e c) (hcρ : c ∈ ρ)
    (hci : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c) :
    ∀ z ∈ twoStepConditions P R (rankCollapseName P R one κ c) ∅, e ‘ z = z :=
  fun z hz ↦ successorRankEmbedding_fixed_below_criticalPoint hρ hγ he hc hcρ z
    (twoStep_rankFormula_conditions_subset hci hP _ _ z hz)

theorem successorRankEmbedding_value_rankCollapseName {ρ γ e P R one κ δ : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hP : P ∈ hierarchy ρ) (hR : R ∈ hierarchy ρ) (hone : one ∈ P)
    (hκ : κ ∈ hierarchy ρ) (hδ : IsOrdinal δ) (hδρ : δ ∈ hierarchy ρ)
    (hord : IsForcingPreorder P R) (hord' : IsForcingPreorder (e ‘ P) (e ‘ R)) :
    e ‘ (rankCollapseName P R one κ δ) =
      rankCollapseName (e ‘ P) (e ‘ R) (e ‘ one) (e ‘ κ) (e ‘ δ) := by
  let := hρ.ordinal
  have ho := (hierarchy_transitive ρ).mem_trans hone hP
  have hv : ∀ i : Fin 3, (![checkName one κ, checkName one δ, rankUniverseName P δ] i) ∈ hierarchy ρ := by
    simp [Fin.forall_fin_iff_zero_and_forall_succ, hρ.checkName_closed ho hκ,
      hρ.checkName_closed ho hδρ, rankUniverseName_mem hρ hP hδ hδρ]
  have hn : ∀ i : Fin 3, IsForcingName P (![checkName one κ, checkName one δ, rankUniverseName P δ] i) := by
    simp [Fin.forall_fin_iff_zero_and_forall_succ, checkName_isName hone, rankUniverseName_isName]
  unfold rankCollapseName
  rw [successorRankEmbedding_value_rankFormulaName hρ hγ he hP hR hδ hδρ hord hord'
    sigmaOneWoodinConditionFormula_sigmaOne _ hv hn]
  congr 1
  funext i
  exact Fin.cases (successorRankEmbedding_value_checkName hρ hγ he ho hκ)
    (fun j ↦ Fin.cases (successorRankEmbedding_value_checkName hρ hγ he ho hδρ)
      (fun k ↦ Fin.cases (successorRankEmbedding_value_rankUniverseName hρ hγ he hP hδ hδρ)
        (fun l ↦ Fin.elim0 l) k) j) i

namespace ForcingContext
variable (A : ForcingContext V)

noncomputable def rankCollapse (κ δ : V) : ForcingName A.P :=
  ⟨rankCollapseName A.P A.R A.one κ δ, rankCollapseName_isName _ _ _ _ _⟩

theorem rankCollapse_value {κ δ : V} (hδ : IsChoicelessInaccessible δ)
    (hP : A.P ∈ hierarchy δ) (hκ : κ ⊆ δ) :
    A.ofName (A.rankCollapse κ δ) = woodinCollapse (A.check κ) (A.check δ) := by
  let v : Fin 3 → ForcingName A.P :=
    ![⟨checkName A.one κ, checkName_isName A.top.1 κ⟩,
      ⟨checkName A.one δ, checkName_isName A.top.1 δ⟩, A.rankUniverse δ]
  have hv : A.ofName ∘ v = ![A.check κ, A.check δ, hierarchy (A.check δ)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl
      (fun k ↦ Fin.cases (A.rankUniverse_value hδ hP) (fun l ↦ Fin.elim0 l) k) j) i
  have hn : A.rankCollapse κ δ = A.rankSelectedName δ sigmaOneWoodinConditionFormula v := by
    apply Subtype.ext
    change rankFormulaName _ _ _ _ _ = rankFormulaName _ _ _ _ _
    congr 1
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
  rw [hn]
  apply mem_ext
  intro x
  have hi := A.check_inaccessible_of_small hδ hP
  let := hi.1
  rw [A.rankSelectedName_value hδ hP, hv, eval_sigmaOneWoodinConditionFormula]
  exact ⟨And.right, fun hx ↦ ⟨woodinCollapse_condition_mem_hierarchy hi.regular
    ((A.checkEmbedding.subset_iff _ _).mpr hκ) hx, hx⟩⟩

end ForcingContext

end ZFVP
