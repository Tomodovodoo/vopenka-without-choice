import ZFVP.ModelTheory.SuccessorRankLiftDC
import ZFVP.ModelTheory.WoodinCollapseLift
import ZFVP.SetTheory.WoodinRestorationCutoff
import ZFVP.SetTheory.WoodinClosedFiniteModels

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinCollapseModel

theorem initial_dependentChoiceBelow {κ c δ ρ γ e : V}
    (hκ : IsRegularCardinal κ) (hc : IsRegularCardinal c)
    (hδ : IsWoodinSupercompact δ) (hcδ : c ⊆ δ) (hκδ : κ ∈ δ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α)
    {G : Set V} (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G)
    (hρ : IsSigmaOneStarCorrect ρ) (hγ : IsSigmaOneStarCorrect γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hcrit : IsCriticalPoint (hierarchy (succ ρ)) e c)
    (hcρ : c ∈ ρ) (hκc : κ ∈ c) (hec : e ‘ c = δ) :
    letI := hδ.1.1
    ∀ η ∈ (initialContext hκ hc hcδ hG).check c, InternalDependentChoiceAt η := by
  let := hδ.1.1
  let := hc.1.1
  let := hρ.1.ordinal
  let := hierarchy_transitive (succ ρ)
  let L := initial_liftData hκ hc hcδ hG hρ.1 hγ.1 he hcrit hcρ hκc hec
  have heone : e ‘ (initialContext hκ hc hcδ hG).one = (woodinCollapseContext hκ δ G hG).one := by
    change e ‘ (∅ : V) = ∅
    exact hcrit.fixed_below (IsOrdinal.toIsTransitive.mem_trans (hκ.2.1 ∅ (by simp)) hκc)
  have hh := L.dependentChoiceBelow_iff hδ hρ hγ heone
    (hρ.1.successor_closed c hcρ) (mem_succ_self c)
  apply hh.mpr
  rw [hec]
  exact woodinSupercompact_collapse_dependentChoice hκ hδ hκδ hDC hG

end WoodinCollapseModel

theorem ForcingContext.forcing_witness_below (A : ForcingContext V) {q : V}
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → ForcingName A.P)
    (ht : φ.Evalb (A.ofName ∘ v)) (hq : q ∈ A.G) :
    ∃ s, s ∈ forcingFormula A.P A.R φ (standardTuple (fun i ↦ (v i).val)) ∧ ⟨s, q⟩ₖ ∈ A.R := by
  obtain ⟨r, hrG, hr⟩ := (A.formula_truth φ v).mp ht
  obtain ⟨s, hsG, hsr, hsq⟩ := A.generic.1.2.2.2 r hrG q hq
  exact ⟨s, (forcingFormula_regular A.order φ _).2.1 r hr s (A.generic.1.1 s hsG) hsr, hsq⟩

theorem ForcingContext.dependentChoiceBelow_forcing_witness (A : ForcingContext V) {c q : V}
    (hDC : ∀ η ∈ A.check c, InternalDependentChoiceAt η) (hq : q ∈ A.G) :
    ∃ s, s ∈ forcingFormula A.P A.R dependentChoiceBelowFormula
      (standardTuple ![checkName A.one c]) ∧ ⟨s, q⟩ₖ ∈ A.R := by
  let n : ForcingName A.P := ⟨checkName A.one c, checkName_isName A.top.1 c⟩
  have ht : dependentChoiceBelowFormula.Evalb ![A.ofName n] :=
    (Defined.eval_iff (φ := dependentChoiceBelowFormula) ![A.check c]).mpr hDC
  have ht' : dependentChoiceBelowFormula.Evalb (A.ofName ∘ ![n]) := by
    have hv : A.ofName ∘ ![n] = ![A.ofName n] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    rw [hv]
    exact ht
  have hh := A.forcing_witness_below dependentChoiceBelowFormula ![n] ht' hq
  have hv : (fun i ↦ (![n] i).val) = ![checkName A.one c] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [hv] at hh
  exact hh

theorem woodinCollapse_forces_below_critical_countable [Countable V] {κ c δ ρ γ e p : V}
    (hκ : IsRegularCardinal κ) (hc : IsRegularCardinal c)
    (hδ : IsWoodinSupercompact δ) (hcδ : c ⊆ δ) (hκδ : κ ∈ δ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α)
    (hρ : IsSigmaOneStarCorrect ρ) (hγ : IsSigmaOneStarCorrect γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hcrit : IsCriticalPoint (hierarchy (succ ρ)) e c)
    (hcρ : c ∈ ρ) (hκc : κ ∈ c) (hec : e ‘ c = δ) (hp : p ∈ woodinCollapse κ c) :
    p ∈ forcingFormula (woodinCollapse κ c) (woodinCollapseOrder κ c) dependentChoiceBelowFormula
      (standardTuple ![checkName ∅ c]) := by
  let := hδ.1.1
  let := hc.1.1
  have hreg := forcingFormula_regular (woodinCollapse_poset κ c).1 dependentChoiceBelowFormula
    (standardTuple ![checkName ∅ c])
  apply hreg.2.2 p hp
  intro q hq _
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric (woodinCollapse_poset κ δ).1
    (woodinCollapse_mono hcδ q hq)
  let A := WoodinCollapseModel.initialContext hκ hc hcδ hG
  have hqA : q ∈ A.G := ⟨hqG, hq⟩
  have htruth := WoodinCollapseModel.initial_dependentChoiceBelow hκ hc hδ hcδ hκδ hDC
    hG hρ hγ he hcrit hcρ hκc hec
  exact A.dependentChoiceBelow_forcing_witness htruth hqA

theorem IsWoodinSupercompact.strictRestorationCutoff_countable [Countable V] {κ δ : V}
    (hδ : IsWoodinSupercompact δ) (hκ : IsRegularCardinal κ) (hκδ : κ ∈ δ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) :
    ∃ c ∈ δ, IsWoodinRestorationCutoff κ c := by
  let := hδ.1.1
  let := hκ.1.1
  obtain ⟨γ, hδγ, hγ⟩ := sigmaOneStarCorrect_unbounded δ
  let := hγ.1.ordinal
  have h0γ : (∅ : V) ∈ hierarchy γ := (hierarchy_transitive γ).mem_trans empty_mem_ω
    (ordinal_mem_hierarchy_iff.mpr hγ.1.omega_lt)
  obtain ⟨_, ρ, _, hρ, _, _, e, he, c, hc, hec, _, hκc⟩ :=
    hδ.highCritical.2.2 γ hδγ hγ ∅ h0γ κ hκδ
  let := hρ.1.ordinal
  let := hc.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  have hcρ := successorRankEmbedding_criticalPoint_lt_height he hc (hec.symm ▸ hδγ)
  have hcδ : c ∈ δ := hec ▸ hc.lt_value he
  have hωc : (ω : V) ∈ c := ordinal_mem_of_subset_mem hκ.2.1 hκc
  have hci : IsChoicelessInaccessible c := by
    refine ⟨hc.ordinal, hωc, ?_⟩
    intro α hα g
    exact successorRankEmbedding_criticalPoint_no_rank_cofinalMap hρ.1 hγ.1 he hc hcρ
      (hierarchy_mem hα)
  refine ⟨c, hcδ, hκc, hci, ?_⟩
  intro p hp
  exact woodinCollapse_forces_below_critical_countable hκ hci.regular hδ
    (IsOrdinal.toIsTransitive.transitive _ hcδ) hκδ hDC hρ hγ he hc hcρ hκc hec hp

def strictWoodinRestorationFormula : SetTheorySemisentence 2 :=
  “κ δ. !regularCardinalFormula κ ∧ !woodinSupercompactFormula δ ∧ κ ∈ δ ∧
    !dependentChoiceBelowFormula κ → ∃ c ∈ δ, !woodinRestorationCutoffFormula κ c”

theorem eval_strictWoodinRestorationFormula (v : Fin 2 → V) :
    strictWoodinRestorationFormula.Evalb v ↔
      (IsRegularCardinal (v 0) → IsWoodinSupercompact (v 1) → v 0 ∈ v 1 →
        (∀ α ∈ v 0, InternalDependentChoiceAt α) → ∃ c ∈ v 1, IsWoodinRestorationCutoff (v 0) c) := by
  simp [strictWoodinRestorationFormula]

theorem strictWoodinRestorationFormula_countable [Countable V] (v : Fin 2 → V) :
    strictWoodinRestorationFormula.Evalb v := by
  apply (eval_strictWoodinRestorationFormula v).mpr
  intro hκ hδ hκδ hDC
  exact hδ.strictRestorationCutoff_countable hκ hκδ hDC

theorem IsWoodinSupercompact.strictRestorationCutoff {κ δ : V}
    (hδ : IsWoodinSupercompact δ) (hκ : IsRegularCardinal κ) (hκδ : κ ∈ δ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) :
    ∃ c ∈ δ, IsWoodinRestorationCutoff κ c := by
  have hh := eval_of_countable_zf strictWoodinRestorationFormula
    (fun _ _ _ _ _ v ↦ strictWoodinRestorationFormula_countable v) ![κ, δ]
  exact (eval_strictWoodinRestorationFormula _).mp hh hκ hδ hκδ hDC

theorem woodinRestorationCutoff_lt_supercompact {κ δ : V}
    (hκ : IsRegularCardinal κ) (hδ : IsWoodinSupercompact δ) (hκδ : κ ∈ δ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) : woodinRestorationCutoff κ ∈ δ := by
  let := hδ.1.1
  obtain ⟨c, hcδ, hc⟩ := hδ.strictRestorationCutoff hκ hκδ hDC
  let := hc.2.1.1
  exact ordinal_mem_of_subset_mem (woodinRestorationCutoff_le hc) hcδ

end ZFVP
