import ZFVP.ModelTheory.FilterProductPresentation
import ZFVP.ModelTheory.ProductHomogeneity
import ZFVP.ModelTheory.MemEquivElementary
import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.SetTheory.NameActionClosure

/-! Decision of a formula at the value of a ground name under a small filter: for a ground
`Q`-name `τ` and a localized `Q̌`-filter `H` meeting the ground dense sets, a formula with ground
parameters holds at `nameValue H τ̌` in the Levy extension iff some `q` with `q̌ ∈ H` lies in the
ground decision set, the set of `q` such that `(q, ∅)` forces the formula at the lifted name in
`Q × Coll(ω, <κ)`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The ground decision set of `φ` at the lifted name of `τ` with parameters `a`. -/
noncomputable def filterDecisionSet (κ Q S one τ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (a : Fin n → V) : V :=
  {q ∈ Q ; ⟨q, ∅⟩ₖ ∈ forcingFormula (Q ×ˢ levyCollapse κ) (productOrder Q S (levyCollapse κ) (levyOrder κ)) φ
    (standardTuple (nameAction (leftEmbedding Q ∅) τ :> fun i ↦ checkName ⟨one, ∅⟩ₖ (a i)))}

theorem mem_filterDecisionSet_iff (κ Q S one τ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (a : Fin n → V) (q : V) :
    q ∈ filterDecisionSet κ Q S one τ φ a ↔ q ∈ Q ∧
      ⟨q, ∅⟩ₖ ∈ forcingFormula (Q ×ˢ levyCollapse κ) (productOrder Q S (levyCollapse κ) (levyOrder κ)) φ
        (standardTuple (nameAction (leftEmbedding Q ∅) τ :> fun i ↦ checkName ⟨one, ∅⟩ₖ (a i))) :=
  mem_sep_iff

theorem filterDecisionSet_subset (κ Q S one τ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (a : Fin n → V) : filterDecisionSet κ Q S one τ φ a ⊆ Q :=
  sep_subset

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- A formula with ground parameters at the value of a ground name under a small filter is decided
by the ground decision set. -/
theorem filter_decision {Q S one : V} (hQ : IsForcingPreorder Q S)
    (htop : IsForcingTop Q S one) {H : (levyContext κ hG).Model}
    (hHQ : H ⊆ (levyContext κ hG).check Q)
    (hfilter : IsForcingFilter ((levyContext κ hG).check Q) ((levyContext κ hG).check S) H)
    (hgen : ∀ D : V, ForcingDense Q S D → ∃ q ∈ D, (levyContext κ hG).check q ∈ H)
    (hloc : IsLocalized hG H) {τ : V} (hτ : IsForcingName Q τ)
    {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (a : Fin n → V) :
    φ.Evalb (nameValue H ((levyContext κ hG).check τ) :> fun i ↦ (levyContext κ hG).check (a i)) ↔
      ∃ q, (levyContext κ hG).check q ∈ H ∧ q ∈ filterDecisionSet κ Q S one τ φ a := by
  obtain ⟨X, g, hXP, hXR, hXone, hgmem, hgcheck, hname, -, hgen'⟩ :=
    exists_filter_product_presentation hAC hU hc hω hκ hG hQ htop hHQ hfilter hgen hloc
  obtain ⟨ρ, hρ, hgx⟩ := hname τ hτ
  have hone₂ : (∅ : V) ∈ levyCollapse κ := (levyCollapse_top κ).1
  have h₂ : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have t₂ : IsForcingTop (levyCollapse κ) (levyOrder κ) ∅ := levyCollapse_top κ
  let v : Fin (n + 1) → ForcingName X.P :=
    ρ :> fun i ↦ ⟨checkName X.one (a i), checkName_isName X.top.1 (a i)⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin (n + 1) → V, w = (nameAction (leftEmbedding Q ∅) τ :>
      fun i ↦ checkName ⟨one, ∅⟩ₖ (a i)) := ⟨_, rfl⟩
  have hvals : (fun i ↦ (v i).val) = w := by
    rw [hw]
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact hρ
    · simp only [v, Matrix.cons_val_succ]
      rw [hXone]
  have hw0 : w 0 = nameAction (leftEmbedding Q ∅) τ := by
    rw [hw]
    rfl
  have hwsucc : ∀ j, w (Fin.succ j) = checkName ⟨one, ∅⟩ₖ (a j) := by
    intro j
    rw [hw]
    rfl
  have h1 : φ.Evalb (nameValue H ((levyContext κ hG).check τ) :> fun i ↦ (levyContext κ hG).check (a i)) ↔
      φ.Evalb (fun i ↦ X.ofName (v i)) := by
    rw [evalb_of_memEquiv g hgmem φ]
    have hfun : (fun i ↦ g ((nameValue H ((levyContext κ hG).check τ) :>
        fun i ↦ (levyContext κ hG).check (a i)) i)) = fun i ↦ X.ofName (v i) := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp only [Matrix.cons_val_zero]
        exact hgx
      · simp only [Matrix.cons_val_succ]
        rw [hgcheck]
        rfl
    rw [hfun]
  rw [h1, X.formula_truth φ v, hvals]
  obtain ⟨F, hF⟩ : ∃ F : V, F = forcingFormula X.P X.R φ (standardTuple w) := ⟨_, rfl⟩
  have hF' : F = forcingFormula (Q ×ˢ levyCollapse κ) (productOrder Q S (levyCollapse κ) (levyOrder κ)) φ
      (standardTuple w) := by
    rw [hF, hXP, hXR]
  have hS : ∀ q, q ∈ filterDecisionSet κ Q S one τ φ a ↔ q ∈ Q ∧ ⟨q, ∅⟩ₖ ∈ F := by
    intro q
    rw [mem_filterDecisionSet_iff, hF', hw]
  rw [← hF]
  have hfirst : ∀ s q : V, ⟨s, q⟩ₖ ∈ X.G → ⟨s, q⟩ₖ ∈ F → ⟨s, ∅⟩ₖ ∈ F := by
    intro s q hG' hsq
    have hsqP : ⟨s, q⟩ₖ ∈ X.P := X.generic.1.1 _ hG'
    rw [hXP] at hsqP
    obtain ⟨hs, hq⟩ := kpair_mem_iff.mp hsqP
    rw [hF'] at hsq ⊢
    refine forced_by_first_of_homogeneous hQ h₂ t₂ (levyCollapse_homogeneous κ) φ w ?_ ?_ hs hq hsq
    · intro i
      have hv : (v i).val = w i := congrFun hvals i
      have := (v i).property
      rw [hv, hXP] at this
      exact this
    · intro π hπ hfix i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rw [hw0]
        exact nameAction_secondCoordinateAction_lift hπ hone₂ hfix hτ
      · rw [hwsucc]
        exact nameAction_checkName (kpair_mem_iff.mpr ⟨htop.1, hone₂⟩)
          (secondCoordinateAction_top hone₂ hfix htop.1) (a j)
  constructor
  · rintro ⟨p, hpG, hpF⟩
    have hpP : p ∈ X.P := X.generic.1.1 _ hpG
    rw [hXP] at hpP
    obtain ⟨s, hs, q, hq, rfl⟩ := mem_prod_iff.mp hpP
    have hsF := hfirst s q hpG hpF
    have hsG : s ∈ firstProjectionGeneric X.G := ⟨q, hpG⟩
    exact ⟨s, (hgen' s).mp hsG, (hS s).mpr ⟨hs, hsF⟩⟩
  · rintro ⟨s, hsH, hsD⟩
    obtain ⟨hsQ, hsF⟩ := (hS s).mp hsD
    obtain ⟨q, hsqG⟩ := (hgen' s).mpr hsH
    have hsqP : ⟨s, q⟩ₖ ∈ X.P := X.generic.1.1 _ hsqG
    rw [hXP] at hsqP
    obtain ⟨_, hq⟩ := kpair_mem_iff.mp hsqP
    refine ⟨⟨s, ∅⟩ₖ, X.generic.1.2.2.1 _ hsqG _ ?_ ?_, hsF⟩
    · rw [hXP]
      exact kpair_mem_iff.mpr ⟨hsQ, hone₂⟩
    · rw [hXR]
      exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr
        ⟨hsQ, hq, hsQ, hone₂, hQ.2.1 s hsQ, t₂.2 q hq⟩

end

end ZFVP
