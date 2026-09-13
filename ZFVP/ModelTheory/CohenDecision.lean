import ZFVP.ModelTheory.CohenProductPresentation
import ZFVP.ModelTheory.ProductHomogeneity
import ZFVP.ModelTheory.MemEquivElementary
import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.SetTheory.NameActionClosure

/-! The Cohen decision of a definable set of reals: a set of reals of the Levy extension definable
from ground parameters is decided on the Cohen reals by the ground set of finite sequences `s`
such that `(s, 1)` forces the defining formula at the lifted Cohen real name in the product
`2^{<ω} × Coll(ω, <κ)`. Hence every such set has the Baire property. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The finite sequences `s` with `(s, ∅) ∈ F`. -/
noncomputable def decisionBelow (F : V) : V := {s ∈ binarySequences V ; ⟨s, ∅⟩ₖ ∈ F}

theorem mem_decisionBelow_iff (F s : V) : s ∈ decisionBelow F ↔ s ∈ binarySequences V ∧ ⟨s, ∅⟩ₖ ∈ F := by
  simp only [decisionBelow, mem_sep_iff]

/-- The Cohen decision set of `φ` with parameters `a`. -/
noncomputable def cohenDecisionSet (κ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (a : Fin n → V) : V :=
  decisionBelow (forcingFormula (binarySequences V ×ˢ levyCollapse κ)
    (productOrder (binarySequences V) (sequenceOrder ((2 : ℕ) : V)) (levyCollapse κ) (levyOrder κ)) φ
    (standardTuple (nameAction (leftEmbedding (binarySequences V) ∅) (binarySequenceRealName V) :>
      fun i ↦ checkName ⟨∅, ∅⟩ₖ (a i))))

theorem cohenDecisionSet_subset (κ : V) {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (a : Fin n → V) :
    cohenDecisionSet κ φ a ⊆ binarySequences V :=
  fun s hs ↦ ((mem_decisionBelow_iff _ _).mp hs).1

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- On the Cohen reals, a formula with ground parameters is decided by the Cohen decision set. -/
theorem cohen_decision {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (a : Fin n → V)
    {x : (levyContext κ hG).Model} (hx : (levyContext κ hG).IsCohenOver x) :
    φ.Evalb (x :> fun i ↦ (levyContext κ hG).check (a i)) ↔
      Meets ((levyContext κ hG).check (cohenDecisionSet κ φ a)) x := by
  obtain ⟨X, g, ρ, hXP, hXR, hXone, hgmem, hgcheck, hρ, hgx, hgen⟩ :=
    exists_cohen_product_presentation hAC hU hc hω hκ hG hx
  have hone₂ : (∅ : V) ∈ levyCollapse κ := (levyCollapse_top κ).1
  have hone₁ : (∅ : V) ∈ binarySequences V := empty_mem_finiteSequences _
  have hQ : IsForcingPreorder (binarySequences V) (sequenceOrder ((2 : ℕ) : V)) := (sequenceOrder_poset _).1
  have h₂ : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have t₂ : IsForcingTop (levyCollapse κ) (levyOrder κ) ∅ := levyCollapse_top κ
  -- the names in the product extension
  let v : Fin (n + 1) → ForcingName X.P :=
    ρ :> fun i ↦ ⟨checkName X.one (a i), checkName_isName X.top.1 (a i)⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin (n + 1) → V, w = (nameAction (leftEmbedding (binarySequences V) ∅) (binarySequenceRealName V) :>
      fun i ↦ checkName ⟨∅, ∅⟩ₖ (a i)) := ⟨_, rfl⟩
  have hvals : (fun i ↦ (v i).val) = w := by
    rw [hw]
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact hρ
    · simp only [v, Matrix.cons_val_succ]
      rw [hXone]
  have hw0 : w 0 = nameAction (leftEmbedding (binarySequences V) ∅) (binarySequenceRealName V) := by
    rw [hw]
    rfl
  have hwsucc : ∀ j, w (Fin.succ j) = checkName ⟨∅, ∅⟩ₖ (a j) := by
    intro j
    rw [hw]
    rfl
  -- truth transfer to the product extension
  have h1 : φ.Evalb (x :> fun i ↦ (levyContext κ hG).check (a i)) ↔ φ.Evalb (fun i ↦ X.ofName (v i)) := by
    rw [evalb_of_memEquiv g hgmem φ]
    have hfun : (fun i ↦ g ((x :> fun i ↦ (levyContext κ hG).check (a i)) i)) = fun i ↦ X.ofName (v i) := by
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
  have hF' : F = forcingFormula (binarySequences V ×ˢ levyCollapse κ)
      (productOrder (binarySequences V) (sequenceOrder ((2 : ℕ) : V)) (levyCollapse κ) (levyOrder κ)) φ
      (standardTuple w) := by
    rw [hF, hXP, hXR]
  have hS : cohenDecisionSet κ φ a = decisionBelow F := by
    unfold cohenDecisionSet
    rw [hF', hw]
  rw [← hF, hS]
  -- forcing by the first coordinate
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
        exact nameAction_secondCoordinateAction_lift hπ hone₂ hfix binarySequenceRealName_isName
      · rw [hwsucc]
        exact nameAction_checkName (kpair_mem_iff.mpr ⟨hone₁, hone₂⟩)
          (secondCoordinateAction_top hone₂ hfix hone₁) (a j)
  have hcheckB : (levyContext κ hG).check (binarySequences V) = binarySequences (levyContext κ hG).Model :=
    (levyContext κ hG).check_binarySequences
  constructor
  · rintro ⟨p, hpG, hpF⟩
    have hpP : p ∈ X.P := X.generic.1.1 _ hpG
    rw [hXP] at hpP
    obtain ⟨s, hs, q, hq, rfl⟩ := mem_prod_iff.mp hpP
    have hsF := hfirst s q hpG hpF
    have hsG : s ∈ firstProjectionGeneric X.G := ⟨q, hpG⟩
    obtain ⟨_, hsx⟩ := (hgen s).mp hsG
    refine ⟨(levyContext κ hG).check s, ((levyContext κ hG).check_mem_iff _ _).mpr
      ((mem_decisionBelow_iff _ _).mpr ⟨hs, hsF⟩), ?_⟩
    have hsB : (levyContext κ hG).check s ∈ binarySequences (levyContext κ hG).Model := by
      rw [← hcheckB]
      exact ((levyContext κ hG).check_mem_iff _ _).mpr hs
    exact (subset_iff_restrict_eq hx.1 hsB).mp hsx
  · rintro ⟨s', hs', hxs⟩
    obtain ⟨s, hs, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hs'
    obtain ⟨hsB, hsF⟩ := (mem_decisionBelow_iff _ _).mp hs
    have hsB' : (levyContext κ hG).check s ∈ binarySequences (levyContext κ hG).Model := by
      rw [← hcheckB]
      exact ((levyContext κ hG).check_mem_iff _ _).mpr hsB
    have hsx : (levyContext κ hG).check s ⊆ x := (subset_iff_restrict_eq hx.1 hsB').mpr hxs
    obtain ⟨q, hsqG⟩ := (hgen s).mpr ⟨hsB, hsx⟩
    have hsqP : ⟨s, q⟩ₖ ∈ X.P := X.generic.1.1 _ hsqG
    rw [hXP] at hsqP
    obtain ⟨_, hq⟩ := kpair_mem_iff.mp hsqP
    refine ⟨⟨s, ∅⟩ₖ, X.generic.1.2.2.1 _ hsqG _ ?_ ?_, hsF⟩
    · rw [hXP]
      exact kpair_mem_iff.mpr ⟨hsB, hone₂⟩
    · rw [hXR]
      exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr
        ⟨hsB, hq, hsB, hone₂, hQ.2.1 s hsB, t₂.2 q hq⟩

include hAC hU hc hω hκ in
/-- Every set of reals of the Levy extension definable from ground parameters has the Baire
property. -/
theorem baireProperty_of_ground_definable {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (a : Fin n → V)
    {X : (levyContext κ hG).Model}
    (hX : ∀ x, x ∈ X ↔ x ∈ cantorSpace (levyContext κ hG).Model ∧
      φ.Evalb (x :> fun i ↦ (levyContext κ hG).check (a i))) :
    BaireProperty X := by
  obtain ⟨e, he, hdense, henum⟩ := levy_exists_dense_enumeration hAC hU hc hω hκ hG
  refine (levyContext κ hG).baireProperty_of_cohen_decision
    (S := (levyContext κ hG).check (cohenDecisionSet κ φ a)) (fun x hx ↦ ((hX x).mp hx).1) ?_ he hdense henum ?_
  · rw [← (levyContext κ hG).check_binarySequences]
    exact ((levyContext κ hG).checkEmbedding.subset_iff _ _).mpr (cohenDecisionSet_subset κ φ a)
  · intro x hx
    rw [hX x, ← cohen_decision hAC hU hc hω hκ hG φ a hx]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hx.1, h⟩⟩

end

end ZFVP
