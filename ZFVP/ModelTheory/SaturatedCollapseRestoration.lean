import ZFVP.ModelTheory.NamedCollapseRestoration
import ZFVP.ModelTheory.SaturatedCollapseBounds
import ZFVP.SetTheory.SaturatedNameEquality
import ZFVP.SetTheory.ClassForcingCongruence
import ZFVP.SetTheory.WoodinNamedPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem forcingFormula_congr_names {P R p : V} (hR : IsForcingPreorder P R)
    {n : ℕ} (φ : SetTheorySemisentence n) (v w : Fin n → V) (hp : p ∈ P)
    (he : ∀ i, p ∈ atomicEquality P R (v i) (w i)) :
    p ∈ forcingFormula P R φ (standardTuple v) ↔ p ∈ forcingFormula P R φ (standardTuple w) :=
  classForcingFormula_congr hR (IsForcingName P) (by definability) φ v w hp he

theorem saturatedWoodinCollapseName_forces {P R one p ζ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P)
    (κ δ : ForcingName P)
    (hU : domain (woodinCollapseName P R κ.val δ.val) ⊆ forcingNameHierarchy P ζ) :
    p ∈ forcingFormula P R totalWoodinCollapseFormula
      (standardTuple ![saturatedWoodinCollapseName P R ζ κ.val δ.val, κ.val, δ.val]) := by
  have hh := forcingFormula_congr_names hR totalWoodinCollapseFormula
    ![saturatedWoodinCollapseName P R ζ κ.val δ.val, κ.val, δ.val]
    ![woodinCollapseName P R κ.val δ.val, κ.val, δ.val] hp (by
      intro i
      refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ Fin.elim0 l) k) j) i
      · exact forcingSaturatedName_atomicEquality hR (woodinCollapseName_isName _ _ _ _) hU hp
      · exact (atomicEquality_refl hR κ.val).symm ▸ hp
      · exact (atomicEquality_refl hR δ.val).symm ▸ hp)
  exact hh.mpr (woodinCollapseName_forces hR htop hp κ δ)

theorem woodinNamedPrefixCutoff_iff_saturated_forces {P R one γ δ ζ : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (κ : ForcingName P)
    (hz : (∅ : V) ∈ forcingNameHierarchy P ζ)
    (hU : domain (woodinCollapseName P R κ.val (checkName one δ)) ⊆ forcingNameHierarchy P ζ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![κ.val])) :
    IsWoodinNamedPrefixCutoff P R one γ κ.val δ ↔ γ ∈ δ ∧ IsChoicelessInaccessible δ ∧
      ∀ p ∈ twoStepConditions P R (saturatedWoodinCollapseName P R ζ κ.val (checkName one δ)) ∅,
        p ∈ forcingFormula
          (twoStepConditions P R (saturatedWoodinCollapseName P R ζ κ.val (checkName one δ)) ∅)
          (twoStepOrder P R (saturatedWoodinCollapseName P R ζ κ.val (checkName one δ))
            (reverseInclusionOrderName P R (saturatedWoodinCollapseName P R ζ κ.val (checkName one δ))) ∅)
          dependentChoiceBelowFormula (standardTuple ![checkName ⟨one, (∅ : V)⟩ₖ δ]) := by
  let cδ : ForcingName P := ⟨checkName one δ, checkName_isName htop.1 δ⟩
  let Q : ForcingName P := ⟨saturatedWoodinCollapseName P R ζ κ.val cδ.val,
    forcingSaturatedName_isName _ _ _ _⟩
  have hiter := saturatedWoodinCollapse_empty_iterand hR htop κ cδ hz hκ
    (fun _ hp ↦ forces_checked_ordinal hR htop inferInstance hp)
  have he := twoStep_checked_forcing (a := δ) hR htop hiter dependentChoiceBelowFormula
  have hl (p : V) (hp : p ∈ P) := woodinNamedCollapse_restoration_forcing_iff hR htop hp Q κ cδ
    (saturatedWoodinCollapseName_forces hR htop hp κ cδ hU)
    (forces_checked_ordinal hR htop (inferInstance : IsOrdinal δ) hp)
  constructor
  · intro h
    exact ⟨h.1, h.2.1, he.mp (fun p hp ↦ (hl p hp).mp (h.2.2 p hp))⟩
  · rintro ⟨hγδ, hδ, h⟩
    exact ⟨hγδ, hδ, fun p hp ↦ (hl p hp).mpr (he.mpr h p hp)⟩

end ZFVP
