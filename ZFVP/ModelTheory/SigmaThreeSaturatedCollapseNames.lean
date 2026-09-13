import ZFVP.ModelTheory.SigmaThreeSaturatedPrefixNames
import ZFVP.ModelTheory.SaturatedCollapseBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def saturatedCollapseNameGraphFormula (Λ : SetTheorySemisentence 5) : SetTheorySemisentence 6 :=
  “Q P R ζ κ δ. ∃ U, ∃ W, !sigmaTwoNameHierarchyFormula U P ζ ∧
    !Λ W P R κ δ ∧ !sigmaOneSaturatedNameFormula Q P R U W”

theorem saturatedCollapseNameGraphFormula_sigmaThree {Λ : SetTheorySemisentence 5}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (saturatedCollapseNameGraphFormula Λ) :=
  .exs (.exs (.and (sigmaTwoNameHierarchyFormula_sigmaTwo.raise.subst _)
    (.and (hΛ.subst _) ((sigmaOneSaturatedNameFormula_sigmaOne.mono (by omega)).subst _))))

theorem saturatedWoodinCollapseName_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 6, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ Q P R one ζ κ δ : V, IsForcingPreorder P R → IsForcingTop P R one → IsOrdinal ζ →
          IsForcingName P κ → IsForcingName P δ →
          (Λ.Evalb ![Q, P, R, ζ, κ, δ] ↔ Q = saturatedWoodinCollapseName P R ζ κ δ) := by
  obtain ⟨Λ, hΛ, he⟩ := woodinCollapseName_sigmaThree_uniform.{u}
  refine ⟨saturatedCollapseNameGraphFormula Λ, saturatedCollapseNameGraphFormula_sigmaThree hΛ, ?_⟩
  intro V _ _ _ Q P R one ζ κ δ hR ht hz hk hd
  have hb : (saturatedCollapseNameGraphFormula Λ).Evalb ![Q, P, R, ζ, κ, δ] ↔
      ∃ U W : V, (IsOrdinal ζ ∧ U = forcingNameHierarchy P ζ) ∧
        Λ.Evalb ![W, P, R, κ, δ] ∧ Q = forcingSaturatedName P R U W := by
    simp [saturatedCollapseNameGraphFormula, eval_sigmaTwoNameHierarchyFormula, eval_sigmaOneSaturatedNameFormula,
      Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  rw [hb]
  simp only [hz, true_and, he V _ P R one κ δ hR ht hk hd]
  simp [saturatedWoodinCollapseName]

theorem saturatedWoodinCollapseName_deltaThree_uniform :
    ∃ Λ Ξ : SetTheorySemisentence 6, IsSigmaFormula 3 Λ ∧ IsPiFormula 3 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ Q P R one ζ κ δ : V, IsForcingPreorder P R → IsForcingTop P R one → IsOrdinal ζ →
          IsForcingName P κ → IsForcingName P δ →
          (Λ.Evalb ![Q, P, R, ζ, κ, δ] ↔ Q = saturatedWoodinCollapseName P R ζ κ δ) ∧
          (Ξ.Evalb ![Q, P, R, ζ, κ, δ] ↔ Q = saturatedWoodinCollapseName P R ζ κ δ) := by
  obtain ⟨Λ, hΛ, he⟩ := saturatedWoodinCollapseName_sigmaThree_uniform.{u}
  refine ⟨Λ, prefixNamePiGraph Λ, hΛ, prefixNamePiGraph_piThree hΛ, ?_⟩
  intro W _ _ _ Q P R one ζ κ δ hR ht hz hk hd
  exact ⟨he W Q P R one ζ κ δ hR ht hz hk hd,
    eval_prefixNamePiGraph Λ Q P R ζ κ δ _ (fun S ↦ he W S P R one ζ κ δ hR ht hz hk hd)⟩

theorem saturatedWoodinCollapseOrderName_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 6, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ S P R one ζ κ δ : V, IsForcingPreorder P R → IsForcingTop P R one → IsOrdinal ζ →
          IsForcingName P κ → IsForcingName P δ →
          (Λ.Evalb ![S, P, R, ζ, κ, δ] ↔ S = reverseInclusionOrderName P R (saturatedWoodinCollapseName P R ζ κ δ)) := by
  obtain ⟨Λ, hΛ, he⟩ := saturatedWoodinCollapseName_sigmaThree_uniform.{u}
  obtain ⟨Ξ, _, hΞ, _, horder⟩ := reverseInclusionOrderName_deltaThree_uniform.{u}
  refine ⟨saturatedPrefixOrderGraphFormula Λ Ξ, saturatedPrefixOrderGraphFormula_sigmaThree hΛ hΞ, ?_⟩
  intro V _ _ _ S P R one ζ κ δ hR ht hz hk hd
  have hb : (saturatedPrefixOrderGraphFormula Λ Ξ).Evalb ![S, P, R, ζ, κ, δ] ↔
      ∃ Q : V, Λ.Evalb ![Q, P, R, ζ, κ, δ] ∧ Ξ.Evalb ![S, P, R, Q] := by
    simp [saturatedPrefixOrderGraphFormula, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb]
  simp only [he V _ P R one ζ κ δ hR ht hz hk hd]
  rw [exists_eq_left]
  exact (horder V S P R _ hR (forcingSaturatedName_isName _ _ _ _)).1

theorem saturatedWoodinCollapseOrderName_deltaThree_uniform :
    ∃ Λ Ξ : SetTheorySemisentence 6, IsSigmaFormula 3 Λ ∧ IsPiFormula 3 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ S P R one ζ κ δ : V, IsForcingPreorder P R → IsForcingTop P R one → IsOrdinal ζ →
          IsForcingName P κ → IsForcingName P δ →
          (Λ.Evalb ![S, P, R, ζ, κ, δ] ↔ S = reverseInclusionOrderName P R (saturatedWoodinCollapseName P R ζ κ δ)) ∧
          (Ξ.Evalb ![S, P, R, ζ, κ, δ] ↔ S = reverseInclusionOrderName P R (saturatedWoodinCollapseName P R ζ κ δ)) := by
  obtain ⟨Λ, hΛ, he⟩ := saturatedWoodinCollapseOrderName_sigmaThree_uniform.{u}
  refine ⟨Λ, prefixNamePiGraph Λ, hΛ, prefixNamePiGraph_piThree hΛ, ?_⟩
  intro W _ _ _ S P R one ζ κ δ hR ht hz hk hd
  exact ⟨he W S P R one ζ κ δ hR ht hz hk hd,
    eval_prefixNamePiGraph Λ S P R ζ κ δ _ (fun T ↦ he W T P R one ζ κ δ hR ht hz hk hd)⟩

end ZFVP
