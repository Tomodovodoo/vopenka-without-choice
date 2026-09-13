import ZFVP.ModelTheory.SigmaThreeWoodinCollapseName
import ZFVP.SetTheory.SigmaTwoNameHierarchy
import ZFVP.SetTheory.DeltaOneCheckNames
import ZFVP.ModelTheory.SaturatedWoodinPrefix

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def checkedPrefixNameGraphFormula (Λ : SetTheorySemisentence 5) : SetTheorySemisentence 6 :=
  “Q P R one κ δ. ∃ τ, ∃ υ, !(sigmaOneCheckNameFormula true) one κ τ ∧
    !(sigmaOneCheckNameFormula true) one δ υ ∧ !Λ Q P R τ υ”

def saturatedPrefixNameGraphFormula (Λ : SetTheorySemisentence 6) : SetTheorySemisentence 6 :=
  “Q P R one κ δ. ∃ U, ∃ W, !sigmaTwoNameHierarchyFormula U P δ ∧
    !Λ W P R one κ δ ∧ !sigmaOneSaturatedNameFormula Q P R U W”

def saturatedPrefixOrderGraphFormula (Λ : SetTheorySemisentence 6) (Ξ : SetTheorySemisentence 4) :
    SetTheorySemisentence 6 :=
  “S P R one κ δ. ∃ Q, !Λ Q P R one κ δ ∧ !Ξ S P R Q”

def prefixNamePiGraph (Λ : SetTheorySemisentence 6) : SetTheorySemisentence 6 :=
  “Q P R one κ δ. ∀ W, !Λ W P R one κ δ → W = Q”

theorem checkedPrefixNameGraphFormula_sigmaThree {Λ : SetTheorySemisentence 5}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (checkedPrefixNameGraphFormula Λ) :=
  .exs (.exs (.and (((sigmaOneCheckNameFormula_sigmaOne true).mono (by omega)).subst _)
    (.and (((sigmaOneCheckNameFormula_sigmaOne true).mono (by omega)).subst _) (hΛ.subst _))))

theorem saturatedPrefixNameGraphFormula_sigmaThree {Λ : SetTheorySemisentence 6}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (saturatedPrefixNameGraphFormula Λ) :=
  .exs (.exs (.and (sigmaTwoNameHierarchyFormula_sigmaTwo.raise.subst _)
    (.and (hΛ.subst _) ((sigmaOneSaturatedNameFormula_sigmaOne.mono (by omega)).subst _))))

theorem saturatedPrefixOrderGraphFormula_sigmaThree {Λ : SetTheorySemisentence 6} {Ξ : SetTheorySemisentence 4}
    (hΛ : IsSigmaFormula 3 Λ) (hΞ : IsSigmaFormula 3 Ξ) :
    IsSigmaFormula 3 (saturatedPrefixOrderGraphFormula Λ Ξ) :=
  .exs (.and (hΛ.subst _) (hΞ.subst _))

theorem prefixNamePiGraph_piThree {Λ : SetTheorySemisentence 6} (hΛ : IsSigmaFormula 3 Λ) :
    IsPiFormula 3 (prefixNamePiGraph Λ) :=
  .all (.or (hΛ.subst _).neg (.bounded (.rel _ _)))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_checkedPrefixNameGraphFormula (Λ : SetTheorySemisentence 5) (Q P R one κ δ : V) :
    (checkedPrefixNameGraphFormula Λ).Evalb ![Q, P, R, one, κ, δ] ↔
      Λ.Evalb ![Q, P, R, checkName one κ, checkName one δ] := by
  simp [checkedPrefixNameGraphFormula, eval_sigmaOneCheckNameFormula, TruthAnswer,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

theorem woodinPrefixPosetName_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 6, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ Q P R one κ δ : V, IsForcingPreorder P R → IsForcingTop P R one →
          (Λ.Evalb ![Q, P, R, one, κ, δ] ↔ Q = woodinPrefixPosetName P R one κ δ) := by
  obtain ⟨Λ, hΛ, he⟩ := woodinCollapseName_sigmaThree_uniform.{u}
  refine ⟨checkedPrefixNameGraphFormula Λ, checkedPrefixNameGraphFormula_sigmaThree hΛ, ?_⟩
  intro V _ _ _ Q P R one κ δ hR ht
  rw [eval_checkedPrefixNameGraphFormula]
  exact he V Q P R one (checkName one κ) (checkName one δ) hR ht
    (checkName_isName ht.1 κ) (checkName_isName ht.1 δ)

theorem saturatedWoodinPrefixPosetName_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 6, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ Q P R one κ δ : V, IsForcingPreorder P R → IsForcingTop P R one → IsOrdinal δ →
          (Λ.Evalb ![Q, P, R, one, κ, δ] ↔ Q = saturatedWoodinPrefixPosetName P R one κ δ) := by
  obtain ⟨Λ, hΛ, he⟩ := woodinPrefixPosetName_sigmaThree_uniform.{u}
  refine ⟨saturatedPrefixNameGraphFormula Λ, saturatedPrefixNameGraphFormula_sigmaThree hΛ, ?_⟩
  intro V _ _ _ Q P R one κ δ hR ht hd
  have hb : (saturatedPrefixNameGraphFormula Λ).Evalb ![Q, P, R, one, κ, δ] ↔
      ∃ U W : V, (IsOrdinal δ ∧ U = forcingNameHierarchy P δ) ∧
        Λ.Evalb ![W, P, R, one, κ, δ] ∧ Q = forcingSaturatedName P R U W := by
    simp [saturatedPrefixNameGraphFormula, eval_sigmaTwoNameHierarchyFormula, eval_sigmaOneSaturatedNameFormula,
      Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  rw [hb]
  simp only [hd, true_and, he V _ P R one κ δ hR ht]
  simp [saturatedWoodinPrefixPosetName]

theorem saturatedWoodinPrefixOrderName_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 6, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ S P R one κ δ : V, IsForcingPreorder P R → IsForcingTop P R one → IsOrdinal δ →
          (Λ.Evalb ![S, P, R, one, κ, δ] ↔ S = saturatedWoodinPrefixOrderName P R one κ δ) := by
  obtain ⟨Λ, hΛ, he⟩ := saturatedWoodinPrefixPosetName_sigmaThree_uniform.{u}
  obtain ⟨Ξ, _, hΞ, _, horder⟩ := reverseInclusionOrderName_deltaThree_uniform.{u}
  refine ⟨saturatedPrefixOrderGraphFormula Λ Ξ, saturatedPrefixOrderGraphFormula_sigmaThree hΛ hΞ, ?_⟩
  intro V _ _ _ S P R one κ δ hR ht hd
  have hb : (saturatedPrefixOrderGraphFormula Λ Ξ).Evalb ![S, P, R, one, κ, δ] ↔
      ∃ Q : V, Λ.Evalb ![Q, P, R, one, κ, δ] ∧ Ξ.Evalb ![S, P, R, Q] := by
    simp [saturatedPrefixOrderGraphFormula, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb]
  simp only [he V _ P R one κ δ hR ht hd]
  rw [exists_eq_left]
  exact (horder V S P R _ hR (saturatedWoodinPrefixPosetName_isName P R one κ δ)).1

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_prefixNamePiGraph (Λ : SetTheorySemisentence 6) (Q P R one κ δ S : V)
    (he : ∀ W : V, Λ.Evalb ![W, P, R, one, κ, δ] ↔ W = S) :
    (prefixNamePiGraph Λ).Evalb ![Q, P, R, one, κ, δ] ↔ Q = S := by
  have hb : (prefixNamePiGraph Λ).Evalb ![Q, P, R, one, κ, δ] ↔
      ∀ W : V, Λ.Evalb ![W, P, R, one, κ, δ] → W = Q := by
    simp [prefixNamePiGraph, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb]
  simp only [he]
  simp [eq_comm]

theorem saturatedWoodinPrefixPosetName_deltaThree_uniform :
    ∃ Λ Ξ : SetTheorySemisentence 6, IsSigmaFormula 3 Λ ∧ IsPiFormula 3 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ Q P R one κ δ : V, IsForcingPreorder P R → IsForcingTop P R one → IsOrdinal δ →
          (Λ.Evalb ![Q, P, R, one, κ, δ] ↔ Q = saturatedWoodinPrefixPosetName P R one κ δ) ∧
          (Ξ.Evalb ![Q, P, R, one, κ, δ] ↔ Q = saturatedWoodinPrefixPosetName P R one κ δ) := by
  obtain ⟨Λ, hΛ, he⟩ := saturatedWoodinPrefixPosetName_sigmaThree_uniform.{u}
  refine ⟨Λ, prefixNamePiGraph Λ, hΛ, prefixNamePiGraph_piThree hΛ, ?_⟩
  intro W _ _ _ Q P R one κ δ hR ht hd
  exact ⟨he W Q P R one κ δ hR ht hd,
    eval_prefixNamePiGraph Λ Q P R one κ δ _ (fun S ↦ he W S P R one κ δ hR ht hd)⟩

theorem saturatedWoodinPrefixOrderName_deltaThree_uniform :
    ∃ Λ Ξ : SetTheorySemisentence 6, IsSigmaFormula 3 Λ ∧ IsPiFormula 3 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ S P R one κ δ : V, IsForcingPreorder P R → IsForcingTop P R one → IsOrdinal δ →
          (Λ.Evalb ![S, P, R, one, κ, δ] ↔ S = saturatedWoodinPrefixOrderName P R one κ δ) ∧
          (Ξ.Evalb ![S, P, R, one, κ, δ] ↔ S = saturatedWoodinPrefixOrderName P R one κ δ) := by
  obtain ⟨Λ, hΛ, he⟩ := saturatedWoodinPrefixOrderName_sigmaThree_uniform.{u}
  refine ⟨Λ, prefixNamePiGraph Λ, hΛ, prefixNamePiGraph_piThree hΛ, ?_⟩
  intro W _ _ _ S P R one κ δ hR ht hd
  exact ⟨he W S P R one κ δ hR ht hd,
    eval_prefixNamePiGraph Λ S P R one κ δ _ (fun T ↦ he W T P R one κ δ hR ht hd)⟩

end ZFVP

