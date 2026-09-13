import ZFVP.ModelTheory.SigmaThreeSaturatedCollapseNames
import ZFVP.ModelTheory.LevyHartogsName
import ZFVP.ModelTheory.SaturatedHartogsFormulas

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def checkedHartogsNameCertificate (Λ : SetTheorySemisentence 4) : SetTheorySemisentence 5 :=
  “N P R o γ. ∃ τ, !(sigmaOneCheckNameFormula true) o γ τ ∧ !Λ N P R τ”

theorem checkedHartogsNameCertificate_sigmaThree {Λ : SetTheorySemisentence 4}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (checkedHartogsNameCertificate Λ) :=
  .exs (.and (((sigmaOneCheckNameFormula_sigmaOne true).mono (by omega)).subst _) (hΛ.subst _))

def saturatedHartogsNameCertificate (Λ : SetTheorySemisentence 5) (Ξ : SetTheorySemisentence 6) :
    SetTheorySemisentence 6 :=
  “Q P R o γ δ. ∃ κ, !Λ κ P R o γ ∧ ∃ υ, !(sigmaOneCheckNameFormula true) o δ υ ∧ !Ξ Q P R δ κ υ”

theorem saturatedHartogsNameCertificate_sigmaThree {Λ : SetTheorySemisentence 5} {Ξ : SetTheorySemisentence 6}
    (hΛ : IsSigmaFormula 3 Λ) (hΞ : IsSigmaFormula 3 Ξ) :
    IsSigmaFormula 3 (saturatedHartogsNameCertificate Λ Ξ) :=
  .exs (.and (hΛ.subst _) (.exs (.and (((sigmaOneCheckNameFormula_sigmaOne true).mono (by omega)).subst _)
    (hΞ.subst _))))

theorem checkedHartogsName_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 5, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ N P R o γ : V, IsForcingPreorder P R → IsForcingTop P R o →
          (Λ.Evalb ![N, P, R, o, γ] ↔ N = hartogsNumberName P R (checkName o γ)) := by
  obtain ⟨Λ, hΛ, he⟩ := hartogsNumberName_sigmaThree_uniform.{u}
  refine ⟨checkedHartogsNameCertificate Λ, checkedHartogsNameCertificate_sigmaThree hΛ, ?_⟩
  intro V _ _ _ N P R o γ hR ht
  have hb : (checkedHartogsNameCertificate Λ).Evalb ![N, P, R, o, γ] ↔
      Λ.Evalb ![N, P, R, checkName o γ] := by
    simp [checkedHartogsNameCertificate, eval_sigmaOneCheckNameFormula, TruthAnswer,
      Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  exact hb.trans (he V N P R o _ hR ht (checkName_isName ht.1 γ))

theorem saturatedHartogsPosetName_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 6, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ Q P R o γ δ : V, IsForcingPreorder P R → IsForcingTop P R o → IsOrdinal δ →
          (Λ.Evalb ![Q, P, R, o, γ, δ] ↔ Q = saturatedHartogsPosetName P R o γ δ) := by
  obtain ⟨Λ, hΛ, heΛ⟩ := checkedHartogsName_sigmaThree_uniform.{u}
  obtain ⟨Ξ, hΞ, heΞ⟩ := saturatedWoodinCollapseName_sigmaThree_uniform.{u}
  refine ⟨saturatedHartogsNameCertificate Λ Ξ, saturatedHartogsNameCertificate_sigmaThree hΛ hΞ, ?_⟩
  intro V _ _ _ Q P R o γ δ hR ht hd
  have hb : (saturatedHartogsNameCertificate Λ Ξ).Evalb ![Q, P, R, o, γ, δ] ↔
      ∃ κ : V, Λ.Evalb ![κ, P, R, o, γ] ∧ Ξ.Evalb ![Q, P, R, δ, κ, checkName o δ] := by
    simp [saturatedHartogsNameCertificate, eval_sigmaOneCheckNameFormula, TruthAnswer,
      Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb]
  simp only [heΛ V _ P R o γ hR ht]
  rw [exists_eq_left]
  exact heΞ V Q P R o δ _ _ hR ht hd (hartogsNumberName_isName _ _ _) (checkName_isName ht.1 δ)

theorem saturatedHartogsOrderName_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 6, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ S P R o γ δ : V, IsForcingPreorder P R → IsForcingTop P R o → IsOrdinal δ →
          (Λ.Evalb ![S, P, R, o, γ, δ] ↔ S = saturatedHartogsOrderName P R o γ δ) := by
  obtain ⟨Λ, hΛ, heΛ⟩ := saturatedHartogsPosetName_sigmaThree_uniform.{u}
  obtain ⟨Ξ, _, hΞ, _, heΞ⟩ := reverseInclusionOrderName_deltaThree_uniform.{u}
  refine ⟨saturatedPrefixOrderGraphFormula Λ Ξ, saturatedPrefixOrderGraphFormula_sigmaThree hΛ hΞ, ?_⟩
  intro V _ _ _ S P R o γ δ hR ht hd
  have hb : (saturatedPrefixOrderGraphFormula Λ Ξ).Evalb ![S, P, R, o, γ, δ] ↔
      ∃ Q : V, Λ.Evalb ![Q, P, R, o, γ, δ] ∧ Ξ.Evalb ![S, P, R, Q] := by
    simp [saturatedPrefixOrderGraphFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb]
  simp only [heΛ V _ P R o γ δ hR ht hd]
  rw [exists_eq_left]
  exact (heΞ V S P R _ hR (forcingSaturatedName_isName _ _ _ _)).1

theorem saturatedHartogsPosetName_deltaThree_uniform :
    ∃ Λ Ξ : SetTheorySemisentence 6, IsSigmaFormula 3 Λ ∧ IsPiFormula 3 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ Q P R o γ δ : V, IsForcingPreorder P R → IsForcingTop P R o → IsOrdinal δ →
          (Λ.Evalb ![Q, P, R, o, γ, δ] ↔ Q = saturatedHartogsPosetName P R o γ δ) ∧
          (Ξ.Evalb ![Q, P, R, o, γ, δ] ↔ Q = saturatedHartogsPosetName P R o γ δ) := by
  obtain ⟨Λ, hΛ, he⟩ := saturatedHartogsPosetName_sigmaThree_uniform.{u}
  refine ⟨Λ, prefixNamePiGraph Λ, hΛ, prefixNamePiGraph_piThree hΛ, ?_⟩
  intro V _ _ _ Q P R o γ δ hR ht hd
  exact ⟨he V Q P R o γ δ hR ht hd,
    eval_prefixNamePiGraph Λ Q P R o γ δ _ (fun W ↦ he V W P R o γ δ hR ht hd)⟩

theorem saturatedHartogsOrderName_deltaThree_uniform :
    ∃ Λ Ξ : SetTheorySemisentence 6, IsSigmaFormula 3 Λ ∧ IsPiFormula 3 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ S P R o γ δ : V, IsForcingPreorder P R → IsForcingTop P R o → IsOrdinal δ →
          (Λ.Evalb ![S, P, R, o, γ, δ] ↔ S = saturatedHartogsOrderName P R o γ δ) ∧
          (Ξ.Evalb ![S, P, R, o, γ, δ] ↔ S = saturatedHartogsOrderName P R o γ δ) := by
  obtain ⟨Λ, hΛ, he⟩ := saturatedHartogsOrderName_sigmaThree_uniform.{u}
  refine ⟨Λ, prefixNamePiGraph Λ, hΛ, prefixNamePiGraph_piThree hΛ, ?_⟩
  intro V _ _ _ S P R o γ δ hR ht hd
  exact ⟨he V S P R o γ δ hR ht hd,
    eval_prefixNamePiGraph Λ S P R o γ δ _ (fun W ↦ he V W P R o γ δ hR ht hd)⟩

end ZFVP
