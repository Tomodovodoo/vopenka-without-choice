import ZFVP.Syntax.MembershipTemplates
import ZFVP.ModelTheory.LocalCodedVopenka

/-! A sentence-code compiler and its semantics for all internal Vopenka instances. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def vopenkaTemplateWith (S : SetTheorySemisentence 2) (E : SetTheorySemisentence 4) : MembershipTemplate 2 0 :=
  .all (.all (.imp
    (.all (.exs (.conj (.hole ![0, 2]) (.fixed “M A a L. M ∉ A”))))
    (.imp
      (.all (.imp (.hole ![0, 1]) (.fixed “M a L. !S L M”)))
      (.exs (.exs (.exs (.conj (.fixed “e N M a L. M ≠ N”)
        (.conj (.hole ![2, 3]) (.conj (.hole ![1, 3])
          (.fixed “e N M a L. !E L M N e”))))))))))

theorem eval_vopenkaTemplateWith {W : Type*} [SetStructure W]
    (S : SetTheorySemisentence 2) (E : SetTheorySemisentence 4) (P : (Fin 2 → W) → Prop) :
    (vopenkaTemplateWith S E).Eval P ![] ↔
      ∀ L a : W, (∀ A : W, ∃ M : W, P ![M, a] ∧ M ∉ A) →
        (∀ M : W, P ![M, a] → S.Evalb ![L, M]) →
        ∃ M N e : W, M ≠ N ∧ P ![M, a] ∧ P ![N, a] ∧
          E.Evalb ![L, M, N, e] := by
  classical
  simp [vopenkaTemplateWith, MembershipTemplate.Eval, MembershipTemplate.imp,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    Semiformula.Evalb, imp_iff_not_or]

def vopenkaTemplate : MembershipTemplate 2 0 :=
  vopenkaTemplateWith isStructureCodeFormula codedElementaryEmbeddingFormula

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def vopenkaCode (φ : V) : V := vopenkaTemplate.compile φ

theorem vopenkaCode_valid {φ : V} (hφ : IsMembershipFormulaCode (2 : V) φ) :
    IsMembershipFormulaCode (0 : V) (vopenkaCode φ) :=
  (mem_formulaSet_iff _ _ _ _).mp (vopenkaTemplate.compile_valid hφ.valid)

theorem vopenkaCode_satisfies {U φ : V} (hU : IsNonempty U)
    (hφ : IsMembershipFormulaCode (2 : V) φ) :
    MembershipSatisfies U 0 (vopenkaCode φ) ∅ ↔ LocalCodedVopenka U φ := by
  have he := vopenkaTemplate.compile_satisfies hU hφ.valid (![] : Fin 0 → SetDomain U)
  have htwo : ((2 : ℕ) : V) = (2 : V) := rfl
  rw [htwo] at he
  have hv (M a : SetDomain U) : (fun i : Fin 2 ↦ (![M, a] i).val) = ![M.val, a.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) j) i
  have ht := eval_vopenkaTemplateWith isStructureCodeFormula codedElementaryEmbeddingFormula
    (fun v : Fin 2 → SetDomain U ↦ MembershipSatisfies U (2 : V) φ (standardTuple (fun i ↦ (v i).val)))
  exact he.trans (by simpa only [vopenkaTemplate, LocalCodedVopenka, hv] using ht)

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem limit_vopenkaCode (hlim : criticalLimit f κ ∈ hierarchy δ)
    {φ : V} (hφ : IsMembershipFormulaCode (2 : V) φ) :
    MembershipSatisfies (hierarchy (criticalLimit f κ)) 0 (vopenkaCode φ) ∅ := by
  let := limit_ordinal hδ h hκ
  apply (vopenkaCode_satisfies ⟨ω, ordinal_subset_hierarchy _ _ (omega_mem_limit hδ h hκ)⟩ hφ).mpr
  exact limit_localCodedVopenka hδ h hκ hlim hφ

end CriticalSequence

end ZFVP
