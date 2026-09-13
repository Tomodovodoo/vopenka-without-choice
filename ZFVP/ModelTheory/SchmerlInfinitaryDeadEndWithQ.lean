import ZFVP.ModelTheory.SchmerlInfinitaryFunctionWithQ
import ZFVP.ModelTheory.SchmerlInfinitarySmallDeadEnd

/-! Assemble the fixed sentences with an arbitrary extensional Q. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary (Formula)

theorem evalWithQ_mapLanguage {L K : Language} (η : L →ᵥ K)
    {M : Type*} (S : Structure K M) (Q : Set M → Prop)
    {n : ℕ} (φ : Infinitary.Formula L n) (b : Fin n → M) :
    @Formula.EvalWithQ K M S Q n (mapLanguage η φ) b ↔
      @Formula.EvalWithQ L M (S.lMap η) Q n φ b := by
  induction φ with
  | fo φ => exact Semiformula.eval_lMap
  | neg φ ih => exact not_congr (ih b)
  | conj φ ih => exact forall_congr' fun i ↦ ih i b
  | exs φ ih => exact exists_congr fun x ↦ ih (x :> b)
  | q φ ih =>
    have he : {x : M | @Formula.EvalWithQ K M S Q _ (mapLanguage η φ) (x :> b)} =
        {x : M | @Formula.EvalWithQ L M (S.lMap η) Q _ φ (x :> b)} := by
      ext x
      exact ih (x :> b)
    change Q _ ↔ Q _
    rw [he]

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem deadEndSentence_of_clausesWithQ
    (Dc : W → Prop) (fc : W → W) (Ds : W → W → Prop) (fs : W → W → W)
    (Q : Set W → Prop)
    (hclass : @Formula.EvalWithQ classLanguage W (classExpansion Dc fc) Q 0 classTreeSentence ![])
    (hfunctions : ∀ s : W, IsInternallyInfinite s →
      @Formula.EvalWithQ deadEndLanguage W (deadEndExpansion Dc fc Ds fs) Q 1
        (functionTreeDataClause deadEndSetEmbedding functionSelected functionColor) ![s]) :
    @Formula.EvalWithQ deadEndLanguage W (deadEndExpansion Dc fc Ds fs) Q 0 deadEndSentence ![] := by
  let : Structure deadEndLanguage W := deadEndExpansion Dc fc Ds fs
  apply (Formula.evalWithQ_and Q _ _ _).mpr
  refine ⟨?_, ?_⟩
  · apply (evalWithQ_mapLanguage deadEndClassEmbedding (deadEndExpansion Dc fc Ds fs) Q _ _).mpr
    exact hclass
  · exact (evalWithQ_functionTreeFamilySentence deadEndSetEmbedding
      (deadEndExpansion Dc fc Ds fs) rfl Q functionSelected functionColor).mpr hfunctions

theorem weaklyRubinSentence_of_clausesWithQ
    (Dc : W → Prop) (fc : W → W) (Ds : W → W → Prop) (fs : W → W → W)
    (Q : Set W → Prop)
    (hclass : @Formula.EvalWithQ classLanguage W (classExpansion Dc fc) Q 0 classTreeSentence ![])
    (hfunctions : ∀ s : W, IsInternallyInfinite s →
      @Formula.EvalWithQ deadEndLanguage W (deadEndExpansion Dc fc Ds fs) Q 1
        (functionTreeDataClause deadEndSetEmbedding functionSelected functionColor) ![s])
    (hsmall : ∀ a : W, IsInternallyFinite a → ¬Q {x | x ∈ a}) :
    @Formula.EvalWithQ deadEndLanguage W (deadEndExpansion Dc fc Ds fs) Q 0 weaklyRubinSentence ![] := by
  let : Structure deadEndLanguage W := deadEndExpansion Dc fc Ds fs
  apply (Formula.evalWithQ_and Q _ _ _).mpr
  exact ⟨deadEndSentence_of_clausesWithQ Dc fc Ds fs Q hclass hfunctions,
    (evalWithQ_finiteSmallSentence (deadEndExpansion Dc fc Ds fs) rfl Q).mpr hsmall⟩

theorem qFree_originalTheorySentence (T : Theory ℒₛₑₜ) :
    Formula.QFree (originalTheorySentence T) := by
  classical
  intro n
  dsimp only
  split_ifs <;> trivial

omit [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem evalWithQ_originalTheorySentence (S : Structure deadEndLanguage W)
    (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ W))
    (Q : Set W → Prop) (T : Theory ℒₛₑₜ) :
    @Formula.EvalWithQ deadEndLanguage W S Q 0 (originalTheorySentence T) ![] ↔ W↓[ℒₛₑₜ] ⊧* T :=
  ((qFree_originalTheorySentence T).evalWithQ_iff Q ![]).trans (eval_originalTheorySentence S hS T)

end ZFVP.Schmerl
