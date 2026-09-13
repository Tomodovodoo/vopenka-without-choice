import ZFVP.ModelTheory.SchmerlInfinitaryClassSentence
import ZFVP.ModelTheory.SchmerlInfinitaryFunctionSentence
import ZFVP.ModelTheory.NoConservativeEndExtension

/-! A fixed countable language and one infinitary sentence whose ZF reducts
are dead ends. This proves the reduct direction; satisfiability and downward
forcing absoluteness remain separate construction theorems. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary (Formula)

universe u v

/-- Changing only the language does not change the meaning in its reduct. -/
def mapLanguage {L K : Language} (η : L →ᵥ K) :
    {n : ℕ} → Infinitary.Formula L n → Infinitary.Formula K n
  | _, .fo φ => .fo (φ.lMap η)
  | _, .neg φ => .neg (mapLanguage η φ)
  | _, .conj φ => .conj fun i ↦ mapLanguage η (φ i)
  | _, .exs φ => .exs (mapLanguage η φ)
  | _, .q φ => .q (mapLanguage η φ)

theorem eval_mapLanguage {L K : Language} (η : L →ᵥ K)
    {M : Type*} (S : Structure K M) {n : ℕ} (φ : Infinitary.Formula L n) (b : Fin n → M) :
    @Formula.Eval K M S n (mapLanguage η φ) b ↔
      @Formula.Eval L M (S.lMap η) n φ b := by
  induction φ with
  | fo φ => exact Semiformula.eval_lMap
  | neg φ ih => exact not_congr (ih b)
  | conj φ ih => exact forall_congr' fun i ↦ ih i b
  | exs φ ih => exact exists_congr fun x ↦ ih (x :> b)
  | q φ ih =>
    have he : {x : M | @Formula.Eval K M S _ (mapLanguage η φ) (x :> b)} =
        {x : M | @Formula.Eval L M (S.lMap η) _ φ (x :> b)} := by
      ext x
      exact ih (x :> b)
    change (¬ Set.Countable _) ↔ ¬ Set.Countable _
    rw [he]

/-- Two relation symbols uniformly name all selected domains and colors. -/
inductive FunctionExtraRelation : ℕ → Type where
  | selected : FunctionExtraRelation 2
  | color : FunctionExtraRelation 3

instance {n : ℕ} : Subsingleton (FunctionExtraRelation n) where
  allEq a b := by cases a <;> cases b <;> rfl

noncomputable instance {n : ℕ} : Encodable (FunctionExtraRelation n) :=
  Encodable.ofInj (fun _ ↦ ()) (fun _ _ _ ↦ Subsingleton.elim _ _)

def functionExtraLanguage : Language := ⟨fun _ ↦ Empty, FunctionExtraRelation⟩

noncomputable instance : functionExtraLanguage.Encodable :=
  ⟨fun _ ↦ inferInstanceAs (Encodable Empty),
    fun n ↦ inferInstanceAs (Encodable (FunctionExtraRelation n))⟩

def deadEndLanguage : Language := Language.add classLanguage functionExtraLanguage

noncomputable instance : deadEndLanguage.Encodable :=
  ⟨fun n ↦ inferInstanceAs (Encodable ((classLanguage.Func n) ⊕ Empty)),
    fun n ↦ inferInstanceAs (Encodable ((classLanguage.Rel n) ⊕ FunctionExtraRelation n))⟩

def deadEndClassEmbedding : classLanguage →ᵥ deadEndLanguage :=
  Language.Hom.add₁ classLanguage functionExtraLanguage

def deadEndSetEmbedding : ℒₛₑₜ →ᵥ deadEndLanguage :=
  deadEndClassEmbedding.comp classLanguageEmbedding

def functionSelected : Formula deadEndLanguage 2 :=
  .fo (.rel (Sum.inr FunctionExtraRelation.selected) (fun i ↦ .bvar i))

def functionColor : Formula deadEndLanguage 3 :=
  .fo (.rel (Sum.inr FunctionExtraRelation.color) (fun i ↦ .bvar i))

/-- No model, parameter enumeration, chosen tree, or coloring occurs in this
fixed syntax. All extra information is supplied by its interpretations. -/
noncomputable def deadEndSentence : Formula deadEndLanguage 0 :=
  .and (mapLanguage deadEndClassEmbedding classTreeSentence)
    (functionTreeFamilySentence deadEndSetEmbedding functionSelected functionColor)

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (S : Structure deadEndLanguage V)
  (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ V))
  (h : @Formula.Eval deadEndLanguage V S 0 deadEndSentence ![])

include hS h

/-- The fixed sentence itself supplies rather classlessness of the reduct. -/
theorem ratherClassless_of_deadEndSentence : IsRatherClassless V := by
  have hc := (Formula.eval_and _ _ _).mp h |>.1
  have he := (eval_mapLanguage deadEndClassEmbedding S classTreeSentence ![]).mp hc
  exact ratherClassless_of_classTreeSentence_model (S.lMap deadEndClassEmbedding) hS he

/-- Every ZF end extension of the reduct is conservative. -/
theorem conservative_of_deadEndSentence {W : Type v}
    [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (j : MembershipEndExtension V W) : j.IsConservative := by
  have hf := (Formula.eval_and _ _ _).mp h |>.2
  exact (ratherClassless_of_deadEndSentence S hS h).isConservative_of_isPowersetPreserving
    (powersetPreserving_of_functionTreeFamilySentence deadEndSetEmbedding S hS
      functionSelected functionColor j hf)

/-- Every standard model of the fixed sentence whose reduct satisfies ZF is
a ZF dead end, using the proved no-conservative-end-extension theorem. -/
theorem isZFDeadEnd_of_deadEndSentence : IsZFDeadEnd V := by
  intro W _ _ _ j
  exact no_conservative_proper_end_extension V W j (conservative_of_deadEndSentence S hS h j)

end ZFVP.Schmerl
