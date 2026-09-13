import ZFVP.Syntax.MembershipTailTemplates
import ZFVP.ModelTheory.InternalZFModel

/-! Separation and Replacement codes with any internal number of parameters. -/

namespace ZFVP

set_option maxHeartbeats 400000

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def MembershipTemplate.iff {a n : ℕ} (s t : MembershipTemplate a n) : MembershipTemplate a n :=
  .conj (.imp s t) (.imp t s)

theorem MembershipTemplate.eval_iff {a n : ℕ} {W : Type*} [SetStructure W]
    (s t : MembershipTemplate a n) (P : (Fin a → W) → Prop) (b : Fin n → W) :
    (s.iff t).Eval P b ↔ (s.Eval P b ↔ t.Eval P b) := by
  classical
  simp only [MembershipTemplate.iff, MembershipTemplate.imp, MembershipTemplate.Eval,
    ← imp_iff_not_or, iff_def]

theorem MembershipTemplate.eval_imp {a n : ℕ} {W : Type*} [SetStructure W]
    (s t : MembershipTemplate a n) (P : (Fin a → W) → Prop) (b : Fin n → W) :
    (s.imp t).Eval P b ↔ (s.Eval P b → t.Eval P b) := by
  classical
  simp only [MembershipTemplate.imp, MembershipTemplate.Eval, imp_iff_not_or]

def separationTemplate : MembershipTemplate 1 0 :=
  .all (.exs (.all (.iff (.fixed “x c a. x ∈ c”)
    (.conj (.fixed “x c a. x ∈ a”) (.hole ![0])))))

def replacementTemplate : MembershipTemplate 2 0 :=
  .all (.imp
    (.all (.imp (.fixed “x a. x ∈ a”)
      (.exs (.conj (.hole ![1, 0])
        (.all (.imp (.hole ![2, 0]) (.fixed “z y x a. z = y”)))))))
    (.exs (.all (.iff (.fixed “y c a. y ∈ c”)
      (.exs (.conj (.fixed “x y c a. x ∈ a”) (.hole ![0, 1])))))))

theorem eval_separationTemplate {W : Type*} [SetStructure W] (P : (Fin 1 → W) → Prop) :
    separationTemplate.Eval P ![] ↔ ∀ a : W, ∃ c : W, ∀ x : W, (x ∈ c ↔ x ∈ a ∧ P ![x]) := by
  simp [separationTemplate, MembershipTemplate.eval_iff, MembershipTemplate.Eval,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton, Semiformula.Evalb]

theorem eval_replacementTemplate {W : Type*} [SetStructure W] (P : (Fin 2 → W) → Prop) :
    replacementTemplate.Eval P ![] ↔
      ∀ a : W, (∀ x : W, x ∈ a → ∃! y : W, P ![x, y]) →
        ∃ c : W, ∀ y : W, (y ∈ c ↔ ∃ x : W, x ∈ a ∧ P ![x, y]) := by
  classical
  simp [replacementTemplate, MembershipTemplate.eval_iff, MembershipTemplate.eval_imp, MembershipTemplate.Eval,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton, Semiformula.Evalb,
    ExistsUnique]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def separationCode (n φ : V) : V := separationTemplate.compileTail n φ

noncomputable def replacementCode (n φ : V) : V := replacementTemplate.compileTail n φ

theorem separationCode_valid {n φ : V} (hn : n ∈ (ω : V)) (hφ : IsMembershipFormulaCode (succ n) φ) :
    IsMembershipFormulaCode n (separationCode n φ) := by
  apply (mem_formulaSet_iff membershipLanguageCode ∅ n (separationCode n φ)).mp
  exact separationTemplate.compileTail_valid (a := 1) (m := 0) (n := n) (φ := φ) hn hφ.valid

theorem replacementCode_valid {n φ : V} (hn : n ∈ (ω : V)) (hφ : IsMembershipFormulaCode (succ (succ n)) φ) :
    IsMembershipFormulaCode n (replacementCode n φ) := by
  apply (mem_formulaSet_iff membershipLanguageCode ∅ n (replacementCode n φ)).mp
  exact replacementTemplate.compileTail_valid (a := 2) (m := 0) (n := n) (φ := φ) hn hφ.valid

theorem separationCode_satisfies {U n φ b : V} (hU : IsNonempty U) (hn : n ∈ (ω : V))
    (hφ : IsMembershipFormulaCode (succ n) φ) (hb : b ∈ U ^ n) :
    MembershipSatisfies U n (separationCode n φ) b ↔
      ∀ a : SetDomain U, ∃ c : SetDomain U, ∀ x : SetDomain U,
        (x ∈ c ↔ x ∈ a ∧ MembershipSatisfies U (succ n) φ (assignmentPrepend n b x.val)) := by
  have he := separationTemplate.compileTail_satisfies (a := 1) (m := 0) (n := n) (φ := φ) hU hn hφ.valid hb (![] : Fin 0 → SetDomain U)
  have ht := eval_separationTemplate
    (fun w : Fin 1 → SetDomain U ↦ MembershipSatisfies U (prefixSize 1 n) φ (prependTuple n b (fun i ↦ (w i).val)))
  exact he.trans (by simpa only [prefixSize, prependTuple, Matrix.cons_val_zero] using ht)

theorem replacementCode_satisfies {U n φ b : V} (hU : IsNonempty U) (hn : n ∈ (ω : V))
    (hφ : IsMembershipFormulaCode (succ (succ n)) φ) (hb : b ∈ U ^ n) :
    MembershipSatisfies U n (replacementCode n φ) b ↔
      ∀ a : SetDomain U, (∀ x : SetDomain U, x ∈ a → ∃! y : SetDomain U,
        MembershipSatisfies U (succ (succ n)) φ (assignmentPrepend (succ n) (assignmentPrepend n b y.val) x.val)) →
        ∃ c : SetDomain U, ∀ y : SetDomain U, (y ∈ c ↔ ∃ x : SetDomain U, x ∈ a ∧
          MembershipSatisfies U (succ (succ n)) φ (assignmentPrepend (succ n) (assignmentPrepend n b y.val) x.val)) := by
  have he := replacementTemplate.compileTail_satisfies (a := 2) (m := 0) (n := n) (φ := φ) hU hn hφ.valid hb (![] : Fin 0 → SetDomain U)
  have ht := eval_replacementTemplate
    (fun w : Fin 2 → SetDomain U ↦ MembershipSatisfies U (prefixSize 2 n) φ (prependTuple n b (fun i ↦ (w i).val)))
  exact he.trans (by simpa only [prefixSize, prependTuple, Matrix.cons_val_zero, Matrix.cons_val_succ] using ht)

theorem InternalSeparation.satisfies_code {U : V} (hsep : InternalSeparation U) (hU : IsNonempty U)
    {n φ b : V} (hn : n ∈ (ω : V)) (hφ : IsMembershipFormulaCode (succ n) φ) (hb : b ∈ U ^ n) :
    MembershipSatisfies U n (separationCode n φ) b := by
  apply (separationCode_satisfies hU hn hφ hb).mpr
  intro a
  obtain ⟨c, hc, hh⟩ := hsep n hn φ hφ b hb a.val a.property
  exact ⟨⟨c, hc⟩, fun x ↦ hh x.val x.property⟩

theorem InternalReplacement.satisfies_code {U : V} (hrepl : InternalReplacement U) (hU : IsNonempty U)
    {n φ b : V} (hn : n ∈ (ω : V)) (hφ : IsMembershipFormulaCode (succ (succ n)) φ) (hb : b ∈ U ^ n) :
    MembershipSatisfies U n (replacementCode n φ) b := by
  apply (replacementCode_satisfies hU hn hφ hb).mpr
  intro a hh
  have hh' : ∀ x ∈ U, x ∈ a.val → ∃! y : V, y ∈ U ∧
      MembershipSatisfies U (succ (succ n)) φ (assignmentPrepend (succ n) (assignmentPrepend n b y) x) := by
    intro x hx hxa
    obtain ⟨y, hy, huniq⟩ := hh ⟨x, hx⟩ hxa
    refine ⟨y.val, ⟨y.property, hy⟩, ?_⟩
    intro z hz
    exact congrArg Subtype.val (huniq ⟨z, hz.1⟩ hz.2)
  obtain ⟨c, hc, hmem⟩ := hrepl n hn φ hφ b hb a.val a.property hh'
  refine ⟨⟨c, hc⟩, fun y ↦ ?_⟩
  constructor
  · intro hy
    obtain ⟨x, hx, hxa, hp⟩ := (hmem y.val y.property).mp hy
    exact ⟨⟨x, hx⟩, hxa, hp⟩
  · rintro ⟨x, hxa, hp⟩
    exact (hmem y.val y.property).mpr ⟨x.val, x.property, hxa, hp⟩

theorem internalSeparation_iff_satisfies_codes {U : V} (hU : IsNonempty U) :
    InternalSeparation U ↔ ∀ n ∈ (ω : V), ∀ φ, IsMembershipFormulaCode (succ n) φ →
      ∀ b ∈ U ^ n, MembershipSatisfies U n (separationCode n φ) b := by
  constructor
  · intro h n hn φ hφ b hb
    exact h.satisfies_code hU hn hφ hb
  · intro h n hn φ hφ b hb a ha
    obtain ⟨c, hc⟩ := (separationCode_satisfies hU hn hφ hb).mp (h n hn φ hφ b hb) ⟨a, ha⟩
    exact ⟨c.val, c.property, fun x hx ↦ hc ⟨x, hx⟩⟩

theorem internalReplacement_iff_satisfies_codes {U : V} (hU : IsNonempty U) :
    InternalReplacement U ↔ ∀ n ∈ (ω : V), ∀ φ, IsMembershipFormulaCode (succ (succ n)) φ →
      ∀ b ∈ U ^ n, MembershipSatisfies U n (replacementCode n φ) b := by
  constructor
  · intro h n hn φ hφ b hb
    exact h.satisfies_code hU hn hφ hb
  · intro h n hn φ hφ b hb a ha hfun
    have hfun' : ∀ x : SetDomain U, x.val ∈ a → ∃! y : SetDomain U,
        MembershipSatisfies U (succ (succ n)) φ (assignmentPrepend (succ n) (assignmentPrepend n b y.val) x.val) := by
      intro x hx
      obtain ⟨y, hy, huniq⟩ := hfun x.val x.property hx
      refine ⟨⟨y, hy.1⟩, hy.2, ?_⟩
      intro z hz
      exact Subtype.ext (huniq z.val ⟨z.property, hz⟩)
    obtain ⟨c, hc⟩ := (replacementCode_satisfies hU hn hφ hb).mp (h n hn φ hφ b hb) ⟨a, ha⟩ hfun'
    refine ⟨c.val, c.property, fun y hy ↦ ?_⟩
    constructor
    · intro hym
      obtain ⟨x, hxa, hp⟩ := (hc ⟨y, hy⟩).mp hym
      exact ⟨x.val, x.property, hxa, hp⟩
    · rintro ⟨x, hx, hxa, hp⟩
      exact (hc ⟨y, hy⟩).mpr ⟨⟨x, hx⟩, hxa, hp⟩

end ZFVP
