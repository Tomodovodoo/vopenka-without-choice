import ZFVP.ModelTheory.SplittingName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- A name followed by one checked parameter. -/
def splittingNamedCheckedFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 6 :=
  f“P R o t p a. !(ordinaryForcingTranslation φ) P R P P p
    (!assignmentPrependFormula (!(numeralFormula 1))
      (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) (!checkNameFormula o a)) t)”

def splittingCheckedMemberFormula : SetTheorySemisentence 6 :=
  f“P R o t p a. !(ordinaryForcingTranslation memberFormula) P R P P p
    (!assignmentPrependFormula (!(numeralFormula 1))
      (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) t) (!checkNameFormula o a))”

def splittingDecidedFormula : SetTheorySemisentence 6 :=
  f“P R o t p z. ∃ m ∈ !isω, ∃ i ∈ !(numeralFormula 2), z = !kpair.dfn m i ∧
    !splittingCheckedMemberFormula P R o t p (!kpair.dfn m i) ∧
    ∀ m' ∈ m, ∃ i' ∈ !(numeralFormula 2),
      !splittingCheckedMemberFormula P R o t p (!kpair.dfn m' i')”

def splittingSegmentFormula : SetTheorySemisentence 6 :=
  f“d P R o t p. ∀ z, z ∈ d ↔ z ∈ !prod.dfn (!isω) (!(numeralFormula 2)) ∧
    !splittingDecidedFormula P R o t p z”

def splittingLawsFormula : SetTheorySemisentence 5 :=
  f“P R o t p₀. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingNameFormula P t ∧ p₀ ∈ P ∧
    !(splittingNamedCheckedFormula newRealFormula) P R o t p₀ (!cantorSpaceFormula) →
    (∀ n ∈ !isω, ∀ q ∈ P, !kpair.dfn q p₀ ∈ R →
      ∃ r ∈ P, !kpair.dfn r q ∈ R ∧ ∀ m ∈ !succ.dfn n,
        ∃ i ∈ !(numeralFormula 2), !splittingCheckedMemberFormula P R o t r (!kpair.dfn m i)) ∧
    (∀ p ∈ P, !kpair.dfn p p₀ ∈ R → !splittingSegmentFormula P R o t p ∈ !binarySequencesFormula) ∧
    (∀ p ∈ P, !kpair.dfn p p₀ ∈ R → ∃ q ∈ P, ∃ q' ∈ P,
      !kpair.dfn q p ∈ R ∧ !kpair.dfn q' p ∈ R ∧
      !incompatibleFormula (!splittingSegmentFormula P R o t q) (!splittingSegmentFormula P R o t q'))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem splitting_forall_eq3 {α : Type*} (a₀ b₀ c₀ : α) (R : α → α → α → Prop) :
    (∀ a b c, a = a₀ → b = b₀ → c = c₀ → R a b c) ↔ R a₀ b₀ c₀ := by
  constructor
  · intro h
    exact h a₀ b₀ c₀ rfl rfl rfl
  · rintro h a b c rfl rfl rfl
    exact h

private theorem splitting_forall_eq5 {α : Type*} (a₀ b₀ c₀ d₀ e₀ : α) (R : α → α → α → α → α → Prop) :
    (∀ a b c d e, a = a₀ → b = b₀ → c = c₀ → d = d₀ → e = e₀ → R a b c d e) ↔ R a₀ b₀ c₀ d₀ e₀ := by
  constructor
  · intro h
    exact h a₀ b₀ c₀ d₀ e₀ rfl rfl rfl rfl rfl
  · rintro h a b c d e rfl rfl rfl rfl rfl
    exact h

private theorem splitting_forall_eq6 {α : Type*} (a₀ b₀ c₀ d₀ e₀ f₀ : α) (R : α → α → α → α → α → α → Prop) :
    (∀ a b c d e f, a = a₀ → b = b₀ → c = c₀ → d = d₀ → e = e₀ → f = f₀ → R a b c d e f) ↔ R a₀ b₀ c₀ d₀ e₀ f₀ := by
  constructor
  · intro h
    exact h a₀ b₀ c₀ d₀ e₀ f₀ rfl rfl rfl rfl rfl rfl
  · rintro h a b c d e f rfl rfl rfl rfl rfl rfl
    exact h

attribute [local simp] splitting_forall_eq3 splitting_forall_eq5 splitting_forall_eq6

instance splittingNamedCheckedFormula_defined (φ : SetTheorySemisentence 2) :
    Defined (fun v : Fin 6 → V ↦ v 4 ∈ forcingFormula (v 0) (v 1) φ
      (standardTuple ![v 3, checkName (v 2) (v 5)])) (splittingNamedCheckedFormula φ) :=
  ⟨fun v ↦ by simp [splittingNamedCheckedFormula, standardTuple, Semiformula.eval_nestFormulae,
    Semiformula.eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]⟩

instance splittingCheckedMemberFormula_defined :
    Defined (fun v : Fin 6 → V ↦ ForcesCheckedMember (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
      splittingCheckedMemberFormula :=
  ⟨fun v ↦ by simp [splittingCheckedMemberFormula, ForcesCheckedMember, standardTuple, Semiformula.eval_nestFormulae,
    Semiformula.eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]⟩

instance splittingDecidedFormula_defined :
    Defined (fun v : Fin 6 → V ↦ IsDecided (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) splittingDecidedFormula :=
  ⟨fun v ↦ by simp [splittingDecidedFormula, IsDecided, Semiformula.eval_nestFormulae,
    Semiformula.eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]⟩

instance splittingSegmentFormula_defined :
    Defined (fun v : Fin 6 → V ↦ v 0 = decidedSegment (v 1) (v 2) (v 3) (v 4) (v 5)) splittingSegmentFormula :=
  ⟨fun v ↦ by simp [splittingSegmentFormula, mem_ext_iff (y := decidedSegment _ _ _ _ _), mem_decidedSegment_iff, Semiformula.eval_nestFormulae,
    Semiformula.eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]⟩

def SplittingLaws (P R one τ p₀ : V) : Prop :=
  (∀ n ∈ (ω : V), ∀ q ∈ P, ⟨q, p₀⟩ₖ ∈ R →
    ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ DecidesBelow P R one τ n r) ∧
  (∀ p ∈ P, ⟨p, p₀⟩ₖ ∈ R → decidedSegment P R one τ p ∈ binarySequences V) ∧
  (∀ p ∈ P, ⟨p, p₀⟩ₖ ∈ R → ∃ q ∈ P, ∃ q' ∈ P,
    ⟨q, p⟩ₖ ∈ R ∧ ⟨q', p⟩ₖ ∈ R ∧
    Incompatible (decidedSegment P R one τ q) (decidedSegment P R one τ q'))

theorem eval_splittingLawsFormula (v : Fin 5 → V) :
    splittingLawsFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        IsForcingName (v 0) (v 3) → v 4 ∈ v 0 →
        v 4 ∈ forcingFormula (v 0) (v 1) newRealFormula
          (standardTuple ![v 3, checkName (v 2) (cantorSpace V)]) →
        SplittingLaws (v 0) (v 1) (v 2) (v 3) (v 4)) := by
  simp [splittingLawsFormula, SplittingLaws, DecidesBelow, Semiformula.eval_nestFormulae,
    Semiformula.eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]

/-- The countable-model argument establishes a single first-order law of ZF; a countable
elementary hull containing the five parameters transfers that law to every ground. -/
theorem splittingLaws_unrestricted {P R one τ p₀ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hτ : IsForcingName P τ)
    (hp₀ : p₀ ∈ P)
    (hnew : p₀ ∈ forcingFormula P R newRealFormula (standardTuple ![τ, checkName one (cantorSpace V)])) :
    SplittingLaws P R one τ p₀ := by
  have h := eval_of_countable_zf splittingLawsFormula (by
    intro W _ _ _ _ v
    apply (eval_splittingLawsFormula v).mpr
    intro hR ht hτ hp hn
    refine ⟨?_, ?_, ?_⟩
    · intro n hn' q hq hqp
      obtain ⟨r, hr, hrq⟩ := decider_dense hR ht hτ hp hn n hn' q hq hqp
      exact ⟨r, (mem_deciderSet_iff _ _ _ _ _ _).mp hr |>.1, hrq,
        (mem_deciderSet_iff _ _ _ _ _ _).mp hr |>.2⟩
    · exact fun p hp' hpp ↦ decidedSegment_mem_binarySequences hR ht hτ hp hn hp' hpp
    · exact fun p hp' hpp ↦ decidedSegment_split hR ht hτ hp hn hp' hpp) ![P, R, one, τ, p₀]
  exact (eval_splittingLawsFormula _).mp h hR htop hτ hp₀ hnew

section
variable {P R one τ p₀ : V}
  (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hτ : IsForcingName P τ)
  (hp₀ : p₀ ∈ P)
  (hnew : p₀ ∈ forcingFormula P R newRealFormula (standardTuple ![τ, checkName one (cantorSpace V)]))

include hR htop hτ hp₀ hnew in
theorem decider_dense_unrestricted (n : V) (hn : n ∈ (ω : V)) :
    ∀ q ∈ P, ⟨q, p₀⟩ₖ ∈ R → ∃ r ∈ deciderSet P R one τ n, ⟨r, q⟩ₖ ∈ R := by
  intro q hq hqp
  obtain ⟨r, hr, hrq, hd⟩ := (splittingLaws_unrestricted hR htop hτ hp₀ hnew).1 n hn q hq hqp
  exact ⟨r, (mem_deciderSet_iff _ _ _ _ _ _).mpr ⟨hr, hd⟩, hrq⟩

include hR htop hτ hp₀ hnew in
theorem decidedSegment_mem_binarySequences_unrestricted {p : V} (hp : p ∈ P) (hpp : ⟨p, p₀⟩ₖ ∈ R) :
    decidedSegment P R one τ p ∈ binarySequences V :=
  (splittingLaws_unrestricted hR htop hτ hp₀ hnew).2.1 p hp hpp

include hR htop hτ hp₀ hnew in
theorem decidedSegment_split_unrestricted {p : V} (hp : p ∈ P) (hpp : ⟨p, p₀⟩ₖ ∈ R) :
    ∃ q ∈ P, ∃ q' ∈ P, ⟨q, p⟩ₖ ∈ R ∧ ⟨q', p⟩ₖ ∈ R ∧
      Incompatible (decidedSegment P R one τ q) (decidedSegment P R one τ q') :=
  (splittingLaws_unrestricted hR htop hτ hp₀ hnew).2.2 p hp hpp
end
end ZFVP
