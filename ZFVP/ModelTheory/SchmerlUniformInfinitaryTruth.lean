import ZFVP.ModelTheory.SchmerlUniformInfinitarySyntax

/-! A fixed first-order definition of full internal infinitary truth. Q uses
internal countability in this definition, so elementary transfer is literal. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def witnessFiberFormula : SetTheorySemisentence 6 :=
  f“A M n b previous φ. ∀ x, x ∈ A ↔ x ∈ !structureDomainFormula M ∧
    !assignmentPrependFormula n b x ∈ !value.dfn previous (!kpair.dfn (!succ.dfn n) φ)”

def stepHoldsFormula : SetTheorySemisentence 5 :=
  f“L M p previous b.
    (∃ φ, !kpair.π₂.dfn p = !foCodeFormula φ ∧
      !satisfiesFormula L (!isEmpty) M (!isEmpty) (!kpair.π₁.dfn p) φ b) ∨
    (∃ φ, !kpair.π₂.dfn p = !negCodeFormula φ ∧ b ∉ !value.dfn previous (!kpair.dfn (!kpair.π₁.dfn p) φ)) ∨
    (∃ f, !kpair.π₂.dfn p = !conjCodeFormula f ∧ ∀ i ∈ !isω,
      b ∈ !value.dfn previous (!kpair.dfn (!kpair.π₁.dfn p) (!value.dfn f i))) ∨
    (∃ φ, !kpair.π₂.dfn p = !exsCodeFormula φ ∧ ∃ x ∈ !structureDomainFormula M,
      !assignmentPrependFormula (!kpair.π₁.dfn p) b x ∈
        !value.dfn previous (!kpair.dfn (!succ.dfn (!kpair.π₁.dfn p)) φ)) ∨
    ∃ φ, !kpair.π₂.dfn p = !qCodeFormula φ ∧
      ¬!internallyCountableFormula (!witnessFiberFormula M (!kpair.π₁.dfn p) b previous φ)”

def isTruthGraphFormula : SetTheorySemisentence 4 :=
  f“L F M g. !IsFunction.dfn g ∧ !domain.dfn g = F ∧ ∀ p ∈ F, ∀ b,
    b ∈ !value.dfn g p ↔ b ∈ !function.dfn (!structureDomainFormula M) (!kpair.π₁.dfn p) ∧
      !stepHoldsFormula L M p (!restrict.dfn g (!predecessorsFormula (!immediateRelationFormula F) F p)) b”

def truthGraphFormula : SetTheorySemisentence 4 := f“g L F M. !isTruthGraphFormula L F M g”

def holdsFormula : SetTheorySemisentence 6 :=
  f“L F M n φ b. b ∈ !value.dfn (!truthGraphFormula L F M) (!kpair.dfn n φ)”

@[simp] theorem eval_nestFormulaeFunc_five {Λ : Language} {ξ A : Type*} [Structure Λ A]
    {m : ℕ} {e : Fin m → A} {f : ξ → A} {z : A} {φ : Semiformula Λ ξ 6}
    {ψ₁ ψ₂ ψ₃ ψ₄ ψ₅ : Semiformula Λ ξ (m + 1)} :
    Semiformula.Eval (z :> e) f (φ.nestFormulaeFunc ![ψ₁, ψ₂, ψ₃, ψ₄, ψ₅]) ↔
      ∀ x₁, Semiformula.Eval (x₁ :> e) f ψ₁ →
      ∀ x₂, Semiformula.Eval (x₂ :> e) f ψ₂ →
      ∀ x₃, Semiformula.Eval (x₃ :> e) f ψ₃ →
      ∀ x₄, Semiformula.Eval (x₄ :> e) f ψ₄ →
      ∀ x₅, Semiformula.Eval (x₅ :> e) f ψ₅ → Semiformula.Eval ![z, x₁, x₂, x₃, x₄, x₅] f φ := by
  simp [Semiformula.eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq,
    Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  grind

variable {V W : Type*} [SetStructure V] [SetStructure W] [Nonempty V] [Nonempty W]
  [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance witnessFiberFormula_defined : ℒₛₑₜ-function₅[V] witnessFiber via witnessFiberFormula :=
  ⟨fun v ↦ by
    change witnessFiberFormula.Evalb v ↔ v 0 = witnessFiber (v 1) (v 2) (v 3) (v 4) (v 5)
    rw [mem_ext_iff]
    simp [witnessFiberFormula, witnessFiber]⟩

instance stepHoldsFormula_defined : Defined
    (fun v : Fin 5 → V ↦ StepHolds (v 0) (v 1) (v 2) (v 3) (v 4)) stepHoldsFormula :=
  ⟨fun v ↦ by simp [stepHoldsFormula, StepHolds]⟩

instance isTruthGraphFormula_defined : ℒₛₑₜ-relation₄[V] IsTruthGraph via isTruthGraphFormula :=
  ⟨fun v ↦ by simp [isTruthGraphFormula, IsTruthGraph]⟩

instance truthGraphFormula_defined : ℒₛₑₜ-function₃[V] truthGraph via truthGraphFormula :=
  ⟨fun v ↦ by
    change truthGraphFormula.Evalb v ↔ v 0 = truthGraph (v 1) (v 2) (v 3)
    rw [eq_comm, truthGraph_eq_iff]
    simp [truthGraphFormula]⟩

instance holdsFormula_defined : Defined
    (fun v : Fin 6 → V ↦ Holds (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) holdsFormula :=
  ⟨fun v ↦ by simp [holdsFormula, Holds]⟩

theorem ElementaryMap.fragment_iff (j : ElementaryMap V W) (L F : V) :
    IsFragment (j L) (j F) ↔ IsFragment L F :=
  (j.map_defined isFragmentFormula (fun v ↦ IsFragment (v 0) (v 1))
    (fun v ↦ IsFragment (v 0) (v 1)) ![L, F]).symm

theorem ElementaryMap.holds_iff (j : ElementaryMap V W) (L F M n φ b : V) :
    Holds (j L) (j F) (j M) (j n) (j φ) (j b) ↔ Holds L F M n φ b :=
  (j.map_defined holdsFormula (fun v ↦ Holds (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
    (fun v ↦ Holds (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) ![L, F, M, n, φ, b]).symm

end ZFVP.Infinitary.Internal
