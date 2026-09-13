import ZFVP.SetTheory.UniformLowTruth
import ZFVP.SetTheory.UniformRecursion
import ZFVP.SetTheory.UniformNumerals
import ZFVP.Syntax.UniformAssignments
import ZFVP.Syntax.MembershipTruthTables
import ZFVP.SetTheory.RankBounds
import ZFVP.SetTheory.LevelOneTruth

/-! Ordinal definability relative to a parameter class. The parameter class is given by a
two-variable formula `Pf` with one parameter `p`; the allowed parameters are the ordinals, the
two-variable membership formula codes and the members of the class. A parameter tree is a finite
pairing of allowed parameters. A set is ordinal definable when it is the set of elements of some
stage `V_α` satisfying, in the structure `(V_α, ∈)`, a coded two-variable formula with a parameter
tree lying in `V_α`; it is hereditarily ordinal definable when in addition every element of its
transitive closure is ordinal definable. All notions have parameter-free defining formulas in the
variables `x` and `p`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Allowed parameters: ordinals, two-variable membership formula codes and members of the
class. -/
def allowedFormula (Pf : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  f“x p. !IsOrdinal.dfn x ∨
    !kpair.dfn (!(numeralFormula 2)) x ∈ !formulaFamilyFormula (!membershipLanguageCodeFormula) (!isEmpty) ∨
    !Pf x p”

/-- Parameter trees: finite pairings of allowed parameters, witnessed by a closed finite
collection. -/
def parameterTreeFormula (Pf : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  f“P p. ∃ S, P ∈ S ∧ ∀ y ∈ S, !(allowedFormula Pf) y p ∨
    ∃ a ∈ S, ∃ b ∈ S, y = !kpair.dfn a b”

/-- The set defined over `V_α` by the code `φ` with the parameter `P`. -/
def decodeFormula : SetTheorySemisentence 4 :=
  f“x α φ P. ∀ z, z ∈ x ↔ z ∈ !hierarchyFormula α ∧
    !membershipSatisfiesFormula (!hierarchyFormula α) (!(numeralFormula 2)) φ
      (!assignmentPrependFormula (!(numeralFormula 1))
        (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) P) z)”

/-- Ordinal definability from the parameter class. -/
def odFormula (Pf : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  f“x p. ∃ α φ P, !IsOrdinal.dfn α ∧
    !kpair.dfn (!(numeralFormula 2)) φ ∈ !formulaFamilyFormula (!membershipLanguageCodeFormula) (!isEmpty) ∧
    !(parameterTreeFormula Pf) P p ∧ P ∈ !hierarchyFormula α ∧ x = !decodeFormula α φ P”

/-- Hereditary ordinal definability from the parameter class. -/
def hodFormula (Pf : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  f“x p. !(odFormula Pf) x p ∧ ∀ y ∈ !transitiveClosureFormula x, !(odFormula Pf) y p”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable (Pf : SetTheorySemisentence 2)

def IsAllowed (x p : V) : Prop :=
  IsOrdinal x ∨ IsMembershipFormulaCode ((2 : ℕ) : V) x ∨ Pf.Evalb ![x, p]

instance allowedFormula_defined : ℒₛₑₜ-relation[V] (IsAllowed Pf) via allowedFormula Pf :=
  ⟨fun v ↦ by simp [allowedFormula, IsAllowed, IsMembershipFormulaCode]⟩

def IsParameterTree (P p : V) : Prop :=
  ∃ S : V, P ∈ S ∧ ∀ y ∈ S, IsAllowed Pf y p ∨ ∃ a ∈ S, ∃ b ∈ S, y = ⟨a, b⟩ₖ

instance parameterTreeFormula_defined :
    ℒₛₑₜ-relation[V] (IsParameterTree Pf) via parameterTreeFormula Pf :=
  ⟨fun v ↦ by simp [parameterTreeFormula, IsParameterTree]⟩

theorem isParameterTree_of_allowed {x p : V} (h : IsAllowed Pf x p) : IsParameterTree Pf x p :=
  ⟨{x}, mem_singleton_iff.mpr rfl, fun y hy ↦ Or.inl (by rw [mem_singleton_iff.mp hy]; exact h)⟩

theorem isParameterTree_kpair {P Q p : V} (hP : IsParameterTree Pf P p) (hQ : IsParameterTree Pf Q p) :
    IsParameterTree Pf ⟨P, Q⟩ₖ p := by
  obtain ⟨S, hPS, hS⟩ := hP
  obtain ⟨T, hQT, hT⟩ := hQ
  refine ⟨insert ⟨P, Q⟩ₖ (S ∪ T), mem_insert.mpr (Or.inl rfl), ?_⟩
  intro y hy
  rcases mem_insert.mp hy with rfl | hy
  · exact Or.inr ⟨P, mem_insert.mpr (Or.inr (mem_union_iff.mpr (Or.inl hPS))),
      Q, mem_insert.mpr (Or.inr (mem_union_iff.mpr (Or.inr hQT))), rfl⟩
  · rcases mem_union_iff.mp hy with hy | hy
    · rcases hS y hy with h | ⟨a, ha, b, hb, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, mem_insert.mpr (Or.inr (mem_union_iff.mpr (Or.inl ha))),
          b, mem_insert.mpr (Or.inr (mem_union_iff.mpr (Or.inl hb))), rfl⟩
    · rcases hT y hy with h | ⟨a, ha, b, hb, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, mem_insert.mpr (Or.inr (mem_union_iff.mpr (Or.inr ha))),
          b, mem_insert.mpr (Or.inr (mem_union_iff.mpr (Or.inr hb))), rfl⟩

end

theorem decodeMembership_definable (α φ P : V) :
    ℒₛₑₜ-predicate (fun z : V ↦ MembershipSatisfies (hierarchy α) ((2 : ℕ) : V) φ (standardTuple ![z, P])) := by
  simp only [standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  definability

/-- The set defined over `V_α` by the code `φ` with the parameter `P`. -/
noncomputable def decode (α φ P : V) : V :=
  sep (hierarchy α) (fun z ↦ MembershipSatisfies (hierarchy α) ((2 : ℕ) : V) φ (standardTuple ![z, P]))
    (decodeMembership_definable α φ P)

theorem mem_decode_iff (α φ P z : V) :
    z ∈ decode α φ P ↔ z ∈ hierarchy α ∧ MembershipSatisfies (hierarchy α) ((2 : ℕ) : V) φ (standardTuple ![z, P]) :=
  mem_sep_iff

theorem standardTuple_two_numeral (z P : V) :
    standardTuple ![z, P] = assignmentPrepend ((1 : ℕ) : V) (assignmentPrepend ((0 : ℕ) : V) ∅ P) z := by
  simp [standardTuple]

instance decodeFormula_defined : ℒₛₑₜ-function₃[V] decode via decodeFormula :=
  ⟨fun v ↦ by
    simp only [decodeFormula, Semiformula.Evalb]
    simp
    constructor
    · intro h
      apply mem_ext
      intro z
      rw [mem_decode_iff, standardTuple_two_numeral]
      exact h z
    · intro h z
      rw [h, mem_decode_iff, standardTuple_two_numeral]
      exact Iff.rfl⟩

section

variable (Pf : SetTheorySemisentence 2)

def IsOD (x p : V) : Prop :=
  ∃ α φ P : V, IsOrdinal α ∧ IsMembershipFormulaCode ((2 : ℕ) : V) φ ∧ IsParameterTree Pf P p ∧
    P ∈ hierarchy α ∧ x = decode α φ P

instance odFormula_defined : ℒₛₑₜ-relation[V] (IsOD Pf) via odFormula Pf :=
  ⟨fun v ↦ by simp [odFormula, IsOD, IsMembershipFormulaCode]⟩

def IsHOD (x p : V) : Prop := IsOD Pf x p ∧ ∀ y ∈ transitiveClosure x, IsOD Pf y p

instance hodFormula_defined : ℒₛₑₜ-relation[V] (IsHOD Pf) via hodFormula Pf :=
  ⟨fun v ↦ by simp [hodFormula, IsHOD]⟩

/-- A defined binary relation with a fixed second argument is a definable predicate. -/
theorem definablePred_of_defined {R : V → V → Prop} {φ : SetTheorySemisentence 2}
    (h : ℒₛₑₜ-relation[V] R via φ) (p : V) : ℒₛₑₜ-predicate (fun x : V ↦ R x p) :=
  ⟨Rew.embSubsts ![Semiterm.bvar 0, Semiterm.fvar p] ▹ φ, fun v ↦ by
    rw [Semiformula.eval_embSubsts]
    have hv : (Semiterm.val (L := ℒₛₑₜ) (M := V) v id ∘
        (![Semiterm.bvar 0, Semiterm.fvar p] : Fin 2 → SetTheorySemiterm V 1)) = ![v 0, p] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
    rw [hv]
    exact h.iff ![v 0, p]⟩

theorem isOD_definable (p : V) : ℒₛₑₜ-predicate (fun x : V ↦ IsOD Pf x p) :=
  definablePred_of_defined (odFormula_defined Pf) p

theorem isHOD_definable (p : V) : ℒₛₑₜ-predicate (fun x : V ↦ IsHOD Pf x p) :=
  definablePred_of_defined (hodFormula_defined Pf) p

theorem IsHOD.od {x p : V} (h : IsHOD Pf x p) : IsOD Pf x p := h.1

/-- Hereditary ordinal definability is transitive. -/
theorem IsHOD.mem {x y p : V} (h : IsHOD Pf x p) (hy : y ∈ x) : IsHOD Pf y p := by
  refine ⟨h.2 y (subset_transitiveClosure x y hy), fun z hz ↦ h.2 z ?_⟩
  have hsub : transitiveClosure y ⊆ transitiveClosure x :=
    transitiveClosure_minimal y _ (fun w hw ↦ (transitiveClosure_transitive x).mem_trans hw
      (subset_transitiveClosure x y hy)) (transitiveClosure_transitive x)
  exact hsub z hz

end

end ZFVP
