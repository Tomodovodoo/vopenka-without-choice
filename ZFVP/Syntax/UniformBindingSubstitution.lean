import ZFVP.Syntax.SubstitutionStates
import ZFVP.Syntax.UniformTermSubstitution
import ZFVP.Syntax.UniformAssignments

/-! Shared definitions for lifting substitutions through binders. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundShiftReplacementFormula : SetTheorySemisentence 2 :=
  f“B n. ∀ p, p ∈ B ↔ ∃ i ∈ n, p = !kpair.dfn i (!boundVarCodeFormula (!succ.dfn i))”

def freeIdentityReplacementFormula : SetTheorySemisentence 2 :=
  f“E Γ. ∀ p, p ∈ E ↔ ∃ x ∈ Γ, p = !kpair.dfn x (!freeVarCodeFormula x)”

def termBoundShiftFormula : SetTheorySemisentence 4 :=
  f“g L Γ n. g = !termSubstitutionFormula L Γ n (!boundShiftReplacementFormula n) (!freeIdentityReplacementFormula Γ)”

def liftBoundReplacementFormula : SetTheorySemisentence 6 :=
  f“B L Δ m n b. B = !assignmentPrependFormula n (!composeFormula b (!termBoundShiftFormula L Δ m))
    (!boundVarCodeFormula (!(numeralFormula 0)))”

def liftFreeReplacementFormula : SetTheorySemisentence 5 :=
  f“E L Δ m e. E = !composeFormula e (!termBoundShiftFormula L Δ m)”

def substitutionStateFormula : SetTheorySemisentence 5 :=
  f“s n m B E. s = !kpair.dfn (!kpair.dfn n m) (!kpair.dfn B E)”

def stateSourceFormula : SetTheorySemisentence 2 := f“n s. n = !kpair.π₁.dfn (!kpair.π₁.dfn s)”
def stateTargetFormula : SetTheorySemisentence 2 := f“m s. m = !kpair.π₂.dfn (!kpair.π₁.dfn s)”
def stateBoundFormula : SetTheorySemisentence 2 := f“B s. B = !kpair.π₁.dfn (!kpair.π₂.dfn s)”
def stateFreeFormula : SetTheorySemisentence 2 := f“E s. E = !kpair.π₂.dfn (!kpair.π₂.dfn s)”

def liftSubstitutionStateFormula : SetTheorySemisentence 4 :=
  f“t L Δ s. t = !substitutionStateFormula (!succ.dfn (!stateSourceFormula s)) (!succ.dfn (!stateTargetFormula s))
    (!liftBoundReplacementFormula L Δ (!stateTargetFormula s) (!stateSourceFormula s) (!stateBoundFormula s))
    (!liftFreeReplacementFormula L Δ (!stateTargetFormula s) (!stateFreeFormula s))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundShiftReplacementFormula_defined :
    ℒₛₑₜ-function₁[V] boundShiftReplacement via boundShiftReplacementFormula :=
  ⟨fun v ↦ by
    change boundShiftReplacementFormula.Evalb v ↔ v 0 = boundShiftReplacement (v 1)
    rw [mem_ext_iff]
    simp [boundShiftReplacementFormula, boundShiftReplacement, mem_definableGraph_iff]⟩

instance freeIdentityReplacementFormula_defined :
    ℒₛₑₜ-function₁[V] freeIdentityReplacement via freeIdentityReplacementFormula :=
  ⟨fun v ↦ by
    change freeIdentityReplacementFormula.Evalb v ↔ v 0 = freeIdentityReplacement (v 1)
    rw [mem_ext_iff]
    simp [freeIdentityReplacementFormula, freeIdentityReplacement, mem_definableGraph_iff]⟩

instance termBoundShiftFormula_defined : ℒₛₑₜ-function₃[V] termBoundShift via termBoundShiftFormula :=
  ⟨fun v ↦ by simp [termBoundShiftFormula, termBoundShift]⟩

instance liftBoundReplacementFormula_defined : ℒₛₑₜ-function₅[V] liftBoundReplacement via liftBoundReplacementFormula :=
  ⟨fun v ↦ by simp [liftBoundReplacementFormula, liftBoundReplacement]⟩

instance liftFreeReplacementFormula_defined : ℒₛₑₜ-function₄[V] liftFreeReplacement via liftFreeReplacementFormula :=
  ⟨fun v ↦ by simp [liftFreeReplacementFormula, liftFreeReplacement]⟩

instance substitutionStateFormula_defined : ℒₛₑₜ-function₄[V] substitutionState via substitutionStateFormula :=
  ⟨fun v ↦ by simp [substitutionStateFormula, substitutionState]⟩

instance stateSourceFormula_defined : ℒₛₑₜ-function₁[V] stateSource via stateSourceFormula :=
  ⟨fun v ↦ by simp [stateSourceFormula, stateSource]⟩
instance stateTargetFormula_defined : ℒₛₑₜ-function₁[V] stateTarget via stateTargetFormula :=
  ⟨fun v ↦ by simp [stateTargetFormula, stateTarget]⟩
instance stateBoundFormula_defined : ℒₛₑₜ-function₁[V] stateBound via stateBoundFormula :=
  ⟨fun v ↦ by simp [stateBoundFormula, stateBound]⟩
instance stateFreeFormula_defined : ℒₛₑₜ-function₁[V] stateFree via stateFreeFormula :=
  ⟨fun v ↦ by simp [stateFreeFormula, stateFree]⟩

instance liftSubstitutionStateFormula_defined : ℒₛₑₜ-function₃[V] liftSubstitutionState via liftSubstitutionStateFormula :=
  ⟨fun v ↦ by simp [liftSubstitutionStateFormula, liftSubstitutionState]⟩

end ZFVP
