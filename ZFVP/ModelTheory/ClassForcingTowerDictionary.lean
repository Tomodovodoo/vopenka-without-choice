import ZFVP.ModelTheory.ClassForcingFormulaCompiler

/-! Fixed formulas for the tagged class forcing of a tower. Only the
stage carriers, orders and section maps are syntactic inputs. Bounded
stages, names and atomic forcing are defined from those inputs here. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

structure ClassForcingTowerDictionary where
  carrier : SetTheorySemisentence 2
  order : SetTheorySemisentence 2
  sectionMap : SetTheorySemisentence 3

namespace ClassForcingTowerDictionary

def condition (D : ClassForcingTowerDictionary) : SetTheorySemisentence 1 :=
  f“c. ∃ i p, !IsOrdinal.dfn i ∧ p ∈ !(D.carrier) i ∧ c = !kpair.dfn i p”

def le (D : ClassForcingTowerDictionary) : SetTheorySemisentence 2 :=
  f“c d. !(D.condition) c ∧ !(D.condition) d ∧ ∃ θ, !IsOrdinal.dfn θ ∧
    !kpair.π₁.dfn c ⊆ θ ∧ !kpair.π₁.dfn d ⊆ θ ∧
    !kpair.dfn (!value.dfn (!(D.sectionMap) (!kpair.π₁.dfn c) θ) (!kpair.π₂.dfn c))
      (!value.dfn (!(D.sectionMap) (!kpair.π₁.dfn d) θ) (!kpair.π₂.dfn d)) ∈ !(D.order) θ”

def boundedConditions (D : ClassForcingTowerDictionary) : SetTheorySemisentence 2 :=
  f“B θ. ∀ c, c ∈ B ↔ ∃ i ∈ !succ.dfn θ, ∃ p ∈ !(D.carrier) i, c = !kpair.dfn i p”

def boundedOrder (D : ClassForcingTowerDictionary) : SetTheorySemisentence 2 :=
  f“R θ. ∀ z, z ∈ R ↔
    z ∈ !prod.dfn (!(D.boundedConditions) θ) (!(D.boundedConditions) θ) ∧
      !(D.le) (!kpair.π₁.dfn z) (!kpair.π₂.dfn z)”

def isName (D : ClassForcingTowerDictionary) : SetTheorySemisentence 1 :=
  f“τ. ∃ θ, !IsOrdinal.dfn θ ∧ !forcingNameFormula (!(D.boundedConditions) θ) τ”

def equal (D : ClassForcingTowerDictionary) : SetTheorySemisentence 3 :=
  f“σ τ p. ∃ i, !IsOrdinal.dfn i ∧
    !forcingNameFormula (!(D.boundedConditions) i) σ ∧
    !forcingNameFormula (!(D.boundedConditions) i) τ ∧
    p ∈ !atomicEqualityFormula (!(D.boundedConditions) i) (!(D.boundedOrder) i) σ τ”

def member (D : ClassForcingTowerDictionary) : SetTheorySemisentence 3 :=
  f“σ τ p. ∃ i, !IsOrdinal.dfn i ∧
    !forcingNameFormula (!(D.boundedConditions) i) σ ∧
    !forcingNameFormula (!(D.boundedConditions) i) τ ∧
    p ∈ !atomicMembershipFormula (!(D.boundedConditions) i) (!(D.boundedOrder) i) σ τ”

def formulaDictionary (D : ClassForcingTowerDictionary) : ClassForcingFormulaDictionary :=
  ⟨D.condition, D.le, D.isName, D.equal, D.member⟩

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure Defines (D : ClassForcingTowerDictionary) (T : DefinableForcingTower V) : Prop where
  carrier : (ℒₛₑₜ-function₁[V] T.P via D.carrier)
  order : (ℒₛₑₜ-function₁[V] T.R via D.order)
  sectionMap : (ℒₛₑₜ-function₂[V] T.sectionMap via D.sectionMap)

variable {D : ClassForcingTowerDictionary} {T : DefinableForcingTower V}

theorem condition_defined (hD : D.Defines T) :
    ℒₛₑₜ-predicate[V] T.Condition via D.condition := by
  let := hD.carrier
  exact ⟨fun v ↦ by simp [condition, DefinableForcingTower.Condition]⟩

theorem le_defined (hD : D.Defines T) : ℒₛₑₜ-relation[V] T.LE via D.le := by
  let := hD.order
  let := hD.sectionMap
  let := condition_defined hD
  exact ⟨fun v ↦ by simp [le, DefinableForcingTower.LE]⟩

theorem boundedConditions_defined (hD : D.Defines T) :
    ℒₛₑₜ-function₁[V] T.boundedConditions via D.boundedConditions := by
  let := hD.carrier
  refine ⟨fun v ↦ ?_⟩
  rw [mem_ext_iff]
  simp [boundedConditions, T.mem_boundedConditions]

theorem boundedOrder_defined (hD : D.Defines T) :
    ℒₛₑₜ-function₁[V] T.boundedOrder via D.boundedOrder := by
  let := boundedConditions_defined hD
  let := le_defined hD
  refine ⟨fun v ↦ ?_⟩
  rw [mem_ext_iff]
  simp [boundedOrder, DefinableForcingTower.boundedOrder]

theorem isName_defined (hD : D.Defines T) :
    ℒₛₑₜ-predicate[V] T.IsName via D.isName := by
  let := boundedConditions_defined hD
  exact ⟨fun v ↦ by simp [isName, T.isName_iff_bounded]⟩

theorem equal_defined (hD : D.Defines T) :
    ℒₛₑₜ-relation₃[V] T.ForcesEqual via D.equal := by
  let := boundedConditions_defined hD
  let := boundedOrder_defined hD
  exact ⟨fun v ↦ by simp [equal, DefinableForcingTower.ForcesEqual]⟩

theorem member_defined (hD : D.Defines T) :
    ℒₛₑₜ-relation₃[V] T.ForcesMember via D.member := by
  let := boundedConditions_defined hD
  let := boundedOrder_defined hD
  exact ⟨fun v ↦ by simp [member, DefinableForcingTower.ForcesMember]⟩

theorem formulaDictionary_defines (hD : D.Defines T) : D.formulaDictionary.Defines T :=
  ⟨condition_defined hD, le_defined hD, isName_defined hD,
    equal_defined hD, member_defined hD⟩

theorem forcingFormula_defined (hD : D.Defines T) {n : ℕ} (φ : SetTheorySemisentence n) :
    ℒₛₑₜ-relation[V] (T.towerFormula φ) via D.formulaDictionary.compile φ :=
  ClassForcingFormulaDictionary.compile_defined (formulaDictionary_defines hD) φ

end ClassForcingTowerDictionary
end ZFVP
