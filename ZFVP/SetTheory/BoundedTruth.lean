import ZFVP.Syntax.MembershipSatisfaction
import ZFVP.Syntax.PackedSatisfaction
import ZFVP.SetTheory.TransitiveClosure

/-! One definable evaluator for bounded formulas in the ambient universe.
Correctness below is for codes of external finite bounded formulas. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def boundedTruthDomain (b : V) : V := transitiveClosure ({range b} : V)

instance boundedTruthDomain_definable : ℒₛₑₜ-function₁[V] boundedTruthDomain := by
  unfold boundedTruthDomain
  definability

instance boundedTruthDomain_transitive (b : V) : IsTransitive (boundedTruthDomain b) :=
  transitiveClosure_transitive _

theorem range_mem_boundedTruthDomain (b : V) : range b ∈ boundedTruthDomain b :=
  subset_transitiveClosure _ _ (by simp)

theorem boundedTruthDomain_nonempty (b : V) : IsNonempty (boundedTruthDomain b) :=
  ⟨⟨range b, range_mem_boundedTruthDomain b⟩⟩

theorem range_subset_boundedTruthDomain (b : V) : range b ⊆ boundedTruthDomain b :=
  fun x hx ↦ (boundedTruthDomain_transitive b).transitive _ (range_mem_boundedTruthDomain b) x hx

theorem standardTuple_value_mem_boundedTruthDomain {n : ℕ} (b : Fin n → V) (i : Fin n) :
    b i ∈ boundedTruthDomain (standardTuple b) := by
  apply range_subset_boundedTruthDomain
  exact mem_range_of_kpair_mem ((mem_standardTuple_iff b _).mpr ⟨i, rfl⟩)

def BoundedTruth (n φ b : V) : Prop :=
  Satisfies membershipLanguageCode ∅ (membershipStructureCode (boundedTruthDomain b)) ∅ n φ b

noncomputable def boundedTruthGraph (b : V) : V :=
  satisfactionGraph membershipLanguageCode ∅ (membershipStructureCode (boundedTruthDomain b)) ∅

instance boundedTruthGraph_definable : ℒₛₑₜ-function₁[V] boundedTruthGraph := by
  exact Language.DefinableFunction.substitution
    (f := ![fun _ ↦ membershipLanguageCode, fun _ ↦ ∅,
      fun v : Fin 1 → V ↦ membershipStructureCode (boundedTruthDomain (v 0)), fun _ ↦ ∅])
    satisfactionGraph_definable (by simp [Fin.forall_fin_iff_zero_and_forall_succ]; all_goals definability)

instance boundedTruth_definable : ℒₛₑₜ-relation₃[V] BoundedTruth := by
  change ℒₛₑₜ-relation₃[V] (fun n φ b ↦ b ∈ (boundedTruthGraph b) ‘ ⟨n, φ⟩ₖ)
  definability

theorem boundedTruth_correct {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (b : Fin n → V) :
    BoundedTruth (n : V) (encodeMembershipFormula φ) (standardTuple b) ↔ φ.Evalb b := by
  let c : Fin n → SetDomain (boundedTruthDomain (standardTuple b)) :=
    fun i ↦ ⟨b i, standardTuple_value_mem_boundedTruthDomain b i⟩
  exact satisfies_boundedMembershipFormula
    (boundedTruthDomain_nonempty (standardTuple b)) hφ c

end ZFVP
