import ZFVP.SetTheory.BoundedTruth
import ZFVP.SetTheory.LevyAbsoluteness
import ZFVP.SetTheory.FormulaReflection

/-! Definable level-one truth predicates, with correctness on external finite syntax.
The proofs use transitive-set absoluteness and the proved finite reflection theorem. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def membershipSatisfactionGraph (A : V) : V :=
  satisfactionGraph membershipLanguageCode ∅ (membershipStructureCode A) ∅

instance membershipSatisfactionGraph_definable : ℒₛₑₜ-function₁[V] membershipSatisfactionGraph := by
  exact Language.DefinableFunction.substitution
    (f := ![fun _ ↦ membershipLanguageCode, fun _ ↦ ∅,
      fun v : Fin 1 → V ↦ membershipStructureCode (v 0), fun _ ↦ ∅])
    satisfactionGraph_definable (by simp [Fin.forall_fin_iff_zero_and_forall_succ]; all_goals definability)

def MembershipSatisfies (A n φ b : V) : Prop := b ∈ (membershipSatisfactionGraph A) ‘ ⟨n, φ⟩ₖ

instance membershipSatisfies_definable : ℒₛₑₜ-relation₄[V] MembershipSatisfies := by
  unfold MembershipSatisfies
  definability

theorem membershipSatisfies_encode {A : V} (hA : IsNonempty A) {n : ℕ}
    (φ : SetTheorySemisentence n) (b : Fin n → SetDomain A) :
    MembershipSatisfies A (n : V) (encodeMembershipFormula φ)
      (standardTuple (fun i ↦ (b i).val)) ↔ φ.Evalb b :=
  satisfies_encodeMembershipFormula hA φ b

theorem standardTuple_values_mem {A : V} {n : ℕ} (b : Fin n → V)
    (hb : standardTuple b ∈ A ^ (n : V)) (i : Fin n) : b i ∈ A := by
  have h := function_value_mem hb (natCast_mem_of_lt i.isLt)
  simpa only [value_standardTuple] using h

theorem finite_coded_reflection_containing (Φ : List FormulaWithArity) (X : V) :
    ∃ δ : V, IsOrdinal δ ∧ X ∈ hierarchy δ ∧ IsNonempty (hierarchy δ) ∧
      ∀ φ ∈ Φ, ∀ b : Fin φ.1 → SetDomain (hierarchy δ),
        MembershipSatisfies (hierarchy δ) (φ.1 : V) (encodeMembershipFormula φ.2)
          (standardTuple (fun i ↦ (b i).val)) ↔ φ.2.Evalb (fun i ↦ (b i).val) := by
  obtain ⟨δ, hδ, hX, _, _, hΦ⟩ := finite_formula_reflection_containing Φ X
  have hA : IsNonempty (hierarchy δ) := ⟨⟨X, hX⟩⟩
  refine ⟨δ, hδ, hX, hA, ?_⟩
  intro φ hφ b
  exact (membershipSatisfies_encode hA φ.2 b).trans (hΦ φ hφ b)

def SigmaOneTruth (n φ b : V) : Prop :=
  ∃ A, IsTransitive A ∧ IsNonempty A ∧ b ∈ A ^ n ∧ MembershipSatisfies A n φ b

def PiOneTruth (n φ b : V) : Prop :=
  ∀ A, IsTransitive A → IsNonempty A → b ∈ A ^ n → MembershipSatisfies A n φ b



instance sigmaOneTruth_definable : ℒₛₑₜ-relation₃[V] SigmaOneTruth := by
  unfold SigmaOneTruth
  definability

instance piOneTruth_definable : ℒₛₑₜ-relation₃[V] PiOneTruth := by
  unfold PiOneTruth
  definability

theorem reflectingMembershipDomain {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → V) :
    ∃ A : V, IsTransitive A ∧ IsNonempty A ∧ standardTuple b ∈ A ^ (n : V) ∧
      (MembershipSatisfies A (n : V) (encodeMembershipFormula φ) (standardTuple b) ↔ φ.Evalb b) := by
  obtain ⟨δ, hδ, hr, hA, hφ⟩ := finite_coded_reflection_containing [⟨n, φ⟩] (range (standardTuple b))
  have : IsOrdinal δ := hδ
  have htrans := hierarchy_transitive δ
  have hb : ∀ i, b i ∈ hierarchy δ := fun i ↦
    htrans.transitive _ hr _ (mem_range_of_kpair_mem ((mem_standardTuple_iff b _).mpr ⟨i, rfl⟩))
  let c : Fin n → SetDomain (hierarchy δ) := fun i ↦ ⟨b i, hb i⟩
  exact ⟨hierarchy δ, htrans, hA, standardTuple_mem_function b hb, hφ ⟨n, φ⟩ (by simp) c⟩

theorem sigmaOneTruth_correct {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsSigmaFormula 1 φ) (b : Fin n → V) :
    SigmaOneTruth (n : V) (encodeMembershipFormula φ) (standardTuple b) ↔ φ.Evalb b := by
  constructor
  · rintro ⟨A, htrans, hA, hb, hs⟩
    have : IsTransitive A := htrans
    let c : Fin n → SetDomain A := fun i ↦ ⟨b i, standardTuple_values_mem b hb i⟩
    exact sigma_one_upward A hφ c ((membershipSatisfies_encode hA φ c).mp hs)
  · intro h
    obtain ⟨A, htrans, hA, hb, href⟩ := reflectingMembershipDomain φ b
    exact ⟨A, htrans, hA, hb, href.mpr h⟩

theorem piOneTruth_correct {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsPiFormula 1 φ) (b : Fin n → V) :
    PiOneTruth (n : V) (encodeMembershipFormula φ) (standardTuple b) ↔ φ.Evalb b := by
  constructor
  · intro h
    obtain ⟨A, htrans, hA, hb, href⟩ := reflectingMembershipDomain φ b
    exact href.mp (h A htrans hA hb)
  · intro h A htrans hA hb
    have : IsTransitive A := htrans
    let c : Fin n → SetDomain A := fun i ↦ ⟨b i, standardTuple_values_mem b hb i⟩
    exact (membershipSatisfies_encode hA φ c).mpr (pi_one_downward A hφ c h)

end ZFVP

