import ZFVP.ModelTheory.StandardCodedRules
import ZFVP.Syntax.MembershipEncodingRewriting

/-! Finite external sequents encoded as internal finite sets of formula codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def encodeClosedSequent {n : ℕ} (Γ : List (SetTheorySemisentence n)) : V :=
  standardListSet (Γ.map encodeMembershipFormula)

@[simp] theorem mem_encodeClosedSequent {n : ℕ} (Γ : List (SetTheorySemisentence n)) (ψ : V) :
    ψ ∈ encodeClosedSequent (V := V) Γ ↔ ∃ φ ∈ Γ, ψ = encodeMembershipFormula φ := by
  simp [encodeClosedSequent, eq_comm]

@[simp] theorem encodeClosedSequent_nil (n : ℕ) :
    encodeClosedSequent (V := V) ([] : List (SetTheorySemisentence n)) = ∅ := rfl

@[simp] theorem encodeClosedSequent_cons {n : ℕ} (φ : SetTheorySemisentence n) (Γ : List (SetTheorySemisentence n)) :
    encodeClosedSequent (V := V) (φ :: Γ) = insert (encodeMembershipFormula φ) (encodeClosedSequent Γ) := rfl

@[simp] theorem encodeClosedSequent_append {n : ℕ} (Γ Δ : List (SetTheorySemisentence n)) :
    encodeClosedSequent (V := V) (Γ ++ Δ) = encodeClosedSequent Γ ∪ encodeClosedSequent Δ := by
  simp [encodeClosedSequent]

theorem encodeClosedSequent_valid {n : ℕ} (Γ : List (SetTheorySemisentence n)) :
    IsCodedSequent (n : V) (encodeClosedSequent Γ) := by
  apply isCodedSequent_standardListSet (by simp)
  intro φ hφ
  obtain ⟨ψ, _, rfl⟩ := List.mem_map.mp hφ
  exact encodeMembershipFormula_mem ψ

theorem encodeClosedSequent_mono {n : ℕ} {Γ Δ : List (SetTheorySemisentence n)} (h : Γ ⊆ Δ) :
    encodeClosedSequent (V := V) Γ ⊆ encodeClosedSequent Δ := by
  intro φ hφ
  obtain ⟨ψ, hψ, rfl⟩ := (mem_encodeClosedSequent Γ φ).mp hφ
  exact (mem_encodeClosedSequent Δ _).mpr ⟨ψ, h hψ, rfl⟩

theorem encodeClosedSequent_rename {n m : ℕ} {r : V}
    (hr : r ∈ (m : V) ^ (n : V)) (f : Fin n → Fin m)
    (he : ∀ i : Fin n, r ‘ (i.val : V) = ((f i).val : V))
    (σ : Rew ℒₛₑₜ Empty n Empty m) (hσ : ∀ i, σ (.bvar i) = .bvar (f i))
    (Γ : List (SetTheorySemisentence n)) :
    renameCodedSequent (n : V) (m : V) r (encodeClosedSequent Γ) =
      encodeClosedSequent (Γ.map (fun φ ↦ σ ▹ φ)) := by
  apply mem_ext
  intro ψ
  simp only [mem_renameCodedSequent_iff, mem_encodeClosedSequent, List.mem_map]
  constructor
  · rintro ⟨χ, ⟨φ, hφ, rfl⟩, rfl⟩
    exact ⟨σ ▹ φ, ⟨φ, hφ, rfl⟩, renameMembershipFormula_encode hr f he σ hσ φ⟩
  · rintro ⟨χ, ⟨φ, hφ, rfl⟩, rfl⟩
    exact ⟨encodeMembershipFormula φ, ⟨φ, hφ, rfl⟩, (renameMembershipFormula_encode hr f he σ hσ φ).symm⟩

theorem encodeClosedSequent_bShift {n : ℕ} (Γ : List (SetTheorySemisentence n)) :
    encodeClosedSequent (V := V) (Γ.map (fun φ ↦ Rew.bShift ▹ φ)) =
      shiftCodedSequent (n : V) (encodeClosedSequent Γ) := by
  apply mem_ext
  intro ψ
  simp only [shiftCodedSequent, mem_renameCodedSequent_iff, mem_encodeClosedSequent, List.mem_map]
  constructor
  · rintro ⟨χ, ⟨φ, hφ, rfl⟩, rfl⟩
    exact ⟨encodeMembershipFormula φ, ⟨φ, hφ, rfl⟩, encodeMembershipFormula_bShift φ⟩
  · rintro ⟨χ, ⟨φ, hφ, rfl⟩, rfl⟩
    exact ⟨Rew.bShift ▹ φ, ⟨φ, hφ, rfl⟩, (encodeMembershipFormula_bShift φ).symm⟩

noncomputable def encodeFiniteSequent (k : ℕ) (Γ : Sequent ℒₛₑₜ) : V :=
  encodeClosedSequent (Γ.map (finiteVariableClosure k))

@[simp] theorem encodeFiniteSequent_nil (k : ℕ) : encodeFiniteSequent (V := V) k [] = ∅ := rfl

@[simp] theorem encodeFiniteSequent_cons (k : ℕ) (φ : SetTheoryProposition) (Γ : Sequent ℒₛₑₜ) :
    encodeFiniteSequent (V := V) k (φ :: Γ) =
      insert (encodeMembershipFormula (finiteVariableClosure k φ)) (encodeFiniteSequent k Γ) := rfl

@[simp] theorem encodeFiniteSequent_append (k : ℕ) (Γ Δ : Sequent ℒₛₑₜ) :
    encodeFiniteSequent (V := V) k (Γ ++ Δ) = encodeFiniteSequent k Γ ∪ encodeFiniteSequent k Δ := by
  simp [encodeFiniteSequent]

theorem encodeFiniteSequent_valid (k : ℕ) (Γ : Sequent ℒₛₑₜ) :
    IsCodedSequent ((k + 1 : ℕ) : V) (encodeFiniteSequent k Γ) :=
  encodeClosedSequent_valid _

theorem encodeFiniteSequent_mono (k : ℕ) {Γ Δ : Sequent ℒₛₑₜ} (h : Γ ⊆ Δ) :
    encodeFiniteSequent (V := V) k Γ ⊆ encodeFiniteSequent k Δ :=
  encodeClosedSequent_mono (List.map_subset _ h)

theorem encodeFiniteSequent_shift (k : ℕ) (Γ : Sequent ℒₛₑₜ) :
    encodeFiniteSequent (V := V) (k + 1) Γ⁺ =
      shiftCodedSequent (((k + 1 : ℕ) : V)) (encodeFiniteSequent k Γ) := by
  unfold encodeFiniteSequent
  rw [← encodeClosedSequent_bShift]
  congr 1
  simp [Rewriting.shifts, List.map_map, Function.comp_def, finiteVariableClosure_shift]

end ZFVP
