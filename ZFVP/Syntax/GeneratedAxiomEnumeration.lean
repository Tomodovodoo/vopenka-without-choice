import ZFVP.Syntax.MembershipPrimcoding

/-! An explicit total enumeration of exactly the generated ZF+VP sentence instances. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def generatedAxiomAt (tag k e : ℕ) : Option SetTheorySentence :=
  match tag with
  | 0 => some Axiom.empty
  | 1 => some Axiom.extentionality
  | 2 => some Axiom.pairing
  | 3 => some Axiom.union
  | 4 => some Axiom.power
  | 5 => some Axiom.infinity
  | 6 => some Axiom.foundation
  | 7 => some equalityBasisSentence
  | 8 => (Semiformula.ofNat (L := ℒₛₑₜ) (ξ := Empty) (k + 1) e).map
      (fun φ ↦ ∀¹* separationTemplate.instantiateTail k φ)
  | 9 => (Semiformula.ofNat (L := ℒₛₑₜ) (ξ := Empty) (k + 2) e).map
      (fun φ ↦ ∀¹* replacementTemplate.instantiateTail k φ)
  | 10 => (Semiformula.ofNat (L := ℒₛₑₜ) (ξ := Empty) 2 e).map
      (fun φ ↦ vopenkaTemplate.instantiate φ)
  | _ => none

def generatedAxiomEnumeration (e : ℕ) : Option SetTheorySentence :=
  generatedAxiomAt e.unpair.1 e.unpair.2.unpair.1 e.unpair.2.unpair.2

theorem generatedAxiomAt_mem {tag k e : ℕ} {φ : SetTheorySentence}
    (h : generatedAxiomAt tag k e = some φ) : φ ∈ generatedZFVPTheory := by
  unfold generatedAxiomAt at h
  split at h
  next => cases h; exact .fixed (by simp [fixedZFTheory])
  next => cases h; exact .fixed (by simp [fixedZFTheory])
  next => cases h; exact .fixed (by simp [fixedZFTheory])
  next => cases h; exact .fixed (by simp [fixedZFTheory])
  next => cases h; exact .fixed (by simp [fixedZFTheory])
  next => cases h; exact .fixed (by simp [fixedZFTheory])
  next => cases h; exact .fixed (by simp [fixedZFTheory])
  next => cases h; exact .fixed (by simp [fixedZFTheory])
  next => obtain ⟨ψ, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact .separation k ψ
  next => obtain ⟨ψ, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact .replacement k ψ
  next => obtain ⟨ψ, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact .vopenka ψ
  next => contradiction

theorem generatedAxiomAt_surjective {φ : SetTheorySentence} (h : φ ∈ generatedZFVPTheory) :
    ∃ tag k e, generatedAxiomAt tag k e = some φ := by
  cases h with
  | fixed h =>
    simp only [fixedZFTheory, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, 0, 0, rfl⟩
    · exact ⟨1, 0, 0, rfl⟩
    · exact ⟨2, 0, 0, rfl⟩
    · exact ⟨3, 0, 0, rfl⟩
    · exact ⟨4, 0, 0, rfl⟩
    · exact ⟨5, 0, 0, rfl⟩
    · exact ⟨6, 0, 0, rfl⟩
    · exact ⟨7, 0, 0, rfl⟩
  | separation k φ => exact ⟨8, k, Semiformula.toNat φ, by simp [generatedAxiomAt, Semiformula.ofNat_toNat]⟩
  | replacement k φ => exact ⟨9, k, Semiformula.toNat φ, by simp [generatedAxiomAt, Semiformula.ofNat_toNat]⟩
  | vopenka φ => exact ⟨10, 0, Semiformula.toNat φ, by simp [generatedAxiomAt, Semiformula.ofNat_toNat]⟩

theorem generatedAxiomEnumeration_iff (φ : SetTheorySentence) :
    (∃ e, generatedAxiomEnumeration e = some φ) ↔ φ ∈ generatedZFVPTheory := by
  constructor
  · rintro ⟨e, he⟩
    exact generatedAxiomAt_mem he
  · intro h
    obtain ⟨tag, k, e, he⟩ := generatedAxiomAt_surjective h
    exact ⟨Nat.pair tag (Nat.pair k e), by simpa [generatedAxiomEnumeration] using he⟩

end ZFVP
