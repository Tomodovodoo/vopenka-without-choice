import ZFVP.ModelTheory.SchmerlInternalInfinitaryInduction
import ZFVP.ModelTheory.SchmerlEndExtensionFragmentCoding

/-! Derived Boolean codes use functions on the model's entire omega. Their
equations and end-extension transport do not require standard omega. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def binaryCodeValue (φ ψ i : V) : V := by
  classical
  exact if i = 0 then φ else ψ

instance binaryCodeValue_definable : ℒₛₑₜ-function₃[V] binaryCodeValue := by
  have h : ℒₛₑₜ-relation₄[V] (fun z φ ψ i ↦ (i = 0 ∧ z = φ) ∨ (i ≠ 0 ∧ z = ψ)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = binaryCodeValue (v 1) (v 2) (v 3) ↔ _
  unfold binaryCodeValue
  split <;> simp_all

noncomputable def binaryCodeSequence (φ ψ : V) : V :=
  definableGraph (ω : V) (binaryCodeValue φ ψ) (by definability)

instance binaryCodeSequence_definable : ℒₛₑₜ-function₂[V] binaryCodeSequence := by
  have h : ℒₛₑₜ-relation₃[V] (fun f φ ψ ↦ ∀ p, p ∈ f ↔
      ∃ i ∈ (ω : V), p = ⟨i, binaryCodeValue φ ψ i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = binaryCodeSequence (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [binaryCodeSequence, mem_definableGraph_iff]

instance binaryCodeSequence_isFunction (φ ψ : V) : IsFunction (binaryCodeSequence φ ψ) :=
  inferInstanceAs (IsFunction (definableGraph _ _ _))

@[simp] theorem domain_binaryCodeSequence (φ ψ : V) :
    domain (binaryCodeSequence φ ψ) = (ω : V) := domain_definableGraph _ _ _

theorem value_binaryCodeSequence (φ ψ : V) {i : V} (hi : i ∈ (ω : V)) :
    (binaryCodeSequence φ ψ) ‘ i = binaryCodeValue φ ψ i :=
  value_definableGraph _ _ _ hi

@[simp] theorem binaryCodeSequence_zero (φ ψ : V) :
    (binaryCodeSequence φ ψ) ‘ (0 : V) = φ := by
  simp [value_binaryCodeSequence φ ψ (i := 0) (by simp), binaryCodeValue]

@[simp] theorem binaryCodeSequence_one (φ ψ : V) :
    (binaryCodeSequence φ ψ) ‘ (1 : V) = ψ := by
  rw [value_binaryCodeSequence φ ψ (i := 1) (by simp)]
  simp [binaryCodeValue, OfNat.ofNat, internalNumeral_eq_iff]

noncomputable def andCode (φ ψ : V) : V := conjCode (binaryCodeSequence φ ψ)
noncomputable def impCode (φ ψ : V) : V := negCode (andCode (negCode (negCode φ)) (negCode ψ))

instance andCode_definable : ℒₛₑₜ-function₂[V] andCode := by unfold andCode; definability
instance impCode_definable : ℒₛₑₜ-function₂[V] impCode := by unfold impCode; definability

theorem IsFragment.neg_mem {L F n φ : V} (hF : IsFragment L F)
    (hφ : ⟨n, negCode φ⟩ₖ ∈ F) : ⟨n, φ⟩ₖ ∈ F :=
  hF.immediate_mem hφ ((immediate_neg_iff _ _ _).mpr rfl)

theorem IsFragment.conj_data {L F n f : V} (hF : IsFragment L F)
    (hf : ⟨n, conjCode f⟩ₖ ∈ F) :
    IsFunction f ∧ domain f = (ω : V) ∧ ∀ i ∈ (ω : V), ⟨n, f ‘ i⟩ₖ ∈ F := by
  have h := (hF.node hf).2
  simpa [foCode, negCode, conjCode, exsCode, qCode, OfNat.ofNat, internalNumeral_eq_iff] using h

theorem IsFragment.and_left_mem {L F n φ ψ : V} (hF : IsFragment L F)
    (h : ⟨n, andCode φ ψ⟩ₖ ∈ F) : ⟨n, φ⟩ₖ ∈ F := by
  simpa only [binaryCodeSequence_zero] using
    (hF.conj_data h).2.2 (0 : V) (by simp)

theorem IsFragment.and_right_mem {L F n φ ψ : V} (hF : IsFragment L F)
    (h : ⟨n, andCode φ ψ⟩ₖ ∈ F) : ⟨n, ψ⟩ₖ ∈ F := by
  simpa only [binaryCodeSequence_one] using
    (hF.conj_data h).2.2 (1 : V) (by simp)

theorem IsFragment.imp_left_mem {L F n φ ψ : V} (hF : IsFragment L F)
    (h : ⟨n, impCode φ ψ⟩ₖ ∈ F) : ⟨n, φ⟩ₖ ∈ F :=
  hF.neg_mem (hF.neg_mem (hF.and_left_mem (hF.neg_mem h)))

theorem IsFragment.imp_right_mem {L F n φ ψ : V} (hF : IsFragment L F)
    (h : ⟨n, impCode φ ψ⟩ₖ ∈ F) : ⟨n, ψ⟩ₖ ∈ F :=
  hF.neg_mem (hF.and_right_mem (hF.neg_mem h))

theorem holds_and {L F M n φ ψ b : V} (hF : IsFragment L F)
    (h : ⟨n, andCode φ ψ⟩ₖ ∈ F) (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n (andCode φ ψ) b ↔ Holds L F M n φ b ∧ Holds L F M n ψ b := by
  rw [andCode, holds_conj hF h hb]
  constructor
  · intro hh
    exact ⟨by simpa only [binaryCodeSequence_zero] using hh 0 (by simp),
      by simpa only [binaryCodeSequence_one] using hh 1 (by simp)⟩
  · rintro ⟨hφ, hψ⟩ i hi
    rw [value_binaryCodeSequence _ _ hi, binaryCodeValue]
    split <;> assumption

theorem holds_imp {L F M n φ ψ b : V} (hF : IsFragment L F)
    (h : ⟨n, impCode φ ψ⟩ₖ ∈ F) (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n (impCode φ ψ) b ↔ (Holds L F M n φ b → Holds L F M n ψ b) := by
  have ha := hF.neg_mem h
  have hl := hF.and_left_mem ha
  have hr := hF.and_right_mem ha
  rw [impCode, holds_neg hF h hb, holds_and hF ha hb,
    holds_neg hF hl hb, holds_neg hF (hF.neg_mem hl) hb, holds_neg hF hr hb]
  tauto

namespace EndExtension

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem map_binaryCodeValue (φ ψ i : V) :
    j (binaryCodeValue φ ψ i) = binaryCodeValue (j φ) (j ψ) (j i) := by
  have hzero : j (0 : V) = (0 : W) := j.map_numeral 0
  have hz : j i = (0 : W) ↔ i = (0 : V) := by rw [← hzero, j.injective.eq_iff]
  unfold binaryCodeValue
  split_ifs <;> tauto

@[simp] theorem map_binaryCodeSequence (φ ψ : V) :
    j (binaryCodeSequence φ ψ) = binaryCodeSequence (j φ) (j ψ) := by
  have h := j.map_definableGraph (ω : V) (binaryCodeValue φ ψ) (binaryCodeValue (j φ) (j ψ))
    (by definability) (by definability) (fun i _ ↦ map_binaryCodeValue j φ ψ i)
  simpa only [binaryCodeSequence, j.map_omega] using h

@[simp] theorem map_andCode (φ ψ : V) : j (andCode φ ψ) = andCode (j φ) (j ψ) := by
  simp only [andCode, map_conjCode, map_binaryCodeSequence]

@[simp] theorem map_impCode (φ ψ : V) : j (impCode φ ψ) = impCode (j φ) (j ψ) := by
  simp only [impCode, map_negCode, map_andCode]

end EndExtension
end ZFVP.Infinitary.Internal
