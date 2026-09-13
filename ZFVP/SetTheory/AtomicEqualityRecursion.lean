import ZFVP.SetTheory.SubnameRecursion
import ZFVP.SetTheory.ForcingOrder

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The two density clauses for equality, using previously computed equality sets. -/
def AtomicEqualityTest (P R : V) (E : V → V → V) (σ τ p : V) : Prop :=
  (∀ υ s, ⟨υ, s⟩ₖ ∈ σ → ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨q, s⟩ₖ ∈ R →
    ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ ∃ ν t, ⟨ν, t⟩ₖ ∈ τ ∧ ⟨r, t⟩ₖ ∈ R ∧ r ∈ E υ ν) ∧
  (∀ ν t, ⟨ν, t⟩ₖ ∈ τ → ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨q, t⟩ₖ ∈ R →
    ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ ∃ υ s, ⟨υ, s⟩ₖ ∈ σ ∧ ⟨r, s⟩ₖ ∈ R ∧ r ∈ E υ ν)

set_option maxHeartbeats 800000 in
instance atomicEqualityTest_definable (P R : V) :
    ℒₛₑₜ-relation₄[V] (fun σ τ f p ↦ AtomicEqualityTest P R (fun υ ν ↦ (f ‘ υ) ‘ ν) σ τ p) := by
  unfold AtomicEqualityTest
  definability

noncomputable def atomicEqualityConditions (P R σ τ f : V) : V :=
  sep P (fun p ↦ AtomicEqualityTest P R (fun υ ν ↦ (f ‘ υ) ‘ ν) σ τ p) (by definability)

instance atomicEqualityConditions_definable (P R : V) :
    ℒₛₑₜ-function₃[V] (atomicEqualityConditions P R) := by
  have h : ℒₛₑₜ-relation₄ (fun z σ τ f : V ↦ ∀ p,
      p ∈ z ↔ p ∈ P ∧ AtomicEqualityTest P R (fun υ ν ↦ (f ‘ υ) ‘ ν) σ τ p) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = atomicEqualityConditions P R (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [atomicEqualityConditions, AtomicEqualityTest, mem_sep_iff]

noncomputable def atomicEqualityRowStep (P R C σ f : V) : V :=
  definableGraph C (fun τ ↦ atomicEqualityConditions P R σ τ f) (by definability)

instance atomicEqualityRowStep_definable (P R : V) :
    ℒₛₑₜ-function₃[V] (atomicEqualityRowStep P R) := by
  have h : ℒₛₑₜ-relation₄ (fun g C σ f : V ↦
      ∀ z, z ∈ g ↔ ∃ τ ∈ C, z = ⟨τ, atomicEqualityConditions P R σ τ f⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = atomicEqualityRowStep P R (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [atomicEqualityRowStep, mem_definableGraph_iff]

noncomputable def atomicEqualityRows (P R C σ : V) : V :=
  subnameRecursion (atomicEqualityRowStep P R C) (by definability) σ

instance atomicEqualityRows_definable (P R : V) : ℒₛₑₜ-function₂[V] (atomicEqualityRows P R) := by
  have h : ℒₛₑₜ-relation₃ (fun y C σ : V ↦ ∃ f,
      IsSubnameRecursion (nameClosure σ) (atomicEqualityRowStep P R C) f ∧ y = f ‘ σ) := by
    unfold IsSubnameRecursion
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = atomicEqualityRows P R (v 1) (v 2) ↔ _
  constructor
  · intro he
    exact ⟨subnameRecursionTable (atomicEqualityRowStep P R (v 1)) (by definability) (v 2),
      subnameRecursionTable_spec _ _ _, he⟩
  · rintro ⟨f, hf, hv⟩
    have he := (subnameRecursionTable_eq_iff (atomicEqualityRowStep P R (v 1)) (by definability) (v 2) f).mpr hf
    exact hv.trans (congrArg (fun g ↦ g ‘ (v 2)) he)

noncomputable def atomicEqualityAt (P R C σ τ : V) : V := (atomicEqualityRows P R C σ) ‘ τ

instance atomicEqualityAt_definable (P R : V) : ℒₛₑₜ-function₃[V] (atomicEqualityAt P R) := by
  unfold atomicEqualityAt
  definability

theorem atomicEqualityAt_step (P R C σ : V) {τ : V} (hτ : τ ∈ C) :
    atomicEqualityAt P R C σ τ = atomicEqualityConditions P R σ τ
      (definableGraph (domain σ) (atomicEqualityRows P R C) (by definability)) := by
  unfold atomicEqualityAt atomicEqualityRows
  rw [subnameRecursion_equation]
  exact value_definableGraph _ _ _ hτ

theorem atomicEqualityTest_congr (P R σ τ p : V) (E E' : V → V → V)
    (h : ∀ υ s, ⟨υ, s⟩ₖ ∈ σ → ∀ ν t, ⟨ν, t⟩ₖ ∈ τ → E υ ν = E' υ ν) :
    AtomicEqualityTest P R E σ τ p ↔ AtomicEqualityTest P R E' σ τ p := by
  unfold AtomicEqualityTest
  constructor <;> rintro ⟨hl, hr⟩ <;> constructor
  · intro υ s hs q hq hqp hqs
    obtain ⟨r, hr, hrq, ν, t, ht, hrt, he⟩ := hl υ s hs q hq hqp hqs
    exact ⟨r, hr, hrq, ν, t, ht, hrt, h υ s hs ν t ht ▸ he⟩
  · intro ν t ht q hq hqp hqt
    obtain ⟨r, hr, hrq, υ, s, hs, hrs, he⟩ := hr ν t ht q hq hqp hqt
    exact ⟨r, hr, hrq, υ, s, hs, hrs, h υ s hs ν t ht ▸ he⟩
  · intro υ s hs q hq hqp hqs
    obtain ⟨r, hr, hrq, ν, t, ht, hrt, he⟩ := hl υ s hs q hq hqp hqs
    exact ⟨r, hr, hrq, ν, t, ht, hrt, (h υ s hs ν t ht).symm ▸ he⟩
  · intro ν t ht q hq hqp hqt
    obtain ⟨r, hr, hrq, υ, s, hs, hrs, he⟩ := hr ν t ht q hq hqp hqt
    exact ⟨r, hr, hrq, υ, s, hs, hrs, (h υ s hs ν t ht).symm ▸ he⟩

theorem mem_atomicEqualityAt_iff (P R C σ p : V) {τ : V} (hτ : τ ∈ C) :
    p ∈ atomicEqualityAt P R C σ τ ↔ p ∈ P ∧
      AtomicEqualityTest P R (atomicEqualityAt P R C) σ τ p := by
  rw [atomicEqualityAt_step P R C σ hτ]
  simp only [atomicEqualityConditions, AtomicEqualityTest, mem_sep_iff]
  change (p ∈ P ∧ AtomicEqualityTest P R
    (fun υ ν ↦ ((definableGraph (domain σ) (atomicEqualityRows P R C) (by definability)) ‘ υ) ‘ ν)
    σ τ p) ↔ _
  apply and_congr_right
  intro _
  apply atomicEqualityTest_congr
  intro υ s hs ν t _
  rw [value_definableGraph _ _ _ (mem_domain_of_kpair_mem hs)]
  rfl

end ZFVP
