import ZFVP.SetTheory.DefinableGraph

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The pair `⟨q,p⟩` in `R` means that `q` is stronger than `p`. -/
def IsForcingPreorder (P R : V) : Prop :=
  R ⊆ P ×ˢ P ∧ (∀ p ∈ P, ⟨p, p⟩ₖ ∈ R) ∧
    ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P,
      ⟨p, q⟩ₖ ∈ R → ⟨q, r⟩ₖ ∈ R → ⟨p, r⟩ₖ ∈ R

def IsForcingPoset (P R : V) : Prop :=
  IsForcingPreorder P R ∧
    ∀ p ∈ P, ∀ q ∈ P, ⟨p, q⟩ₖ ∈ R → ⟨q, p⟩ₖ ∈ R → p = q

def IsForcingTop (P R one : V) : Prop :=
  one ∈ P ∧ ∀ p ∈ P, ⟨p, one⟩ₖ ∈ R

instance isForcingTop_definable : ℒₛₑₜ-relation₃[V] IsForcingTop := by
  unfold IsForcingTop
  definability

def ForcingCompatible (P R p q : V) : Prop :=
  ∃ r ∈ P, ⟨r, p⟩ₖ ∈ R ∧ ⟨r, q⟩ₖ ∈ R

def ForcingDenseBelow (P R D p : V) : Prop :=
  D ⊆ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ D, ⟨r, q⟩ₖ ∈ R

def ForcingDense (P R D : V) : Prop :=
  D ⊆ P ∧ ∀ p ∈ P, ∃ q ∈ D, ⟨q, p⟩ₖ ∈ R

instance isForcingPreorder_definable : ℒₛₑₜ-relation[V] IsForcingPreorder := by
  unfold IsForcingPreorder
  definability

instance isForcingPoset_definable : ℒₛₑₜ-relation[V] IsForcingPoset := by
  unfold IsForcingPoset
  definability

instance forcingCompatible_definable : ℒₛₑₜ-relation₄[V] ForcingCompatible := by
  unfold ForcingCompatible
  definability

instance forcingDenseBelow_definable : ℒₛₑₜ-relation₄[V] ForcingDenseBelow := by
  unfold ForcingDenseBelow
  definability

instance forcingDense_definable : ℒₛₑₜ-relation₃[V] ForcingDense := by
  unfold ForcingDense
  definability

theorem forcingCompatible_symm {P R p q : V} (h : ForcingCompatible P R p q) :
    ForcingCompatible P R q p := by
  obtain ⟨r, hr, hrp, hrq⟩ := h
  exact ⟨r, hr, hrq, hrp⟩

theorem forcingCompatible_of_stronger {P R p q r : V} (hR : IsForcingPreorder P R)
    (hp : p ∈ P) (hq : q ∈ P) (_hr : r ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R)
    (h : ForcingCompatible P R q r) : ForcingCompatible P R p r := by
  obtain ⟨s, hs, hsq, hsr⟩ := h
  exact ⟨s, hs, hR.2.2 s hs q hq p hp hsq hqp, hsr⟩

theorem forcingDense_below {P R D p : V} (hD : ForcingDense P R D) :
    ForcingDenseBelow P R D p :=
  ⟨hD.1, fun q hq _ ↦ hD.2 q hq⟩

theorem forcingDenseBelow_mono {P R D p q : V} (hR : IsForcingPreorder P R)
    (hp : p ∈ P) (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R)
    (hD : ForcingDenseBelow P R D p) : ForcingDenseBelow P R D q := by
  refine ⟨hD.1, fun r hr hrq ↦ ?_⟩
  exact hD.2 r hr (hR.2.2 r hr q hq p hp hrq hqp)

/-- An internal dense set extending a set dense below `p`. -/
noncomputable def forcingDenseExtension (P R D p : V) : V :=
  {q ∈ P ; q ∈ D ∨ ¬ForcingCompatible P R q p}

instance forcingDenseExtension_definable : ℒₛₑₜ-function₄[V] forcingDenseExtension := by
  have h : ℒₛₑₜ-relation₅[V] (fun E P R D p ↦
      ∀ q, q ∈ E ↔ q ∈ P ∧ (q ∈ D ∨ ¬ForcingCompatible P R q p)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingDenseExtension (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp [forcingDenseExtension]

theorem forcingDenseExtension_dense {P R D p : V} (hR : IsForcingPreorder P R)
    (hD : ForcingDenseBelow P R D p) : ForcingDense P R (forcingDenseExtension P R D p) := by
  classical
  refine ⟨fun q hq ↦ (mem_sep_iff.mp hq).1, fun q hq ↦ ?_⟩
  by_cases hc : ForcingCompatible P R q p
  · obtain ⟨r, hr, hrq, hrp⟩ := hc
    obtain ⟨s, hs, hsr⟩ := hD.2 r hr hrp
    exact ⟨s, mem_sep_iff.mpr ⟨hD.1 s hs, Or.inl hs⟩,
      hR.2.2 s (hD.1 s hs) r hr q hq hsr hrq⟩
  · exact ⟨q, mem_sep_iff.mpr ⟨hq, Or.inr hc⟩, hR.2.1 q hq⟩

end ZFVP
