import ZFVP.ModelTheory.ForcingGeneric
import ZFVP.SetTheory.ForcingQuantifiers

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def GenericMeets (G : Set V) (A : V) : Prop := ∃ p ∈ G, p ∈ A

theorem forcing_decisions_dense {P R A : V} (hR : IsForcingPreorder P R) (hAP : A ⊆ P) :
    ForcingDense P R (A ∪ forcingNegation P R A) := by
  classical
  refine ⟨?_, ?_⟩
  · intro p hp
    rcases mem_union_iff.mp hp with hpA | hpN
    · exact hAP p hpA
    · exact forcingNegation_subset _ _ _ p hpN
  · intro p hp
    by_cases h : ∃ q ∈ A, ⟨q, p⟩ₖ ∈ R
    · obtain ⟨q, hqA, hqp⟩ := h
      exact ⟨q, mem_union_iff.mpr (Or.inl hqA), hqp⟩
    · exact ⟨p, mem_union_iff.mpr (Or.inr ((mem_forcingNegation_iff _ _ _ _).mpr
        ⟨hp, fun q _ hqp hqA ↦ h ⟨q, hqA, hqp⟩⟩)), hR.2.1 p hp⟩

theorem genericMeets_negation {P R A : V} {G : Set V} (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (hAP : A ⊆ P) (hA : IsForcingDownwardClosed P R A) :
    GenericMeets G (forcingNegation P R A) ↔ ¬GenericMeets G A := by
  constructor
  · rintro ⟨p, hpG, hpN⟩ ⟨q, hqG, hqA⟩
    obtain ⟨r, hrG, hrp, hrq⟩ := hG.1.2.2.2 p hpG q hqG
    exact ((mem_forcingNegation_iff _ _ _ _).mp hpN).2 r (hG.1.1 r hrG) hrp
      (hA q hqA r (hG.1.1 r hrG) hrq)
  · intro hn
    obtain ⟨p, hpG, hpD⟩ := hG.2 _ (forcing_decisions_dense hR hAP)
    rcases mem_union_iff.mp hpD with hpA | hpN
    · exact False.elim (hn ⟨p, hpG, hpA⟩)
    · exact ⟨p, hpG, hpN⟩

theorem genericMeets_closure {P R A : V} {G : Set V} (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (hAP : A ⊆ P) (hA : IsForcingDownwardClosed P R A) :
    GenericMeets G (forcingClosure P R A) ↔ GenericMeets G A := by
  constructor
  · rintro ⟨p, hpG, hpC⟩
    exact externalForcingGeneric_meets_denseBelow hR hG hpG
      ⟨hAP, ((mem_forcingClosure_iff _ _ _ _).mp hpC).2⟩
  · rintro ⟨p, hpG, hpA⟩
    exact ⟨p, hpG, subset_forcingClosure hR hAP hA p hpA⟩

theorem genericMeets_inter {P R A B : V} {G : Set V} (hG : IsExternalForcingFilter P R G)
    (hA : IsForcingDownwardClosed P R A) (hB : IsForcingDownwardClosed P R B) :
    GenericMeets G (A ∩ B) ↔ GenericMeets G A ∧ GenericMeets G B := by
  constructor
  · rintro ⟨p, hpG, hpAB⟩
    exact ⟨⟨p, hpG, (mem_inter_iff.mp hpAB).1⟩, ⟨p, hpG, (mem_inter_iff.mp hpAB).2⟩⟩
  · rintro ⟨⟨p, hpG, hpA⟩, ⟨q, hqG, hqB⟩⟩
    obtain ⟨r, hrG, hrp, hrq⟩ := hG.2.2.2 p hpG q hqG
    exact ⟨r, hrG, mem_inter_iff.mpr
      ⟨hA p hpA r (hG.1 r hrG) hrp, hB q hqB r (hG.1 r hrG) hrq⟩⟩

theorem genericMeets_union {A B : V} {G : Set V} :
    GenericMeets G (A ∪ B) ↔ GenericMeets G A ∨ GenericMeets G B := by
  simp only [GenericMeets, mem_union_iff]
  aesop

theorem genericMeets_classUnion {P R : V} {G : Set V} (hG : IsExternalForcingFilter P R G)
    (N : V → Prop) (hN : ℒₛₑₜ-predicate N) (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    GenericMeets G (forcingClassUnion P N hN F hF) ↔ ∃ x, N x ∧ GenericMeets G (F x) := by
  constructor
  · rintro ⟨p, hpG, hpU⟩
    obtain ⟨_, x, hx, hpF⟩ := (mem_forcingClassUnion_iff _ _ _ _ _ _).mp hpU
    exact ⟨x, hx, p, hpG, hpF⟩
  · rintro ⟨x, hx, p, hpG, hpF⟩
    exact ⟨p, hpG, (mem_forcingClassUnion_iff _ _ _ _ _ _).mpr ⟨hG.1 p hpG, x, hx, hpF⟩⟩

theorem genericMeets_classIntersection {P R : V} {G : Set V} (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (hreg : ∀ x, N x → IsForcingRegular P R (F x)) :
    GenericMeets G (forcingClassIntersection P N hN F hF) ↔ ∀ x, N x → GenericMeets G (F x) := by
  constructor
  · rintro ⟨p, hpG, hpI⟩ x hx
    exact ⟨p, hpG, ((mem_forcingClassIntersection_iff _ _ _ _ _ _).mp hpI).2 x hx⟩
  · intro hall
    rw [forcingClassIntersection_eq_negation hR N hN F hF hreg]
    apply (genericMeets_negation hR hG (forcingClassUnion_subset _ _ _ _ _)
      (forcingClassUnion_downward N hN _ _
        (fun x _ ↦ fun _ hp _ hq hqp ↦ forcingNegation_mono hR hp hq hqp))).mpr
    intro hmeet
    obtain ⟨x, hx, hxN⟩ := (genericMeets_classUnion hG.1 N hN _ _).mp hmeet
    exact (genericMeets_negation hR hG (hreg x hx).1 (hreg x hx).2.1).mp hxN (hall x hx)

theorem genericMeets_existential {P R : V} {G : Set V} (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (hdown : ∀ x, N x → IsForcingDownwardClosed P R (F x)) :
    GenericMeets G (forcingExistential P R N hN F hF) ↔ ∃ x, N x ∧ GenericMeets G (F x) := by
  rw [forcingExistential, genericMeets_closure hR hG (forcingClassUnion_subset _ _ _ _ _)
    (forcingClassUnion_downward N hN F hF hdown)]
  exact genericMeets_classUnion hG.1 N hN F hF

end ZFVP
