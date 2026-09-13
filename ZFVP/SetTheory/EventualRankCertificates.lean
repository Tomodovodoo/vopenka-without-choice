import ZFVP.SetTheory.BoundedDomainParameters
import ZFVP.SetTheory.PiOneHierarchy
import ZFVP.SetTheory.PiOneRegularInaccessible

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Evaluate a fixed formula in every sufficiently high inaccessible rank.
The formula being evaluated can have arbitrary first-order complexity. -/
def eventualRankCertificate (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “z x. ∃ η, !IsOrdinal.dfn η ∧ ∀ ξ, η ∈ ξ → !rankCriterionFormula ξ →
    ∀ D, !piOneHierarchyFormula D ξ →
      z ∈ D ∧ x ∈ D ∧ !(boundedDomainParametersFormula φ) D z x”

theorem eventualRankCertificate_sigmaThree (φ : SetTheorySemisentence 2) :
    IsSigmaFormula 3 (eventualRankCertificate φ) := by
  apply IsLevyFormula.exs
  apply IsLevyFormula.and (.bounded (isOrdinalFormula_bounded.subst _))
  apply IsLevyFormula.raise
  apply IsLevyFormula.all
  apply IsLevyFormula.or (.bounded (.nrel _ _))
  apply IsLevyFormula.or
  · exact (rankCriterionFormula_piOne.subst _).neg.raise
  · apply IsLevyFormula.all
    apply IsLevyFormula.or (piOneHierarchyFormula_piOne.subst _).neg.raise
    exact .bounded (.and (.rel _ _) (.and (.rel _ _)
      ((boundedDomainParametersFormula_bounded φ).subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def RankCertificateHolds (φ : SetTheorySemisentence 2) (z x ξ : V) : Prop :=
  z ∈ hierarchy ξ ∧ x ∈ hierarchy ξ ∧
    (boundedDomainParametersFormula φ).Evalb ![hierarchy ξ, z, x]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_boundedDomainParametersFormula_two (φ : SetTheorySemisentence 2)
    (A : V) (z x : SetDomain A) :
    (boundedDomainParametersFormula φ).Evalb ![A, z.val, x.val] ↔ φ.Evalb ![z, x] := by
  have he := eval_boundedDomainParametersFormula φ A ![z, x]
  have hv : (fun i : Fin 2 ↦ ((![z, x] : Fin 2 → SetDomain A) i).val) = ![z.val, x.val] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j ↦ Fin.elim0 j)) i
  simpa only [hv] using he

theorem rankCertificateHolds_iff_of_graph (φ : SetTheorySemisentence 2) (ξ z : V)
    (x y : SetDomain (hierarchy ξ))
    (he : ∀ w : SetDomain (hierarchy ξ), φ.Evalb ![w, x] ↔ w = y) :
    RankCertificateHolds φ z x.val ξ ↔ z = y.val := by
  constructor
  · rintro ⟨hz, _, hb⟩
    have hw := (eval_boundedDomainParametersFormula_two φ (hierarchy ξ) ⟨z, hz⟩ x).mp hb
    exact congrArg Subtype.val ((he _).mp hw)
  · intro hz
    subst z
    exact ⟨y.property, x.property,
      (eval_boundedDomainParametersFormula_two φ (hierarchy ξ) y x).mpr ((he y).mpr rfl)⟩

theorem eval_eventualRankCertificate_raw (φ : SetTheorySemisentence 2) (z x : V) :
    (eventualRankCertificate φ).Evalb ![z, x] ↔
      ∃ η : V, IsOrdinal η ∧ ∀ ξ : V, η ∈ ξ → IsChoicelessInaccessible ξ →
        RankCertificateHolds φ z x ξ := by
  have he : (eventualRankCertificate φ).Evalb ![z, x] ↔
      ∃ η : V, IsOrdinal η ∧ ∀ ξ : V, η ∈ ξ → IsChoicelessInaccessible ξ →
        ∀ D : V, IsHierarchySegment D ξ →
          z ∈ D ∧ x ∈ D ∧ (boundedDomainParametersFormula φ).Evalb ![D, z, x] := by
    simp [eventualRankCertificate, Semiformula.Evalb, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
      rankCriterionHeight_iff_choicelessInaccessible]
  rw [he]
  constructor
  · rintro ⟨η, ho, h⟩
    exact ⟨η, ho, fun ξ hη hξ ↦ h ξ hη hξ (hierarchy ξ) ⟨hξ.1, rfl⟩⟩
  · rintro ⟨η, ho, h⟩
    refine ⟨η, ho, fun ξ hη hξ D hD ↦ ?_⟩
    obtain ⟨_, rfl⟩ := hD
    exact h ξ hη hξ

theorem eval_eventualRankCertificate (φ : SetTheorySemisentence 2) (z x : V) :
    (eventualRankCertificate φ).Evalb ![z, x] ↔
      ∃ η : V, IsOrdinal η ∧ ∀ ξ : V, η ∈ ξ → IsChoicelessInaccessible ξ →
        ∃ (hz : z ∈ hierarchy ξ) (hx : x ∈ hierarchy ξ),
          φ.Evalb (![⟨z, hz⟩, ⟨x, hx⟩] : Fin 2 → SetDomain (hierarchy ξ)) := by
  have hrel (D : V) :
      z ∈ D ∧ x ∈ D ∧ (boundedDomainParametersFormula φ).Evalb ![D, z, x] ↔
        ∃ (hz : z ∈ D) (hx : x ∈ D), φ.Evalb (![⟨z, hz⟩, ⟨x, hx⟩] : Fin 2 → SetDomain D) := by
    have hev (hz : z ∈ D) (hx : x ∈ D) :=
      eval_boundedDomainParametersFormula φ D (![⟨z, hz⟩, ⟨x, hx⟩] : Fin 2 → SetDomain D)
    have hv (hz : z ∈ D) (hx : x ∈ D) :
        (fun i : Fin 2 ↦ ((![⟨z, hz⟩, ⟨x, hx⟩] : Fin 2 → SetDomain D) i).val) = ![z, x] := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (fun j ↦ Fin.elim0 j)) i
    simp only [hv] at hev
    constructor
    · rintro ⟨hz, hx, he⟩
      exact ⟨hz, hx, (hev hz hx).mp he⟩
    · rintro ⟨hz, hx, he⟩
      exact ⟨hz, hx, (hev hz hx).mpr he⟩
  have he : (eventualRankCertificate φ).Evalb ![z, x] ↔
      ∃ η : V, IsOrdinal η ∧ ∀ ξ : V, η ∈ ξ → IsChoicelessInaccessible ξ →
        ∀ D : V, IsHierarchySegment D ξ →
          z ∈ D ∧ x ∈ D ∧ (boundedDomainParametersFormula φ).Evalb ![D, z, x] := by
    simp [eventualRankCertificate, Semiformula.Evalb, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
      rankCriterionHeight_iff_choicelessInaccessible]
  rw [he]
  constructor
  · rintro ⟨η, ho, h⟩
    refine ⟨η, ho, fun ξ hη hξ ↦ ?_⟩
    exact (hrel _).mp (h ξ hη hξ (hierarchy ξ) ⟨hξ.1, rfl⟩)
  · rintro ⟨η, ho, h⟩
    refine ⟨η, ho, fun ξ hη hξ D hD ↦ ?_⟩
    obtain ⟨_, rfl⟩ := hD
    exact (hrel _).mpr (h ξ hη hξ)

end ZFVP
