import ZFVP.SetTheory.BoundedRelationDomain
import ZFVP.SetTheory.BoundedRelationRange
import ZFVP.SetTheory.FunctionComposition
import ZFVP.Syntax.BoundedTruthClauses

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedRelationCompositionCertificate : SetTheorySemisentence 6 :=
  “C f g D M E. (∀ p ∈ C, ∃ x ∈ D, ∃ z ∈ E, !boundedKpairFormula p x z) ∧
    (∀ x ∈ D, ∀ z ∈ E, !boundedPairMemberFormula C x z ↔
      ∃ y ∈ M, !boundedPairMemberFormula f x y ∧ !boundedPairMemberFormula g y z)”

theorem boundedRelationCompositionCertificate_bounded : IsBoundedSetFormula boundedRelationCompositionCertificate :=
  .and (.all (.bvar 0) (.exs (.bvar 4) (.exs (.bvar 7) (boundedKpairFormula_bounded.subst _))))
    (.all (.bvar 3) (.all (.bvar 6) ((boundedPairMemberFormula_bounded.subst _).iff
      (.exs (.bvar 6) (.and (boundedPairMemberFormula_bounded.subst _) (boundedPairMemberFormula_bounded.subst _))))))

def sigmaOneRelationCompositionFormula : SetTheorySemisentence 3 :=
  “C f g. ∃ D, !boundedRelationDomainFormula D f ∧ ∃ M, !boundedRangeFormula M f ∧
    ∃ E, !boundedRangeFormula E g ∧ !boundedRelationCompositionCertificate C f g D M E”

def piOneRelationCompositionFormula : SetTheorySemisentence 3 :=
  “C f g. ∀ D, !boundedRelationDomainFormula D f → ∀ M, !boundedRangeFormula M f →
    ∀ E, !boundedRangeFormula E g → !boundedRelationCompositionCertificate C f g D M E”

theorem sigmaOneRelationCompositionFormula_sigmaOne : IsSigmaFormula 1 sigmaOneRelationCompositionFormula :=
  .exs (.and (.bounded (boundedRelationDomainFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedRangeFormula_bounded.subst _))
      (.exs (.bounded (.and (boundedRangeFormula_bounded.subst _) (boundedRelationCompositionCertificate_bounded.subst _)))))))

theorem piOneRelationCompositionFormula_piOne : IsPiFormula 1 piOneRelationCompositionFormula :=
  .all (.or (.bounded (boundedRelationDomainFormula_bounded.subst _).neg)
    (.all (.or (.bounded (boundedRangeFormula_bounded.subst _).neg)
      (.all (.bounded (.or (boundedRangeFormula_bounded.subst _).neg (boundedRelationCompositionCertificate_bounded.subst _)))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedRelationCompositionCertificate (C f g : V) :
    boundedRelationCompositionCertificate.Evalb ![C, f, g, domain f, range f, range g] ↔ C = compose f g := by
  simp [boundedRelationCompositionCertificate]
  constructor
  · rintro ⟨hs, ht⟩
    apply mem_ext
    intro p
    constructor
    · intro hp
      obtain ⟨x, hx, z, hz, rfl⟩ := hs p hp
      obtain ⟨y, _, hxy, hyz⟩ := (ht x hx z hz).mp hp
      exact mem_compose_iff.mpr ⟨x, y, z, hxy, hyz, rfl⟩
    · intro hp
      obtain ⟨x, y, z, hxy, hyz, rfl⟩ := mem_compose_iff.mp hp
      exact (ht x (mem_domain_iff.mpr ⟨y, hxy⟩) z (mem_range_iff.mpr ⟨y, hyz⟩)).mpr
        ⟨y, mem_range_iff.mpr ⟨x, hxy⟩, hxy, hyz⟩
  · intro hC
    rw [hC]
    constructor
    · intro p hp
      obtain ⟨x, y, z, hxy, hyz, rfl⟩ := mem_compose_iff.mp hp
      exact ⟨x, mem_domain_iff.mpr ⟨y, hxy⟩, z, mem_range_iff.mpr ⟨y, hyz⟩, rfl⟩
    · intro x _ z _
      constructor
      · intro hxz
        obtain ⟨a, y, b, hay, hyb, he⟩ := mem_compose_iff.mp hxz
        have hab : x = a ∧ z = b := by simpa using he
        obtain ⟨rfl, rfl⟩ := hab
        exact ⟨y, mem_range_iff.mpr ⟨x, hay⟩, hay, hyb⟩
      · rintro ⟨y, _, hxy, hyz⟩
        exact mem_compose_iff.mpr ⟨x, y, z, hxy, hyz, rfl⟩

instance sigmaOneRelationCompositionFormula_defined : ℒₛₑₜ-function₂[V] compose via sigmaOneRelationCompositionFormula :=
  ⟨fun v ↦ by
    have he := eval_boundedRelationCompositionCertificate (V := V)
    simp only [Semiformula.Evalb] at he
    simp [sigmaOneRelationCompositionFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, he]⟩

instance piOneRelationCompositionFormula_defined : ℒₛₑₜ-function₂[V] compose via piOneRelationCompositionFormula :=
  ⟨fun v ↦ by
    have he := eval_boundedRelationCompositionCertificate (V := V)
    simp only [Semiformula.Evalb] at he
    simp [piOneRelationCompositionFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, he]⟩

end ZFVP
