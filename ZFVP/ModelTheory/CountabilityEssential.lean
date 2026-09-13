import ZFVP.ModelTheory.WeaklyRubinDeadEnd
import ZFVP.SetTheory.ChoiceDictionary

/-! The model-theoretic half of the paper's Proposition `prop:countability-essential`.

Starting from a countable model of `ZF` together with the Vopenka scheme and the failure of
choice, we produce a model `N` of cardinality `ℵ₁` with the same three properties which has no
proper end extension to a model of `ZF`.

Two inputs are used but not proved here, and both appear as named hypotheses of every theorem
that uses them:

* `RubinShelahSchmerl` is Enayat's Theorem 5.17 (Rubin, Shelah, Schmerl): every countable model
  of `ZF` has an elementary extension of cardinality `ℵ₁` that is weakly Rubin.
* `NoConservativeProperEndExtension` (from `ZFVP.ModelTheory.WeaklyRubinDeadEnd`) is Enayat's
  Theorem 5.1: a model of `ZF` has no conservative proper end extension satisfying `ZF`.

What is proved here is the model-theoretic statement `IsZFDeadEnd N`: no proper end extension of
`N` satisfies `ZF`. The paper's phrasing, "no proper generic extension satisfying `ZF`", needs the
forcing half of the argument, which is separate from this file: a quotient-of-names extension that
adds a set is a proper end extension, so `IsZFDeadEnd.false_of_new_element` applied to that end
extension rules it out. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-- An elementary extension of `M` of cardinality `ℵ₁` that is weakly Rubin. This is the object
Enayat's Theorem 5.17 produces from a countable `M`. -/
structure AlephOneWeaklyRubinExtension (M : Type u) [SetStructure M] [Nonempty M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] where
  /-- The larger model. -/
  Model : Type u
  [setStructure : SetStructure Model]
  [nonempty : Nonempty Model]
  [modelsZF : Model↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  /-- The larger model has cardinality `ℵ₁`. -/
  card : Cardinal.mk Model = Cardinal.aleph 1
  /-- The larger model is weakly Rubin in the sense of Enayat's Definition 5.16. -/
  weaklyRubin : IsWeaklyRubin Model
  /-- `M` embeds elementarily into it. -/
  embedding : ElementaryMap M Model

attribute [instance] AlephOneWeaklyRubinExtension.setStructure
  AlephOneWeaklyRubinExtension.nonempty AlephOneWeaklyRubinExtension.modelsZF

/-- An elementary extension of `M` of cardinality `ℵ₁` with no proper end extension to a model
of `ZF`. -/
structure AlephOneDeadEndExtension (M : Type u) [SetStructure M] [Nonempty M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] where
  /-- The larger model. -/
  Model : Type u
  [setStructure : SetStructure Model]
  [nonempty : Nonempty Model]
  [modelsZF : Model↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  /-- The larger model has cardinality `ℵ₁`. -/
  card : Cardinal.mk Model = Cardinal.aleph 1
  /-- `M` embeds elementarily into it. -/
  embedding : ElementaryMap M Model
  /-- No proper end extension of it satisfies `ZF`. -/
  deadEnd : IsZFDeadEnd Model

attribute [instance] AlephOneDeadEndExtension.setStructure
  AlephOneDeadEndExtension.nonempty AlephOneDeadEndExtension.modelsZF

/-- Enayat's Theorem 5.17 (Rubin, Shelah, Schmerl): every countable model of `ZF` has an
elementary extension of cardinality `ℵ₁` that is weakly Rubin. This development does not prove it;
it is stated so that everything depending on it carries it as a visible hypothesis. -/
def RubinShelahSchmerl.{v} : Prop :=
  ∀ (M : Type v) [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M],
    Nonempty (AlephOneWeaklyRubinExtension M)

/-- A countable model of `ZF` has an elementary extension of cardinality `ℵ₁` with no proper end
extension to a model of `ZF`. Both unproved inputs, Enayat's Theorems 5.17 and 5.1, are
hypotheses. -/
theorem exists_zf_dead_end_of_countable (h517 : RubinShelahSchmerl.{u})
    (h51 : NoConservativeProperEndExtension.{u}) (M : Type u) [SetStructure M] [Nonempty M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M] : Nonempty (AlephOneDeadEndExtension M) := by
  obtain ⟨E⟩ := h517 M
  exact ⟨{ Model := E.Model
           card := E.card
           embedding := E.embedding
           deadEnd := E.weaklyRubin.isZFDeadEnd h51 }⟩

/-- The model-theoretic half of the paper's Proposition `prop:countability-essential`. From a
countable model of `ZF` satisfying every instance of the Vopenka scheme and failing internal
choice, we get a model `N` of cardinality `ℵ₁` with the same three properties and with no proper
end extension to a model of `ZF`.

The paper states the conclusion as "no proper generic extension satisfying `ZF`". Getting there
from `IsZFDeadEnd N` is the forcing half of the argument, which lives outside this file: a
quotient-of-names extension that adds a set is a proper end extension of `N`, so
`IsZFDeadEnd.false_of_new_element` applied to it gives a contradiction.

Enayat's Theorem 5.17 (`h517`) and his Theorem 5.1 (`h51`) are hypotheses; this development does
not prove either. -/
theorem countability_essential (h517 : RubinShelahSchmerl.{u})
    (h51 : NoConservativeProperEndExtension.{u}) (M : Type u) [SetStructure M] [Nonempty M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := M) φ)
    (hAC : ¬ InternalChoice M) :
    ∃ E : AlephOneDeadEndExtension M,
      (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := E.Model) φ) ∧
        ¬ InternalChoice E.Model := by
  obtain ⟨E⟩ := h517 M
  refine ⟨{ Model := E.Model
            card := E.card
            embedding := E.embedding
            deadEnd := E.weaklyRubin.isZFDeadEnd h51 }, ?_, ?_⟩
  · exact E.embedding.vopenkaScheme hVP
  · exact fun h ↦ hAC ((E.embedding.internalChoice_iff).mpr h)

end ZFVP
