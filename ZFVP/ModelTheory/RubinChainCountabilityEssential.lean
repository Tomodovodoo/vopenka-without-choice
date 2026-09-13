import ZFVP.ModelTheory.DeadEndModelAlephOne
import ZFVP.ModelTheory.RubinChainCriterion
import ZFVP.SetTheory.DiamondOmegaOne

/-! The top of Enayat's Theorem 5.17 chain, under `◊`, on a hypothesis the Appendix can deliver.

`ZFVP.ModelTheory.DiamondCountabilityEssential` used to run this chain from
`RubinExtensionUnderDiamond`, whose conclusion asked the extension to satisfy `IsRubin`, the
literal reading of Enayat's Definition 5.13. That property is refutable in ZF: `ZFVP.not_isRubin`
applies clause (a) to the ordinals under inclusion and then clause (b) to the maximal filter they
form over themselves, and a code for that filter is a set of all ordinals. So the old hypothesis
was false for every model, and it has been removed along with everything drawn from it; that file
is now a docstring only.

This file carries the chain instead, on `RubinChainUnderDiamond`, which asks for the object the
`ω₁`-length construction of Enayat's Appendix actually builds: a `RubinChain`, the increasing
chain of countable elementary submodels with the upper bound and reflection closure properties of
Stage 1. `ZFVP.ModelTheory.RubinChainCriterion` turns a `RubinChain W` into everything the
downstream argument needs, namely `Cardinal.mk W = ℵ₁` and `IsWeaklyRubin W`, so the four
conclusions come back unchanged with the new hypothesis in place of the old one.

Nothing here weakens what is proved elsewhere. Enayat's Theorem 5.1 is discharged in
`ZFVP.ModelTheory.NoConservativeEndExtension`, the step from the corrected Definition 5.13 to
Definition 5.16 in `ZFVP.ModelTheory.RubinDefinableFilters`, and the step from a weakly Rubin
model to a dead end model in `ZFVP.ModelTheory.WeaklyRubinDeadEnd`.

What is still open, and visible in every statement below:

* The construction of a `RubinChain` over a countable model, that is Stage 1 of Enayat's Appendix.
  It is the whole content of `RubinChainUnderDiamond`, and it is a hypothesis here.
* Schmerl's elimination of `◊`. Nothing in this file removes the `DiamondOmegaOne` hypothesis, so
  the results are conditional on `◊` as well.

There is no `sorry` and no new axiom here; both gaps are hypotheses of the theorems. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-! ### The replacement hypothesis -/

/-- Stage 1 of Enayat's Appendix: under `◊`, every countable model of `ZF` has an elementary
extension carrying a `RubinChain`, the `ω₁`-chain of countable elementary submodels with the
upper bound and reflection properties of the construction.

This development does not prove it. It is stated so that everything depending on it carries it as
a visible hypothesis, in the same style as `RubinShelahSchmerl`. Unlike `RubinExtensionUnderDiamond`
it is not refutable: `RubinChainCriterion` derives the corrected Definition 5.13 from a
`RubinChain`, not the literal one. -/
def RubinChainUnderDiamond.{v} : Prop :=
  DiamondOmegaOne →
    ∀ (M : Type v) [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M],
      ∃ (W : Type v) (_ : SetStructure W) (_ : Nonempty W) (_ : W↓[ℒₛₑₜ] ⊧* 𝗭𝗙),
        Nonempty (RubinChain W) ∧ Nonempty (ElementaryMap M W)

/-! ### The chain from Stage 1 to the dead end model -/

/-- A model carrying a `RubinChain`, with `M` elementarily inside it, is a weakly Rubin elementary
extension of `M` of cardinality `ℵ₁`. The cardinality is `RubinChain.mk_eq_alephOne` and the
weakly Rubin field is `RubinChain.isWeaklyRubin`. -/
theorem alephOneWeaklyRubinExtension_of_rubinChain {M : Type u} [SetStructure M] [Nonempty M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {W : Type u} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (C : RubinChain W) (j : ElementaryMap M W) : Nonempty (AlephOneWeaklyRubinExtension M) :=
  ⟨{ Model := W
     card := C.mk_eq_alephOne
     weaklyRubin := C.isWeaklyRubin
     embedding := j }⟩

/-- Enayat's Theorem 5.17 under `◊`, in the packaged form the later theorems consume: from Stage 1
of the Appendix and `◊`, every countable model of `ZF` has a weakly Rubin elementary extension of
cardinality `ℵ₁`. -/
theorem exists_weaklyRubin_elementary_extension_of_rubinChain
    (h : RubinChainUnderDiamond.{u}) (hdiamond : DiamondOmegaOne) (M : Type u) [SetStructure M]
    [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M] : Nonempty (AlephOneWeaklyRubinExtension M) := by
  obtain ⟨W, _, _, _, ⟨C⟩, ⟨j⟩⟩ := h hdiamond M
  exact alephOneWeaklyRubinExtension_of_rubinChain C j

/-- Enayat's Theorem 5.17 follows from Stage 1 of his Appendix together with `◊`. Schmerl's
argument, which removes `◊`, is not formalized here. -/
theorem rubinShelahSchmerl_of_rubinChain (h : RubinChainUnderDiamond.{u})
    (hdiamond : DiamondOmegaOne) : RubinShelahSchmerl.{u} :=
  fun M _ _ _ _ ↦ exists_weaklyRubin_elementary_extension_of_rubinChain h hdiamond M

/-- A countable model of `ZF` has an elementary extension of cardinality `ℵ₁` with no proper end
extension to a model of `ZF`, from Stage 1 of Enayat's Appendix and `◊`.

This is `exists_zf_dead_end_of_countable'` with Enayat's Theorem 5.17 replaced by the two inputs
it is assembled from, one of which, the `ω₁`-length construction, is still a hypothesis. -/
theorem exists_zf_dead_end_of_countable_of_rubinChain (h : RubinChainUnderDiamond.{u})
    (hdiamond : DiamondOmegaOne) (M : Type u) [SetStructure M] [Nonempty M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M] : Nonempty (AlephOneDeadEndExtension M) :=
  exists_zf_dead_end_of_countable' (rubinShelahSchmerl_of_rubinChain h hdiamond) M

/-- The model-theoretic half of the paper's Proposition `prop:countability-essential`, from Stage 1
of Enayat's Appendix and `◊`. From a countable model of `ZF` satisfying every instance of the
Vopenka scheme and failing internal choice, we get a model of cardinality `ℵ₁` with the same two
properties and with no proper end extension to a model of `ZF`.

The paper phrases the conclusion in terms of forcing rather than end extensions. Getting there
from `IsZFDeadEnd` is the forcing half of the argument, which is outside this file: a generic
extension that adds a set is a proper end extension, so `IsZFDeadEnd.false_of_new_element` applied
to it gives a contradiction. -/
theorem countability_essential_of_rubinChain (h : RubinChainUnderDiamond.{u})
    (hdiamond : DiamondOmegaOne) (M : Type u) [SetStructure M] [Nonempty M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable M] (hVP : ∀ φ : SetTheorySemisentence 2,
      VopenkaInstance (V := M) φ) (hAC : ¬ InternalChoice M) :
    ∃ E : AlephOneDeadEndExtension M,
      (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := E.Model) φ) ∧
        ¬ InternalChoice E.Model :=
  countability_essential' (rubinShelahSchmerl_of_rubinChain h hdiamond) M hVP hAC

end ZFVP
