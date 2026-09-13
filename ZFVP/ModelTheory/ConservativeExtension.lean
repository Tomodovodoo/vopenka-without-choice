import ZFVP.ModelTheory.EndExtensionBasics

/-! Classes, rather classless models and conservative end extensions, following Enayat's
"Models of set theory: extensions and dead ends" (Definitions 2.4(c) and 5.2(a)(b)).

The main result is the step used in Enayat's Proposition 5.4 and Theorem 5.18: a
powerset-preserving end extension of a rather classless model is conservative. Enayat phrases
that step for rank extensions; powerset preservation is the only part of rank extension the
argument uses, so it is stated with that hypothesis here.

Throughout, "parametrically definable subset" is `ℒₛₑₜ-predicate[V] X`, that is,
`Language.DefinablePred`: a first-order formula in the language of set theory whose free
variables take values in `V`, so it carries finitely many parameters from `V`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Enayat's Definition 5.2(a): a class of `V` is a subset whose intersection with every set of
`V` is coded in `V`. -/
def IsClass (V : Type*) [SetStructure V] (X : V → Prop) : Prop :=
  ∀ a : V, ∃ b : V, ∀ x : V, x ∈ b ↔ (x ∈ a ∧ X x)

/-- Separation: every parametrically definable subset of a model of ZF is a class. -/
theorem isClass_of_definable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (X : V → Prop) (hX : ℒₛₑₜ-predicate[V] X) : IsClass V X := by
  intro a
  exact ⟨sep a X hX, fun x ↦ mem_sep_iff⟩

/-- Enayat's Definition 5.2(b). -/
def IsRatherClassless (V : Type*) [SetStructure V] : Prop :=
  ∀ X : V → Prop, IsClass V X → ℒₛₑₜ-predicate[V] X

/-- Enayat's Definition 2.4(c) for membership end extensions: every subset of the smaller model
cut out by a formula with parameters of the larger model is already definable in the smaller one. -/
def MembershipEndExtension.IsConservative {V W : Type*} [SetStructure V] [SetStructure W]
    (j : MembershipEndExtension V W) : Prop :=
  ∀ D : W → Prop, (ℒₛₑₜ-predicate[W] D) → ℒₛₑₜ-predicate[V] (fun x ↦ D (j x))

/-- Along a powerset-preserving end extension, the pullback of a parametrically definable subset
of the larger model is a class of the smaller one. -/
theorem MembershipEndExtension.IsPowersetPreserving.pullback_isClass
    {V W : Type*} [SetStructure V] [SetStructure W] [Nonempty V] [Nonempty W]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {j : MembershipEndExtension V W}
    (hj : j.IsPowersetPreserving) (D : W → Prop) (hD : ℒₛₑₜ-predicate[W] D) :
    IsClass V (fun x ↦ D (j x)) := by
  intro a
  -- Separate inside `W`, then pull the resulting subset of `j a` back to `V`.
  set b : W := sep (j a) D hD with hb
  have hbsub : b ⊆ j a := fun x hx ↦ (mem_sep_iff.mp hx).1
  obtain ⟨c, hc⟩ := hj a b hbsub
  refine ⟨c, fun x ↦ ?_⟩
  have h1 : x ∈ c ↔ j x ∈ j c := (j.mem_iff x c).symm
  rw [h1, hc, hb, mem_sep_iff, j.mem_iff]

/-- Enayat's Proposition 5.4 step: a powerset-preserving end extension of a rather classless
model is conservative. -/
theorem IsRatherClassless.isConservative_of_isPowersetPreserving
    {V W : Type*} [SetStructure V] [SetStructure W] [Nonempty V] [Nonempty W]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (hV : IsRatherClassless V)
    {j : MembershipEndExtension V W} (hj : j.IsPowersetPreserving) : j.IsConservative :=
  fun D hD ↦ hV _ (hj.pullback_isClass D hD)

end ZFVP
