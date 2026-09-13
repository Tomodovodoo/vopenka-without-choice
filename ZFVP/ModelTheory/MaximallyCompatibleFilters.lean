import ZFVP.ModelTheory.RubinModel

/-! Maximally compatible subsets of a poset, the notion Enayat's Appendix argument actually uses.

Definition 5.10 of "Models of set theory: extensions and dead ends" calls a subset `F` of a poset
a filter when `F` is a directed subposet, and calls a filter maximal when it has no proper
extension to a filter. That is `ZFVP.IsMaximalFilterOn`. Footnote 30 of the paper says a maximal
filter is the same thing as a maximally compatible subset, and the Appendix uses the second
reading: from `q` in the poset outside the filter it concludes that some `p` in the filter has no
common upper bound with `q`.

Inclusion maximality alone does not give that in a general poset. Take a chain
`p₀ < p₁ < p₂ < ...` and a point `q` such that `q` and `pₙ` have a common upper bound `zₙ` for
each `n`, while no single element lies above `q` and above cofinally many `pₙ`. The chain is then
an inclusion maximal directed set, yet `q` is compatible with every one of its members. So the two
readings come apart, and the Appendix needs the stronger one.

`IsMaximallyCompatibleOn` is that stronger notion: a filter that contains every poset element
compatible with all of its members. `IsMaximallyCompatibleOn.isMaximalFilterOn` shows it implies
inclusion maximality, and `IsMaximallyCompatibleOn.exists_incompatible` states the incompatibility
clause in the shape the reflection argument consumes.

On the poset the development applies this to the two readings do agree:
`isMaximallyCompatibleOn_of_isMaximalInternalFilter` shows that a maximal filter of the poset
`Fin(a,2)` of Definition 5.11(b), the internal finite partial functions from `a` into `2` ordered
by inclusion, is maximally compatible. This is the poset of Definition 5.16, so the whole
downstream argument is covered. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A filter on a poset that contains every poset element compatible with all of its members.
This is the "maximally compatible" reading of Enayat's Definition 5.10(c). -/
def IsMaximallyCompatibleOn (P : V → Prop) (le : V → V → Prop) (F : V → Prop) : Prop :=
  IsFilterOn P le F ∧ ∀ q, P q → (∀ p, F p → ∃ z, P z ∧ le p z ∧ le q z) → F q

/-- A maximally compatible filter is a maximal filter: any filter `F'` extending `F` has all of
its members compatible with all of `F`, by directedness of `F'`. -/
theorem IsMaximallyCompatibleOn.isMaximalFilterOn {P : V → Prop} {le : V → V → Prop}
    {F : V → Prop} (h : IsMaximallyCompatibleOn P le F) : IsMaximalFilterOn P le F := by
  refine ⟨h.1, ?_⟩
  intro F' hF' hle q hq
  refine h.2 q (hF'.1 q hq) ?_
  intro p hp
  obtain ⟨z, hz, hpz, hqz⟩ := hF'.2 p q (hle p hp) hq
  exact ⟨z, hF'.1 z hz, hpz, hqz⟩

/-- The incompatibility clause: a poset element outside a maximally compatible filter has no
common upper bound with some member of the filter. -/
theorem IsMaximallyCompatibleOn.exists_incompatible {P : V → Prop} {le : V → V → Prop}
    {F : V → Prop} (h : IsMaximallyCompatibleOn P le F) (q : V) (hq : P q) (hqF : ¬ F q) :
    ∃ p, F p ∧ ¬ ∃ z, P z ∧ le p z ∧ le q z := by
  by_contra hcon
  refine hqF (h.2 q hq ?_)
  intro p hp
  by_contra hno
  exact hcon ⟨p, hp, hno⟩

/-- On the poset `Fin(a,2)` of internal finite partial functions ordered by inclusion, a maximal
filter is maximally compatible. Two conditions there have a common upper bound exactly when they
agree where both are defined, so if `q` is compatible with every member of `F` then all of `F`
together with `q` is one partial function class, and the conditions below it form a filter
extending `F` and containing `q`. -/
theorem isMaximallyCompatibleOn_of_isMaximalInternalFilter (a : V) (F : V → Prop)
    (hF : IsMaximalInternalFilter (finitePartialFunctions a ((2 : ℕ) : V)) F) :
    IsMaximallyCompatibleOn (fun x ↦ x ∈ finitePartialFunctions a ((2 : ℕ) : V)) (· ⊆ ·) F := by
  refine ⟨hF.1, ?_⟩
  intro q hq hcomp
  have hqfun : IsFunction q :=
    ((mem_finitePartialFunctions _ _ _).mp hq).2.1
  -- Any two pairs with the same first entry drawn from `q` or from members of `F` agree.
  have agree : ∀ u v₁ v₂,
      (⟨u, v₁⟩ₖ ∈ q ∨ ∃ p, F p ∧ ⟨u, v₁⟩ₖ ∈ p) →
      (⟨u, v₂⟩ₖ ∈ q ∨ ∃ p, F p ∧ ⟨u, v₂⟩ₖ ∈ p) → v₁ = v₂ := by
    intro u v₁ v₂ h₁ h₂
    rcases h₁ with h₁ | ⟨p₁, hp₁, hmem₁⟩
    · rcases h₂ with h₂ | ⟨p₂, hp₂, hmem₂⟩
      · exact IsFunction.unique h₁ h₂
      · obtain ⟨z, hz, hp₂z, hqz⟩ := hcomp p₂ hp₂
        have hzfun : IsFunction z := ((mem_finitePartialFunctions _ _ _).mp hz).2.1
        exact IsFunction.unique (hqz _ h₁) (hp₂z _ hmem₂)
    · rcases h₂ with h₂ | ⟨p₂, hp₂, hmem₂⟩
      · obtain ⟨z, hz, hp₁z, hqz⟩ := hcomp p₁ hp₁
        have hzfun : IsFunction z := ((mem_finitePartialFunctions _ _ _).mp hz).2.1
        exact IsFunction.unique (hp₁z _ hmem₁) (hqz _ h₂)
      · obtain ⟨z, hz, hp₁z, hp₂z⟩ := hF.1.2 p₁ p₂ hp₁ hp₂
        have hzfun : IsFunction z :=
          ((mem_finitePartialFunctions _ _ _).mp (hF.1.1 z hz)).2.1
        exact IsFunction.unique (hp₁z _ hmem₁) (hp₂z _ hmem₂)
  -- The conditions all of whose pairs come from `q` or from members of `F`.
  set F' : V → Prop := fun x ↦ x ∈ finitePartialFunctions a ((2 : ℕ) : V) ∧
    ∀ w, w ∈ x → (w ∈ q ∨ ∃ p, F p ∧ w ∈ p) with hF'def
  have hmemF' : ∀ x, F' x ↔ x ∈ finitePartialFunctions a ((2 : ℕ) : V) ∧
      ∀ w, w ∈ x → (w ∈ q ∨ ∃ p, F p ∧ w ∈ p) := fun x ↦ Iff.rfl
  have hfilter : IsInternalFilter (finitePartialFunctions a ((2 : ℕ) : V)) F' := by
    refine ⟨fun x hx ↦ ((hmemF' x).mp hx).1, ?_⟩
    intro x y hx hy
    obtain ⟨hxP, hxH⟩ := (hmemF' x).mp hx
    obtain ⟨hyP, hyH⟩ := (hmemF' y).mp hy
    have hc : ∀ u v₁ v₂, ⟨u, v₁⟩ₖ ∈ x → ⟨u, v₂⟩ₖ ∈ y → v₁ = v₂ := by
      intro u v₁ v₂ h₁ h₂
      exact agree u v₁ v₂ (hxH _ h₁) (hyH _ h₂)
    have hu : x ∪ y ∈ finitePartialFunctions a ((2 : ℕ) : V) :=
      finitePartialFunction_union hxP hyP hc
    refine ⟨x ∪ y, (hmemF' _).mpr ⟨hu, ?_⟩,
      fun w hw ↦ mem_union_iff.mpr (Or.inl hw), fun w hw ↦ mem_union_iff.mpr (Or.inr hw)⟩
    intro w hw
    rcases mem_union_iff.mp hw with hw | hw
    · exact hxH w hw
    · exact hyH w hw
  have hsub : ∀ x, F x → F' x := by
    intro x hx
    exact (hmemF' x).mpr ⟨hF.1.1 x hx, fun w hw ↦ Or.inr ⟨x, hx, hw⟩⟩
  have hqF' : F' q := (hmemF' q).mpr ⟨hq, fun w hw ↦ Or.inl hw⟩
  exact hF.2 F' hfilter hsub q hqF'

end ZFVP
