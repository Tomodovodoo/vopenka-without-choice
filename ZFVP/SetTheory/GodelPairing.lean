import ZFVP.SetTheory.Hessenberg
import ZFVP.SetTheory.SetCodesTransport
import ZFVP.SetTheory.EndExtensionWellOrdering

/-! The Gödel pairing of an ordinal.

`GodelLess` is the Gödel order written as a first-order property of two pairs, with no reference
to `godelOrder α` as a set. `IsGodelPairing Λ p` says that `p` is a bijection from `Λ ×ˢ Λ` onto an
ordinal that carries `GodelLess` to membership. Such a `p` exists for every ordinal, is unique, and
is the Mostowski collapse of `godelOrder α`. Because every clause of `IsGodelPairing` is bounded,
the property moves along a membership end extension without transporting the order itself. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The Gödel order on Kuratowski pairs, spelled out: compare the unions of the two coordinates
first, then the first coordinates, then the second ones. -/
def GodelLess (u v : V) : Prop :=
  (kpair.π₁ u ∪ kpair.π₂ u) ∈ (kpair.π₁ v ∪ kpair.π₂ v) ∨
    ((kpair.π₁ u ∪ kpair.π₂ u) = (kpair.π₁ v ∪ kpair.π₂ v) ∧
      (kpair.π₁ u ∈ kpair.π₁ v ∨ (kpair.π₁ u = kpair.π₁ v ∧ kpair.π₂ u ∈ kpair.π₂ v)))

instance godelLess_definable : ℒₛₑₜ-relation[V] GodelLess := by
  unfold GodelLess
  definability

/-- `GodelLess` describes membership in `godelOrder α` for pairs from `α`. -/
theorem pair_mem_godelOrder_iff (α a b c d : V) [IsOrdinal α] (ha : a ∈ α) (hb : b ∈ α)
    (hc : c ∈ α) (hd : d ∈ α) :
    ⟨⟨a, b⟩ₖ, ⟨c, d⟩ₖ⟩ₖ ∈ godelOrder α ↔ GodelLess ⟨a, b⟩ₖ ⟨c, d⟩ₖ := by
  have : IsOrdinal a := IsOrdinal.of_mem ha
  have : IsOrdinal b := IsOrdinal.of_mem hb
  have : IsOrdinal c := IsOrdinal.of_mem hc
  have : IsOrdinal d := IsOrdinal.of_mem hd
  have hab : a ∪ b ∈ α := union_mem_of_ordinals ha hb
  have hcd : c ∪ d ∈ α := union_mem_of_ordinals hc hd
  simp only [godelOrder, pair_mem_pulledRelation_iff, godelCode_kpair, godelTarget,
    pair_mem_lexicographicRelation, pair_mem_membershipRelation, kpair.π₁_kpair, kpair.π₂_kpair,
    kpair_mem_iff, kpair_iff, GodelLess, ha, hb, hc, hd, hab, hcd, true_and, and_true]
  tauto

/-- `p` is the Gödel pairing of `Λ`: a bijection from `Λ ×ˢ Λ` onto an ordinal that turns
`GodelLess` into membership. -/
def IsGodelPairing (Λ p : V) : Prop :=
  IsFunction p ∧ domain p = Λ ×ˢ Λ ∧ IsOrdinal (range p) ∧
    (∀ u ∈ Λ ×ˢ Λ, ∀ v ∈ Λ ×ˢ Λ, p ‘ u ∈ p ‘ v ↔ GodelLess u v)

instance isGodelPairing_definable : ℒₛₑₜ-relation[V] IsGodelPairing := by
  unfold IsGodelPairing
  definability

/-- The values of a Gödel pairing compare by membership exactly as their arguments compare in
`godelOrder α`. -/
theorem godelPairing_value_mem_iff {α p : V} [IsOrdinal α] (h : IsGodelPairing α p) {u v : V}
    (hu : u ∈ α ×ˢ α) (hv : v ∈ α ×ˢ α) : p ‘ u ∈ p ‘ v ↔ ⟨u, v⟩ₖ ∈ godelOrder α := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hu
  obtain ⟨c, hc, d, hd, rfl⟩ := mem_prod_iff.mp hv
  rw [h.2.2.2 _ hu _ hv, ← pair_mem_godelOrder_iff α a b c d ha hb hc hd]

theorem exists_godelPairing (α : V) [IsOrdinal α] : ∃ p : V, IsGodelPairing α p := by
  have hR := godelOrder_wellOrder α
  have hcol := mostowskiMap_isTransitiveCollapse hR.2.1 (internalWellOrder_extensional hR)
  refine ⟨mostowskiMap (godelOrder α) (α ×ˢ α), IsFunction.of_mem hcol.2.1,
    domain_eq_of_mem_function hcol.2.1, ?_, ?_⟩
  · have h : range (mostowskiMap (godelOrder α) (α ×ˢ α))
        = internalOrderType (godelOrder α) (α ×ˢ α) := rfl
    rw [h]
    exact internalOrderType_ordinal hR
  · intro u hu v hv
    rw [hcol.2.2.2.2 u hu v hv]
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hu
    obtain ⟨c, hc, d, hd, rfl⟩ := mem_prod_iff.mp hv
    exact pair_mem_godelOrder_iff α a b c d ha hb hc hd

theorem isTransitiveCollapse_of_godelPairing {α p : V} [IsOrdinal α] (h : IsGodelPairing α p) :
    IsTransitiveCollapse (godelOrder α) (α ×ˢ α) (range p) p := by
  have hfun : IsFunction p := h.1
  have hord : IsOrdinal (range p) := h.2.2.1
  refine ⟨IsOrdinal.toIsTransitive, ?_, rfl, ?_, ?_⟩
  · have hm := IsFunction.mem_function p
    rwa [h.2.1] at hm
  · intro x hx y hy heq
    rcases (godelOrder_wellOrder α).2.2.2 x hx y hy with hxy | hxy | hxy
    · have hv := (godelPairing_value_mem_iff h hx hy).mpr hxy
      rw [heq] at hv
      exact (mem_irrefl _ hv).elim
    · exact hxy
    · have hv := (godelPairing_value_mem_iff h hy hx).mpr hxy
      rw [heq] at hv
      exact (mem_irrefl _ hv).elim
  · intro x hx y hy
    exact godelPairing_value_mem_iff h hx hy

theorem godelPairing_unique {α p q : V} [IsOrdinal α] (hp : IsGodelPairing α p)
    (hq : IsGodelPairing α q) : p = q := by
  have hR := godelOrder_wellOrder α
  have h1 := (transitiveCollapse_unique hR.2.1 (isTransitiveCollapse_of_godelPairing hp)).1
  have h2 := (transitiveCollapse_unique hR.2.1 (isTransitiveCollapse_of_godelPairing hq)).1
  exact h1.trans h2.symm

theorem godelPairing_injective {α p : V} [IsOrdinal α] (h : IsGodelPairing α p) : Injective p := by
  have hfun : IsFunction p := h.1
  have hcol := isTransitiveCollapse_of_godelPairing h
  intro x₁ x₂ y h₁ h₂
  have hx₁ : x₁ ∈ α ×ˢ α := h.2.1 ▸ mem_domain_of_kpair_mem h₁
  have hx₂ : x₂ ∈ α ×ˢ α := h.2.1 ▸ mem_domain_of_kpair_mem h₂
  exact hcol.2.2.2.1 x₁ hx₁ x₂ hx₂
    ((value_eq_of_kpair_mem h₁).trans (value_eq_of_kpair_mem h₂).symm)

theorem godelPairing_mem_function {α p : V} [IsOrdinal α] (h : IsGodelPairing α p) :
    p ∈ range p ^ (α ×ˢ α) :=
  (isTransitiveCollapse_of_godelPairing h).2.1

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

variable (j : MembershipEndExtension V W)

/-- The Gödel order comparison is preserved and reflected by a membership end extension. -/
theorem godelLess_map (u v : V) : GodelLess (j u) (j v) ↔ GodelLess u v := by
  simp only [GodelLess, ← j.map_first, ← j.map_second, ← j.map_union, j.mem_iff,
    j.injective.eq_iff]

/-- Being the Gödel pairing of `Λ` is preserved by a membership end extension. -/
theorem isGodelPairing_map {Λ p : V} (h : IsGodelPairing Λ p) : IsGodelPairing (j Λ) (j p) := by
  obtain ⟨hfun, hdom, hord, hmem⟩ := h
  refine ⟨j.map_function p, ?_, ?_, ?_⟩
  · rw [← j.map_domain p, hdom, j.map_prod]
  · rw [← j.map_range p]
    exact (j.bounded_defined isOrdinalFormula_bounded (fun v ↦ IsOrdinal (v 0))
      (fun v ↦ IsOrdinal (v 0)) ![range p]).mp hord
  · intro u hu v hv
    rw [← j.map_prod] at hu hv
    obtain ⟨u₀, hu₀, rfl⟩ := j.endExtension _ u hu
    obtain ⟨v₀, hv₀, rfl⟩ := j.endExtension _ v hv
    rw [← j.map_value p u₀ (by rw [hdom]; exact hu₀),
      ← j.map_value p v₀ (by rw [hdom]; exact hv₀), j.mem_iff, j.godelLess_map]
    exact hmem u₀ hu₀ v₀ hv₀

end MembershipEndExtension

/-- The Gödel order comparison as a formula with no parameters. -/
def godelLessFormula : SetTheorySemisentence 2 :=
  f“u v. !union.dfn (!kpair.π₁.dfn u) (!kpair.π₂.dfn u) ∈
      !union.dfn (!kpair.π₁.dfn v) (!kpair.π₂.dfn v) ∨
    (!union.dfn (!kpair.π₁.dfn u) (!kpair.π₂.dfn u) =
        !union.dfn (!kpair.π₁.dfn v) (!kpair.π₂.dfn v) ∧
      (!kpair.π₁.dfn u ∈ !kpair.π₁.dfn v ∨
        (!kpair.π₁.dfn u = !kpair.π₁.dfn v ∧ !kpair.π₂.dfn u ∈ !kpair.π₂.dfn v)))”

/-- `p` is the Gödel pairing of `Λ`, as a formula with no parameters. -/
def godelPairingFormula : SetTheorySemisentence 2 :=
  f“L p. !IsFunction.dfn p ∧ !domain.dfn p = !prod.dfn L L ∧ !IsOrdinal.dfn (!range.dfn p) ∧
    ∀ u ∈ !prod.dfn L L, ∀ v ∈ !prod.dfn L L,
      (!value.dfn p u ∈ !value.dfn p v ↔ !godelLessFormula u v)”

instance godelLessFormula_defined : ℒₛₑₜ-relation[V] GodelLess via godelLessFormula :=
  ⟨fun v ↦ by simp [godelLessFormula, GodelLess]⟩

instance godelPairingFormula_defined :
    ℒₛₑₜ-relation[V] IsGodelPairing via godelPairingFormula :=
  ⟨fun v ↦ by simp [godelPairingFormula, IsGodelPairing]⟩

theorem eval_godelPairingFormula (Λ p : V) :
    godelPairingFormula.Evalb ![Λ, p] ↔ IsGodelPairing Λ p :=
  Defined.eval_iff (φ := godelPairingFormula)
    (R := fun v : Fin 2 → V ↦ IsGodelPairing (v 0) (v 1)) ![Λ, p]

end ZFVP
