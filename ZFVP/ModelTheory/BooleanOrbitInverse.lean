import ZFVP.ModelTheory.BooleanGenericAutomorphism
import ZFVP.ModelTheory.BooleanInternalTruth

/-! Two halves of Karagila-Schilhan, Lemma 9.3 that need no Galois step.

The first is the inverse of the value map. An orbit filter `H` carries the side condition
`V[H] = V[G]` (`IsFullValuation`), so the generic ultrafilter `A.boolGenericSet` of the extension
is the value at `H` of a set of the ground model. That set need not be a forcing name, so it is
replaced by its name hull (`nameHull`), which keeps only the pairs whose condition lies in the
completion and does so hereditarily; the hull is a name over the completion and has the same
value at every filter that lives inside the completion. With a genuine name `σ` for the generic
in hand, the atomic truth lemma for `H` gives the map `d c = ‖č ∈ σ‖` with

  `č ∈ G ↔ (d c)ˇ ∈ H`,

which composed with the map `e b = ‖b̌ ∈ τ‖` of a name `τ` of `H` says that a condition is met by
the generic exactly when `e (d c)` is. That is the identity making the value map invertible.

The second is that below one condition of the generic the value map is the identity on the
support algebra. The orbit filter and the generic contain the same members of the support algebra
(`orbitFilter_agree_supportAlgebraBase`), so for each `d` there the generic meets `d` exactly when
it meets `e d`. A single condition works for all `d` at once: the conditions that either lie in
one of the regular sets `d ∩ ¬(e d)`, `¬d ∩ (e d)` or have no extension in any of them are dense,
the generic meets that set, and the first case contradicts the agreement, so the generic contains
a condition `r` no extension of which enters any of those sets. The regular cone of `r` is the
condition below which the two families agree as sets.

The argument for the second half is by density inside the given generic, so it needs neither
`[Countable V]` nor the forcing calculus.

Nontriviality of the value map in the form `e b ≠ ∅` for every condition `b` of the completion is
not proved, and it does not follow from the clauses of an orbit filter. What is proved
(`booleanMemValue_nonempty_of_meets`) is nontriviality along the inverse: `e (d c)` is met by the
generic whenever `c` is. For an arbitrary `b` the clauses leave room for `e b = ∅`: an orbit filter
is only asked to be an antichain-generic ultrafilter on the checked completion with the same
extension as the generic and the same values on the finitely many support names, and an
ultrafilter of that kind can be forced to lie below a fixed `¬b`, in which case no condition forces
`b̌ ∈ τ`. Making the map onto is what the Galois step of Lemma 9.3 does. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ### The name hull of a set -/

section

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- One step of the hull recursion: keep the pairs of `μ` whose condition lies in `B`, and
replace the first coordinate by its own hull. -/
noncomputable def nameHullStep (B μ f : V) : V :=
  repl (fun z ↦ (⟨f ‘ (kpair.π₁ z), kpair.π₂ z⟩ₖ : V)) (by definability)
    {z ∈ μ ; kpair.π₂ z ∈ B ∧ z = ⟨kpair.π₁ z, kpair.π₂ z⟩ₖ}

theorem mem_nameHullStep_iff (B μ f y : V) :
    y ∈ nameHullStep B μ f ↔ ∃ ν : V, ∃ p ∈ B, (⟨ν, p⟩ₖ : V) ∈ μ ∧ y = ⟨f ‘ ν, p⟩ₖ := by
  simp only [nameHullStep, repl_spec, mem_sep_iff]
  constructor
  · rintro ⟨z, ⟨hzμ, hp, hz⟩, rfl⟩
    exact ⟨kpair.π₁ z, kpair.π₂ z, hp, by rw [← hz]; exact hzμ, rfl⟩
  · rintro ⟨ν, p, hp, hνp, rfl⟩
    refine ⟨(⟨ν, p⟩ₖ : V), ⟨hνp, ?_, ?_⟩, ?_⟩ <;>
      simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    · exact hp

instance nameHullStep_definable : ℒₛₑₜ-function₃[V] nameHullStep := by
  have h : ℒₛₑₜ-relation₄ (fun C B μ f : V ↦ ∀ y, y ∈ C ↔
      ∃ ν : V, ∃ p ∈ B, (⟨ν, p⟩ₖ : V) ∈ μ ∧ y = ⟨f ‘ ν, p⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = nameHullStep (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [mem_nameHullStep_iff]

/-- The name hull of a set over a set of conditions `B`: the pairs with a condition in `B`, kept
hereditarily. -/
noncomputable def nameHull (B μ : V) : V :=
  subnameRecursion (nameHullStep B) (by definability) μ

instance nameHull_definable (B : V) : ℒₛₑₜ-function₁[V] (nameHull B) := by
  unfold nameHull
  infer_instance

theorem mem_nameHull_iff (B μ y : V) :
    y ∈ nameHull B μ ↔ ∃ ν : V, ∃ p ∈ B, (⟨ν, p⟩ₖ : V) ∈ μ ∧ y = ⟨nameHull B ν, p⟩ₖ := by
  rw [nameHull, subnameRecursion_equation]
  change y ∈ nameHullStep B μ
    (definableGraph (domain μ) (nameHull B) (nameHull_definable B)) ↔ _
  rw [mem_nameHullStep_iff]
  constructor
  · rintro ⟨ν, p, hp, hνp, rfl⟩
    exact ⟨ν, p, hp, hνp, by rw [value_definableGraph _ _ _ (mem_domain_of_kpair_mem hνp)]⟩
  · rintro ⟨ν, p, hp, hνp, rfl⟩
    exact ⟨ν, p, hp, hνp, by rw [value_definableGraph _ _ _ (mem_domain_of_kpair_mem hνp)]⟩

/-- The hull of any set is a forcing name over `B`. -/
theorem nameHull_isForcingName (B μ : V) : IsForcingName B (nameHull B μ) := by
  have h := projectedRank_induction (nameClosure μ) (fun x : V ↦ x) (by definability)
    (fun ν ↦ IsForcingName B (nameHull B ν)) (by definability) ?_
  · exact h μ (mem_nameClosure_self μ)
  intro ν hν ih
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨ν', p, hp, hνp, rfl⟩ := (mem_nameHull_iff B ν z).mp hz
  refine ⟨nameHull B ν', p, hp, rfl, ?_⟩
  exact ih ν' (nameClosure_closed μ ν hν ν' (mem_domain_of_kpair_mem hνp))
    (rank_subname_lt hνp)

/-- A filter contained in `B` gives the hull the value it gives the set: the pairs the hull drops
have a condition outside `B`, so outside the filter. -/
theorem nameValue_nameHull {B G : V} (hGB : G ⊆ B) (μ : V) :
    nameValue G (nameHull B μ) = nameValue G μ := by
  have h := projectedRank_induction (nameClosure μ) (fun x : V ↦ x) (by definability)
    (fun ν ↦ nameValue G (nameHull B ν) = nameValue G ν) (by definability) ?_
  · exact h μ (mem_nameClosure_self μ)
  intro ν hν ih
  have ihν : ∀ ν' : V, ∀ p : V, (⟨ν', p⟩ₖ : V) ∈ ν →
      nameValue G (nameHull B ν') = nameValue G ν' := by
    intro ν' p hp
    exact ih ν' (nameClosure_closed μ ν hν ν' (mem_domain_of_kpair_mem hp)) (rank_subname_lt hp)
  apply mem_ext
  intro z
  rw [mem_nameValue_iff, mem_nameValue_iff]
  constructor
  · rintro ⟨σ, p, hp, hσp, rfl⟩
    obtain ⟨ν', q, hq, hνq, he⟩ := (mem_nameHull_iff B ν _).mp hσp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact ⟨ν', p, hp, hνq, (ihν ν' p hνq).symm ▸ rfl⟩
  · rintro ⟨σ, p, hp, hσp, rfl⟩
    exact ⟨nameHull B σ, p, hp,
      (mem_nameHull_iff B ν _).mpr ⟨σ, p, hGB p hp, hσp, rfl⟩, (ihν σ p hσp).symm⟩

/-- The conditions that lie in one of the sets of the family `Y` and those no extension of which
lies in any of them together form a dense set. -/
theorem exists_dense_decideFamily {P R : V} (hR : IsForcingPreorder P R) (Y : V) :
    ∃ Dn : V, ForcingDense P R Dn ∧
      ∀ r ∈ Dn, r ∈ P ∧ ((∃ y ∈ Y, r ∈ y) ∨
        (∀ y ∈ Y, ∀ t ∈ P, (⟨t, r⟩ₖ : V) ∈ R → t ∉ y)) := by
  refine ⟨sep P (fun r ↦ (∃ y ∈ Y, r ∈ y) ∨
    (∀ y ∈ Y, ∀ t ∈ P, (⟨t, r⟩ₖ : V) ∈ R → t ∉ y)) (by definability), ⟨sep_subset, ?_⟩,
    fun r hr ↦ mem_sep_iff.mp hr⟩
  intro q hq
  by_cases hcase : ∃ y ∈ Y, ∃ t ∈ P, (⟨t, q⟩ₖ : V) ∈ R ∧ t ∈ y
  · obtain ⟨y, hy, t, htP, htq, hty⟩ := hcase
    exact ⟨t, mem_sep_iff.mpr ⟨htP, Or.inl ⟨y, hy, hty⟩⟩, htq⟩
  · exact ⟨q, mem_sep_iff.mpr
      ⟨hq, Or.inr fun y hy t htP htq hty ↦ hcase ⟨y, hy, t, htP, htq, hty⟩⟩, hR.2.1 q hq⟩

end

/-! ### The hull along an end extension -/

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_nameHullStep (j : MembershipEndExtension V W) (B μ f : V) :
    j (nameHullStep B μ f) = nameHullStep (j B) (j μ) (j f) := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension _ y hy
    obtain ⟨ν, p, hp, hνp, rfl⟩ := (mem_nameHullStep_iff _ _ _ _).mp hx
    refine (mem_nameHullStep_iff _ _ _ _).mpr ⟨j ν, j p, (j.mem_iff _ _).mpr hp, ?_, ?_⟩
    · rw [← j.map_kpair, j.mem_iff]; exact hνp
    · rw [j.map_kpair, j.map_value_total]
  · intro hy
    obtain ⟨ν, p, hp, hνp, he⟩ := (mem_nameHullStep_iff _ _ _ _).mp hy
    obtain ⟨ν₀, p₀, hν₀, rfl, rfl⟩ := (j.pair_mem_image_iff μ ν p).mp hνp
    rw [← j.map_value_total, ← j.map_kpair] at he
    rw [he, j.mem_iff]
    exact (mem_nameHullStep_iff _ _ _ _).mpr ⟨ν₀, p₀, (j.mem_iff _ _).mp hp, hν₀, rfl⟩

theorem map_nameHullRecursion (j : MembershipEndExtension V W) {B N f : V}
    (hf : IsSubnameRecursion N (nameHullStep B) f) :
    IsSubnameRecursion (j N) (nameHullStep (j B)) (j f) := by
  letI : IsFunction f := hf.1
  refine ⟨j.map_function f, ?_, ?_⟩
  · rw [← j.map_relationDomain, hf.2.1]
  · intro x hx
    obtain ⟨τ, hτ, rfl⟩ := j.endExtension N x hx
    rw [← j.map_value_total, hf.2.2 τ hτ, j.map_nameHullStep,
      j.map_restrict, j.map_relationDomain]

theorem map_nameHull (j : MembershipEndExtension V W) (B μ : V) :
    j (nameHull B μ) = nameHull (j B) (j μ) := by
  let f := subnameRecursionTable (nameHullStep B) (by definability) μ
  have hf : IsSubnameRecursion (nameClosure μ) (nameHullStep B) f :=
    subnameRecursionTable_spec _ _ _
  have hg := j.map_nameHullRecursion hf
  have hμ : j μ ∈ j (nameClosure μ) := (j.mem_iff _ _).mpr (mem_nameClosure_self μ)
  have he := subnameRecursion_coherent (j.map_subnameClosed (nameClosure_closed μ))
    (nameClosure_closed (j μ)) hg
    (subnameRecursionTable_spec (nameHullStep (j B)) (by definability) (j μ))
    (j μ) hμ (mem_nameClosure_self (j μ))
  change j (f ‘ μ) = _
  rw [j.map_value_total]
  exact he

end MembershipEndExtension

/-! ### The name hull of a checked set -/

section

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable {A : ForcingContext V}

theorem check_nameHull (A : ForcingContext V) (B μ : V) :
    A.check (nameHull B μ) = nameHull (A.check B) (A.check μ) :=
  A.checkEmbedding.map_nameHull B μ

/-- A set of the extension that is the value at a filter `H` of a ground set is the value at `H`
of a ground name over the completion, as soon as `H` consists of checked Boolean conditions. -/
theorem exists_forcingName_nameValue_eq {H : A.Model}
    (hHB : H ⊆ A.check (booleanConditions A.P A.R)) (μ : V) :
    IsForcingName (booleanConditions A.P A.R) (nameHull (booleanConditions A.P A.R) μ) ∧
      nameValue H (A.check (nameHull (booleanConditions A.P A.R) μ)) =
        nameValue H (A.check μ) :=
  ⟨nameHull_isForcingName _ _, by
    rw [A.check_nameHull]
    exact nameValue_nameHull hHB (A.check μ)⟩

/-! ### The atomic truth lemma for two names -/

section

variable {U : A.Model}
  (hU : IsAntichainGeneric (A.check (regularSets A.P A.R))
    (A.check (boolMaximalAntichains A.P A.R)) U)

include hU

/-- The atomic truth lemma for membership between two names over the completion. This is
`check_mem_nameValue_iff` with the hypothesis that the first name lies in the domain of the
second replaced by the hypothesis that it is a name over the completion. -/
theorem check_mem_nameValue_iff_of_names (hAC : InternalChoice V) {ν μ : V}
    (hν : IsForcingName (booleanConditions A.P A.R) ν)
    (hμ : IsForcingName (booleanConditions A.P A.R) μ) :
    nameValue U (A.check ν) ∈ nameValue U (A.check μ) ↔
      A.check (booleanValueBase A.P A.R ν μ) ∈ U := by
  have hclosed : IsSubnameClosed (nameClosure ν ∪ nameClosure μ) :=
    (nameClosure_closed ν).union (nameClosure_closed μ)
  have hnames : ∀ τ' ∈ nameClosure ν ∪ nameClosure μ, ∀ z ∈ τ',
      ∃ υ : V, ∃ p ∈ booleanConditions A.P A.R, z = ⟨υ, p⟩ₖ := by
    intro τ' hτ' z hz
    rcases mem_union_iff.mp hτ' with h' | h'
    · exact hν τ' h' z hz
    · exact hμ τ' h' z hz
  have hνN : ν ∈ nameClosure ν ∪ nameClosure μ :=
    mem_union_iff.mpr (Or.inl (mem_nameClosure_self ν))
  have hμN : μ ∈ nameClosure ν ∪ nameClosure μ :=
    mem_union_iff.mpr (Or.inr (mem_nameClosure_self μ))
  constructor
  · intro h
    obtain ⟨p, -, hpU, hp⟩ :=
      exists_mem_atomicMembership_of_nameValue_check_mem hU hAC hclosed hνN hμN h
    exact hU.upward _ hpU _ ((A.check_mem_iff _ _).mpr ((mem_regularSets_iff _ _ _).mpr
      (booleanValueBase_regular A.order ν μ)))
      ((A.checkEmbedding.subset_iff _ _).mpr (subset_booleanValueBase A.order hp))
  · intro h
    have hYreg : ∀ y ∈ atomicMembership (booleanConditions A.P A.R) (booleanOrder A.P A.R) ν μ,
        IsForcingRegular A.P A.R y := fun y hy ↦
      booleanConditions_regular (atomicMembership_subset _ _ _ _ y hy)
    obtain ⟨y, hy, hyU⟩ := antichainGeneric_check_join_mem hU hAC hYreg h
    exact nameValue_check_mem_of_mem_atomicMembership hU hAC hclosed hnames hνN hμN hyU hy

end

/-! ### The inverse of the value map -/

/-- The generic ultrafilter of the extension is the value at an orbit filter `H` of a ground name
over the completion, and the Boolean value `d c = ‖č ∈ σ‖` of that name decides membership in the
generic: `č` lies in the generic exactly when `(d c)ˇ` lies in `H`. The name comes from the
clause `V[H] = V[G]` of `IsOrbitFilter`, read with a formula `Pf` whose instances at `p` are
checked sets. -/
theorem exists_ground_name_boolGenericSet (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a) :
    ∃ σ : V, IsForcingName (booleanConditions A.P A.R) σ ∧
      nameValue H (A.check σ) = A.boolGenericSet ∧
      ∀ c ∈ booleanConditions A.P A.R,
        (A.check c ∈ A.boolGenericSet ↔
          A.check (booleanValueBase A.P A.R (checkName A.P c) σ) ∈ H) := by
  have hU := antichainGeneric_of_clauses hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2.1
  have htop : A.check A.P ∈ H := hH.2.2.2.2.2.1
  have hHB : H ⊆ A.check (booleanConditions A.P A.R) :=
    subset_check_booleanConditions_of_isOrbitFilter hH
  obtain ⟨y, hy, heq⟩ := hH.2.2.2.2.2.2.1 A.boolGenericSet
  obtain ⟨σ₀, rfl⟩ := hPf y hy
  obtain ⟨hname, hvalue⟩ := exists_forcingName_nameValue_eq hHB σ₀
  have hσval : nameValue H (A.check (nameHull (booleanConditions A.P A.R) σ₀)) =
      A.boolGenericSet := by rw [hvalue, ← heq]
  refine ⟨nameHull (booleanConditions A.P A.R) σ₀, hname, hσval, fun c hc ↦ ?_⟩
  have hcn : IsForcingName (booleanConditions A.P A.R) (checkName A.P c) :=
    checkName_isName (top_mem_booleanConditions ⟨A.one, A.top.1⟩) c
  rw [← hσval, ← A.nameValue_check_checkName htop c,
    check_mem_nameValue_iff_of_names hU hAC hcn hname]

/-- The value map is invertible: with `e b = ‖b̌ ∈ τ‖` for a ground name `τ` of the orbit filter
`H` and `d c = ‖č ∈ σ‖` for the ground name `σ` of the generic, a condition `c` of the completion
is met by the generic exactly when `e (d c)` is. -/
theorem exists_valueMap_inverse (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a) :
    ∃ τ σ : V, IsForcingName (booleanConditions A.P A.R) τ ∧
      IsForcingName (booleanConditions A.P A.R) σ ∧
      (∀ b : V, (A.check b ∈ H ↔ ∃ q ∈ A.G, q ∈ A.booleanMemValue τ b)) ∧
      nameValue H (A.check σ) = A.boolGenericSet ∧
      ∀ c ∈ booleanConditions A.P A.R,
        ((∃ q ∈ A.G, q ∈ c) ↔
          ∃ q ∈ A.G, q ∈ A.booleanMemValue τ (booleanValueBase A.P A.R (checkName A.P c) σ)) := by
  obtain ⟨τ, hτ, hval⟩ := A.exists_booleanValueFamily H
  obtain ⟨σ, hσ, hσval, hd⟩ := exists_ground_name_boolGenericSet hAC hH hPf
  refine ⟨τ, σ, hτ, hσ, hval, hσval, fun c hc ↦ ?_⟩
  rw [← hval, ← hd c hc, A.check_mem_boolGenericSet_iff]
  exact ⟨fun h ↦ ⟨(mem_regularSets_iff _ _ _).mpr (booleanConditions_regular hc), h⟩, And.right⟩


/-- Nontriviality of the value map along the inverse: for every condition `c` of the completion
that the generic meets, the value `e (d c)` is met by the generic, so it is not empty. -/
theorem booleanMemValue_nonempty_of_meets (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {cs ck W p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) cs ck W p H)
    (hPf : ∀ y : A.Model, Pf.Evalb ![y, p] → ∃ a : V, y = A.check a) :
    ∃ τ σ : V, IsForcingName (booleanConditions A.P A.R) τ ∧
      IsForcingName (booleanConditions A.P A.R) σ ∧
      (∀ b : V, (A.check b ∈ H ↔ ∃ q ∈ A.G, q ∈ A.booleanMemValue τ b)) ∧
      nameValue H (A.check σ) = A.boolGenericSet ∧
      ∀ c ∈ booleanConditions A.P A.R, (∃ q ∈ A.G, q ∈ c) →
        ∃ z : V, z ∈ A.booleanMemValue τ (booleanValueBase A.P A.R (checkName A.P c) σ) := by
  obtain ⟨τ, σ, hτ, hσ, hval, hσval, hcomp⟩ := exists_valueMap_inverse hAC hH hPf
  refine ⟨τ, σ, hτ, hσ, hval, hσval, fun c hc hmet ↦ ?_⟩
  obtain ⟨q, -, hq⟩ := (hcomp c hc).mp hmet
  exact ⟨q, hq⟩

/-! ### The value map on the support algebra -/

/-- The Boolean value of `b̌ ∈ τ` is a regular set of the ground poset. -/
theorem booleanMemValue_regular (A : ForcingContext V) (τ b : V) :
    IsForcingRegular A.P A.R (A.booleanMemValue τ b) :=
  A.booleanValue_regular memAtom _

/-- Below one condition of the generic the value map is the identity on the support algebra: for
an orbit filter `H` with ground name `τ`, there is a condition `p₁` met by the generic with
`‖ď ∈ τ‖ ∩ p₁ = d ∩ p₁` for every `d` of the support algebra that is a Boolean condition.

The filter and the generic contain the same members of the support algebra, so the generic meets
`d` exactly when it meets `‖ď ∈ τ‖`. The conditions that lie in one of the regular sets
`d ∩ ¬‖ď ∈ τ‖`, `¬d ∩ ‖ď ∈ τ‖`, or have no extension in any of them, are dense; a member of the
first kind in the generic contradicts the agreement, so the generic contains a condition `r` of
the second kind, and `p₁` is the regular cone of `r`. -/
theorem exists_condition_booleanMemValue_eq_on_supportAlgebra (hAC : InternalChoice V)
    {Pf : SetTheorySemisentence 2} {s k : V} [IsFunction s] (hsdom : domain s = k)
    (hs : ∀ i ∈ k, IsSaturatedNiceName (booleanConditions A.P A.R) (booleanOrder A.P A.R) A.P
      ((ω : V) ×ˢ (ω : V)) (s ‘ i))
    {p H : A.Model}
    (hH : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H)
    {τ : V} (hval : ∀ b : V, (A.check b ∈ H ↔ ∃ q ∈ A.G, q ∈ A.booleanMemValue τ b)) :
    ∃ p₁ ∈ booleanConditions A.P A.R, (∃ q ∈ A.G, q ∈ p₁) ∧
      ∀ d ∈ supportAlgebraBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s),
        d ∈ booleanConditions A.P A.R →
        A.booleanMemValue τ d ∩ p₁ = d ∩ p₁ := by
  have hdef : ℒₛₑₜ-function₁[V] (A.booleanMemValue τ) := A.booleanMemValue_definable τ
  have hEreg : ∀ d : V, IsForcingRegular A.P A.R (A.booleanMemValue τ d) :=
    A.booleanMemValue_regular τ
  set D : V := sep (supportAlgebraBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s))
    (fun d ↦ d ∈ booleanConditions A.P A.R) (by definability) with hDdef
  have hmemD : ∀ d : V, d ∈ D ↔
      d ∈ supportAlgebraBase A.P A.R A.P ((ω : V) ×ˢ (ω : V)) (range s) ∧
        d ∈ booleanConditions A.P A.R := fun d ↦ by rw [hDdef]; exact mem_sep_iff
  have hagree : ∀ d ∈ D, ((∃ q ∈ A.G, q ∈ d) ↔ (∃ q ∈ A.G, q ∈ A.booleanMemValue τ d)) := by
    intro d hd
    obtain ⟨hdS, hdB⟩ := (hmemD d).mp hd
    have h := orbitFilter_agree_supportAlgebraBase hAC hsdom hs hH (A.check d)
      ((A.check_mem_iff _ _).mpr hdS)
    rw [A.check_mem_boolGenericSet_iff, hval d] at h
    exact ⟨fun hm ↦ h.mp ⟨(mem_regularSets_iff _ _ _).mpr (booleanConditions_regular hdB), hm⟩,
      fun hm ↦ (h.mpr hm).2⟩
  obtain ⟨Y, hY⟩ : ∃ Y : V, ∀ y : V, y ∈ Y ↔
      (∃ d ∈ D, y = d ∩ forcingNegation A.P A.R (A.booleanMemValue τ d)) ∨
      (∃ d ∈ D, y = forcingNegation A.P A.R d ∩ A.booleanMemValue τ d) := by
    refine ⟨repl (fun d ↦ d ∩ forcingNegation A.P A.R (A.booleanMemValue τ d))
        (by definability) D ∪
      repl (fun d ↦ forcingNegation A.P A.R d ∩ A.booleanMemValue τ d) (by definability) D,
      fun y ↦ ?_⟩
    rw [mem_union_iff, repl_spec, repl_spec]
  have hYreg : ∀ y ∈ Y, IsForcingRegular A.P A.R y := by
    intro y hy
    rcases (hY y).mp hy with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
    · exact forcingRegular_inter (booleanConditions_regular ((hmemD d).mp hd).2)
        (forcingNegation_regular A.order (hEreg d).2.1)
    · exact forcingRegular_inter
        (forcingNegation_regular A.order (booleanConditions_regular ((hmemD d).mp hd).2).2.1)
        (hEreg d)
  obtain ⟨Dn, hDn, hDnmem⟩ := exists_dense_decideFamily A.order Y
  obtain ⟨r, hrG, hrDn⟩ := A.generic.2 Dn hDn
  obtain ⟨hrP, hcases⟩ := hDnmem r hrDn
  have hnocase : ∀ y ∈ Y, r ∉ y := by
    intro y hy hry
    rcases (hY y).mp hy with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
    · obtain ⟨hrd, hrn⟩ := mem_inter_iff.mp hry
      obtain ⟨q, hqG, hqe⟩ := (hagree d hd).mp ⟨r, hrG, hrd⟩
      obtain ⟨t, htP, htr, htq⟩ := externalForcingFilter_compatible A.generic.1 hrG hqG
      have h1 : t ∈ A.booleanMemValue τ d := (hEreg d).2.1 q hqe t htP htq
      have h2 : t ∈ forcingNegation A.P A.R (A.booleanMemValue τ d) :=
        (forcingNegation_regular A.order (hEreg d).2.1).2.1 r hrn t htP htr
      have hemp := inter_forcingNegation_eq_empty A.order (hEreg d).1
      rw [SetTheory.mem_ext_iff] at hemp
      exact not_mem_empty ((hemp t).mp (mem_inter_iff.mpr ⟨h1, h2⟩))
    · obtain ⟨hrn, hre⟩ := mem_inter_iff.mp hry
      obtain ⟨q, hqG, hqd⟩ := (hagree d hd).mpr ⟨r, hrG, hre⟩
      obtain ⟨t, htP, htr, htq⟩ := externalForcingFilter_compatible A.generic.1 hrG hqG
      have hdreg : IsForcingRegular A.P A.R d := booleanConditions_regular ((hmemD d).mp hd).2
      have h1 : t ∈ d := hdreg.2.1 q hqd t htP htq
      have h2 : t ∈ forcingNegation A.P A.R d :=
        (forcingNegation_regular A.order hdreg.2.1).2.1 r hrn t htP htr
      have hemp := inter_forcingNegation_eq_empty A.order hdreg.1
      rw [SetTheory.mem_ext_iff] at hemp
      exact not_mem_empty ((hemp t).mp (mem_inter_iff.mpr ⟨h1, h2⟩))
  have hsep : ∀ y ∈ Y, ∀ t ∈ A.P, (⟨t, r⟩ₖ : V) ∈ A.R → t ∉ y := by
    rcases hcases with ⟨y, hy, hry⟩ | h
    · exact absurd hry (hnocase y hy)
    · exact h
  have hdisj : ∀ y ∈ Y, ∀ z : V, z ∈ coneRegular A.P A.R r → z ∈ y → False := by
    intro y hy z hz hzy
    obtain ⟨hzP, hh⟩ := mem_coneRegular_iff.mp hz
    obtain ⟨u, huP, hur, huz⟩ := hh z hzP (A.order.2.1 z hzP)
    exact hsep y hy u huP hur ((hYreg y hy).2.1 z hzy u huP huz)
  refine ⟨coneRegular A.P A.R r, coneRegular_mem_booleanConditions A.order hrP,
    ⟨r, hrG, self_mem_coneRegular A.order hrP⟩, fun d hd hdB ↦ ?_⟩
  have hdD : d ∈ D := (hmemD d).mpr ⟨hd, hdB⟩
  have hdreg : IsForcingRegular A.P A.R d := booleanConditions_regular hdB
  have hy1 : d ∩ forcingNegation A.P A.R (A.booleanMemValue τ d) ∈ Y :=
    (hY _).mpr (Or.inl ⟨d, hdD, rfl⟩)
  have hy2 : forcingNegation A.P A.R d ∩ A.booleanMemValue τ d ∈ Y :=
    (hY _).mpr (Or.inr ⟨d, hdD, rfl⟩)
  have hcone : IsForcingRegular A.P A.R (coneRegular A.P A.R r) := coneRegular_regular A.order r
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨hze, hzp⟩ := mem_inter_iff.mp hz
    refine mem_inter_iff.mpr ⟨?_, hzp⟩
    by_contra hzd
    obtain ⟨t, ht, htz⟩ := exists_forcingNegation_of_not_mem ((hEreg d).1 z hze) hzd hdreg.2.2
    have htP : t ∈ A.P := forcingNegation_subset _ _ _ t ht
    exact hdisj _ hy2 t (hcone.2.1 z hzp t htP htz)
      (mem_inter_iff.mpr ⟨ht, (hEreg d).2.1 z hze t htP htz⟩)
  · intro hz
    obtain ⟨hzd, hzp⟩ := mem_inter_iff.mp hz
    refine mem_inter_iff.mpr ⟨?_, hzp⟩
    by_contra hze
    obtain ⟨t, ht, htz⟩ := exists_forcingNegation_of_not_mem (hdreg.1 z hzd) hze (hEreg d).2.2
    have htP : t ∈ A.P := forcingNegation_subset _ _ _ t ht
    exact hdisj _ hy1 t (hcone.2.1 z hzp t htP htz)
      (mem_inter_iff.mpr ⟨hdreg.2.1 z hzd t htP htz, ht⟩)


end ForcingContext

end

end ZFVP
