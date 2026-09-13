import ZFVP.ModelTheory.SchmerlCofinalSpecialization

/-! Semantic bridges for the countability quantifier in Schmerl's expanded
structure. A coloring need only have countable range, and an uncountable
selected-level order with countable initial segments has uncountable cofinality.
-/

namespace ZFVP.Schmerl

open Set Order LO LO.FirstOrder

universe u v w z

variable {T : Type u} {C : Type v}

/-- Encode the range, without requiring the entire color sort to be countable. -/
noncomputable def countableColorCode (f : T → C) (h : (Set.range f).Countable) : T → ℕ := by
  let : Countable (Set.range f) := h.to_subtype
  let : Encodable (Set.range f) := Encodable.ofCountable _
  exact fun x ↦ Encodable.encode (⟨f x, Set.mem_range_self x⟩ : Set.range f)

theorem countableColorCode_eq_iff (f : T → C) (h : (Set.range f).Countable) (x y : T) :
    countableColorCode f h x = countableColorCode f h y ↔ f x = f y := by
  let : Countable (Set.range f) := h.to_subtype
  let : Encodable (Set.range f) := Encodable.ofCountable _
  change Encodable.encode (⟨f x, Set.mem_range_self x⟩ : Set.range f) =
    Encodable.encode (⟨f y, Set.mem_range_self y⟩ : Set.range f) ↔ f x = f y
  rw [Encodable.encode_injective.eq_iff, Subtype.mk.injEq]

theorem weaklySpecializes_countableColorCode_iff (r : T → T → Prop)
    (f : T → C) (h : (Set.range f).Countable) :
    WeaklySpecializes r (countableColorCode f h) ↔ WeaklySpecializes r f := by
  unfold WeaklySpecializes
  simp only [countableColorCode_eq_iff]

theorem branchDefinition_countableColorCode_iff (r : T → T → Prop)
    (f : T → C) (h : (Set.range f).Countable) (b x : T) :
    branchDefinition r (countableColorCode f h) b x ↔ branchDefinition r f b x := by
  simp only [branchDefinition, colorCone, countableColorCode_eq_iff]

namespace RankedTree

variable {I : Type w} [PartialOrder T] [LinearOrder I] [Nonempty I]

/-- Lemma A.6 with the exact countable-range assumption expressible using Q. -/
theorem IsBranch.exists_branchDefinition_countable_range
    {R : RankedTree T I} (hI : Cardinal.aleph0 < Order.cof I)
    {f : T → C} (hf : WeaklySpecializes (· ≤ ·) f) (hcolor : (Set.range f).Countable)
    {B : Set T} (hB : R.IsBranch B) :
    ∃ b ∈ B, ∀ x, branchDefinition (· ≤ ·) f b x ↔ x ∈ B := by
  obtain ⟨b, hb, hdef⟩ := hB.exists_branchDefinition_nat hI
    ((weaklySpecializes_countableColorCode_iff _ f hcolor).mpr hf)
  exact ⟨b, hb, fun x ↦ (branchDefinition_countableColorCode_iff _ f hcolor b x).symm.trans (hdef x)⟩

end RankedTree

/-- The cofinal-level candidate with an arbitrary color sort. -/
def cofinalColorBranchDefinition [LE T] (S : Set T) (f : T → C) (b x : T) : Prop :=
  ∃ y ∈ S, colorCone (· ≤ ·) f b y ∧ x ≤ y

theorem cofinalColorBranchDefinition_countableColorCode_iff [PartialOrder T]
    (S : Set T) (f : T → C) (h : (Set.range f).Countable) (b x : T) :
    cofinalBranchDefinition S (countableColorCode f h) b x ↔
      cofinalColorBranchDefinition S f b x := by
  simp only [cofinalBranchDefinition, cofinalColorBranchDefinition, colorCone,
    countableColorCode_eq_iff]

namespace RankedTree

variable {I : Type w} {K : Type z} [PartialOrder T] [LinearOrder I] [LinearOrder K]

/-- The cofinal-level form of A.6 also needs only a countable color range. -/
theorem exists_cofinalColorBranchDefinition [Nonempty K] (R : RankedTree T I) (c : K ↪o I)
    (hK : Cardinal.aleph0 < Order.cof K) (hcof : IsCofinal (Set.range c))
    {f : T → C} (hcolor : (Set.range f).Countable)
    (hf : WeaklySpecializes (· ≤ ·) (fun x : R.RankRestriction c ↦ f x.val))
    {B : Set T} (hB : R.IsBranch B) :
    ∃ b ∈ B, R.rank b ∈ Set.range c ∧
      ∀ x, cofinalColorBranchDefinition {y | R.rank y ∈ Set.range c} f b x ↔ x ∈ B := by
  have hcode : WeaklySpecializes (· ≤ ·)
      (fun x : R.RankRestriction c ↦ countableColorCode f hcolor x.val) := by
    intro x y z hxy hxz hfy hfz
    exact hf hxy hxz ((countableColorCode_eq_iff f hcolor _ _).mp hfy)
      ((countableColorCode_eq_iff f hcolor _ _).mp hfz)
  obtain ⟨b, hb, hbrank, hdef⟩ := R.exists_cofinalBranchDefinition c hK hcof hcode hB
  exact ⟨b, hb, hbrank, fun x ↦
    (cofinalColorBranchDefinition_countableColorCode_iff _ f hcolor b x).symm.trans (hdef x)⟩

end RankedTree

/-- In an expanded model the candidate is definable from the selected-level
predicate, tree order, and equality of colors; the colors need not be naturals. -/
theorem cofinalColorBranchDefinition_definable [LE T] {L : Language.{z}} [L.Eq]
    [LO.FirstOrder.Structure L T] [LO.FirstOrder.Structure.Eq L T]
    (S : Set T) (f : T → C) [L-predicate[T] (· ∈ S)] [L-relation[T] (· ≤ ·)]
    [L-relation[T] (fun x y ↦ f x = f y)] (b : T) :
    L-predicate[T] (cofinalColorBranchDefinition S f b) := by
  unfold cofinalColorBranchDefinition colorCone
  apply LO.FirstOrder.Language.Definable.exs
  apply LO.FirstOrder.Language.Definable.and
  · definability
  · apply LO.FirstOrder.Language.Definable.and
    · apply LO.FirstOrder.Language.Definable.or
      · definability
      · apply LO.FirstOrder.Language.Definable.and
        · definability
        · exact LO.FirstOrder.Language.DefinableRel.comp (P := fun x y ↦ f x = f y)
            (by definability) (by definability)
    · definability

/-- An uncountable linear order with countable initial segments cannot have
a countable cofinal subset. These are direct Q-countability conditions. -/
theorem uncountable_cof_of_countable_initials {I : Type u} [LinearOrder I] [Uncountable I]
    (hinitial : ∀ i : I, (Set.Iic i).Countable) : Cardinal.aleph0 < Order.cof I := by
  by_contra hn
  obtain ⟨A, hAcof, hAcard⟩ := Order.exists_cof_eq I
  have hAcount : A.Countable := by
    rw [← Set.countable_coe_iff, ← Cardinal.mk_le_aleph0_iff, hAcard]
    exact le_of_not_gt hn
  let : Countable A := hAcount.to_subtype
  have hu : (Set.univ : Set I) = ⋃ a : A, Set.Iic a.val := by
    ext i
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_Iic, true_iff]
    obtain ⟨a, ha, hia⟩ := hAcof i
    exact ⟨⟨a, ha⟩, hia⟩
  have hcount : (Set.univ : Set I).Countable := by
    rw [hu]
    exact Set.countable_iUnion (fun a ↦ hinitial a.val)
  exact not_countable (Set.countable_univ_iff.mp hcount)

/-- In an aleph-one-sized expanded model the same Q conditions give exact
cofinality aleph-one, as required by the specialization construction. -/
theorem cof_eq_aleph_one_of_countable_initials {I : Type u} [LinearOrder I] [Uncountable I]
    (hinitial : ∀ i : I, (Set.Iic i).Countable)
    (hcard : Cardinal.mk I ≤ Cardinal.aleph 1) : Order.cof I = Cardinal.aleph 1 := by
  apply le_antisymm
  · exact (Order.cof_le (show IsCofinal (Set.univ : Set I) from
      fun i ↦ ⟨i, Set.mem_univ i, le_rfl⟩)).trans (by simpa using hcard)
  · exact Cardinal.aleph_one_le_iff.mpr (uncountable_cof_of_countable_initials hinitial)

/-- The explicit three-clause Q witness: an uncountable cofinal predicate whose
intersection with every bounded initial segment is countable. -/
theorem uncountable_cof_of_cofinal_countable_sections {I : Type u} [LinearOrder I]
    (D : Set I) (hD : ¬ D.Countable)
    (hsections : ∀ i : I, {x ∈ D | x ≤ i}.Countable) (hcof : IsCofinal D) :
    Cardinal.aleph0 < Order.cof I := by
  let : Uncountable D := not_countable_iff.mp (fun h ↦ hD (Set.countable_coe_iff.mp h))
  have hinitial (d : D) : (Set.Iic d).Countable := by
    change ({x : D | x.val ≤ d.val}).Countable
    have h := (hsections d.val).preimage (f := fun x : D ↦ x.val) Subtype.val_injective
    simpa only [Set.preimage_ofPred_eq, Subtype.coe_prop, true_and] using h
  rw [← Order.cof_eq_of_isCofinal hcof]
  exact uncountable_cof_of_countable_initials hinitial

end ZFVP.Schmerl
