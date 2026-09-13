import ZFVP.ModelTheory.SchmerlInternalSpecializationCCC
import ZFVP.SetTheory.ProductForcing

/-! The internal square of the strict-specialization poset is ccc.
Pairs of conditions are encoded on two disjoint tagged copies of the tree. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The original order within each of two copies of `D`. -/
noncomputable def internalTaggedOrder (D S : V) : V :=
  {z ∈ (D ×ˢ (2 : V)) ×ˢ (D ×ˢ (2 : V)) ;
    kpair.π₂ (kpair.π₁ z) = kpair.π₂ (kpair.π₂ z) ∧
    ⟨kpair.π₁ (kpair.π₁ z), kpair.π₁ (kpair.π₂ z)⟩ₖ ∈ S}

theorem pair_mem_internalTaggedOrder (D S x y : V) :
    ⟨x, y⟩ₖ ∈ internalTaggedOrder D S ↔
      x ∈ D ×ˢ (2 : V) ∧ y ∈ D ×ˢ (2 : V) ∧
      kpair.π₂ x = kpair.π₂ y ∧ ⟨kpair.π₁ x, kpair.π₁ y⟩ₖ ∈ S := by
  simp only [internalTaggedOrder, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

theorem pair_mem_internalTaggedOrder_nodes (D S x y i j : V) :
    ⟨⟨x, i⟩ₖ, ⟨y, j⟩ₖ⟩ₖ ∈ internalTaggedOrder D S ↔
      x ∈ D ∧ i ∈ (2 : V) ∧ y ∈ D ∧ j ∈ (2 : V) ∧ i = j ∧ ⟨x, y⟩ₖ ∈ S := by
  simp only [pair_mem_internalTaggedOrder, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

theorem internalTaggedOrder_reflexive {D S : V} (href : ∀ x ∈ D, ⟨x, x⟩ₖ ∈ S) :
    ∀ x ∈ D ×ˢ (2 : V), ⟨x, x⟩ₖ ∈ internalTaggedOrder D S := by
  intro x hx
  obtain ⟨a, ha, i, hi, rfl⟩ := mem_prod_iff.mp hx
  exact (pair_mem_internalTaggedOrder_nodes _ _ _ _ _ _).mpr ⟨ha, hi, ha, hi, rfl, href a ha⟩

theorem internalTaggedOrder_below {D S : V}
    (hbelow : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
      ⟨x, z⟩ₖ ∈ S → ⟨y, z⟩ₖ ∈ S → ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S) :
    ∀ x ∈ D ×ˢ (2 : V), ∀ y ∈ D ×ˢ (2 : V), ∀ z ∈ D ×ˢ (2 : V),
      ⟨x, z⟩ₖ ∈ internalTaggedOrder D S → ⟨y, z⟩ₖ ∈ internalTaggedOrder D S →
      ⟨x, y⟩ₖ ∈ internalTaggedOrder D S ∨ ⟨y, x⟩ₖ ∈ internalTaggedOrder D S := by
  intro x hx y hy z hz hxz hyz
  obtain ⟨a, ha, i, hi, rfl⟩ := mem_prod_iff.mp hx
  obtain ⟨b, hb, j, hj, rfl⟩ := mem_prod_iff.mp hy
  obtain ⟨c, hc, k, _, rfl⟩ := mem_prod_iff.mp hz
  obtain ⟨_, _, _, _, hik, hac⟩ := (pair_mem_internalTaggedOrder_nodes _ _ _ _ _ _).mp hxz
  obtain ⟨_, _, _, _, hjk, hbc⟩ := (pair_mem_internalTaggedOrder_nodes _ _ _ _ _ _).mp hyz
  rcases hbelow a ha b hb c hc hac hbc with hab | hba
  · exact Or.inl ((pair_mem_internalTaggedOrder_nodes _ _ _ _ _ _).mpr
      ⟨ha, hi, hb, hj, hik.trans hjk.symm, hab⟩)
  · exact Or.inr ((pair_mem_internalTaggedOrder_nodes _ _ _ _ _ _).mpr
      ⟨hb, hj, ha, hi, hjk.trans hik.symm, hba⟩)

/-- Projection is internally injective on a tagged chain: comparability
forces the tags to agree. Its image is a chain in the original tree. -/
theorem internalTaggedOrder_chains_countable {D S : V}
    (hchains : ∀ C : V, C ⊆ D →
      (∀ x ∈ C, ∀ y ∈ C, ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S) → IsInternallyCountable C)
    (C : V) (hC : C ⊆ D ×ˢ (2 : V))
    (hchain : ∀ x ∈ C, ∀ y ∈ C,
      ⟨x, y⟩ₖ ∈ internalTaggedOrder D S ∨ ⟨y, x⟩ₖ ∈ internalTaggedOrder D S) :
    IsInternallyCountable C := by
  let F : V → V := kpair.π₁
  have hF : ℒₛₑₜ-function₁ F := by definability
  have hproj : repl F hF C ⊆ D := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := (repl_spec hF).mp ha
    obtain ⟨b, hb, i, _, rfl⟩ := mem_prod_iff.mp (hC x hx)
    simpa only [F, kpair.π₁_kpair] using hb
  have hprojchain : ∀ x ∈ repl F hF C, ∀ y ∈ repl F hF C,
      ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := (repl_spec hF).mp hx
    obtain ⟨b, hb, rfl⟩ := (repl_spec hF).mp hy
    exact (hchain a ha b hb).imp
      (fun h ↦ ((pair_mem_internalTaggedOrder _ _ _ _).mp h).2.2.2)
      (fun h ↦ ((pair_mem_internalTaggedOrder _ _ _ _).mp h).2.2.2)
  apply internallyCountable_of_cardLE (hchains _ hproj hprojchain)
  apply cardLE_of_injective_map F hF
  · intro x hx
    exact (repl_spec hF).mpr ⟨x, hx, rfl⟩
  · intro x hx y hy he
    obtain ⟨a, _, i, _, rfl⟩ := mem_prod_iff.mp (hC x hx)
    obtain ⟨b, _, j, _, rfl⟩ := mem_prod_iff.mp (hC y hy)
    have hab : a = b := by simpa only [F, kpair.π₁_kpair] using he
    have hij : i = j := by
      rcases hchain _ hx _ hy with h | h
      · exact ((pair_mem_internalTaggedOrder_nodes _ _ _ _ _ _).mp h).2.2.2.2.1
      · exact ((pair_mem_internalTaggedOrder_nodes _ _ _ _ _ _).mp h).2.2.2.2.1.symm
    exact kpair_iff.mpr ⟨hab, hij⟩

/-- Tag every node of a condition's graph, retaining its assigned color. -/
noncomputable def internalTagGraph (i p : V) : V :=
  repl (fun a ↦ ⟨⟨kpair.π₁ a, i⟩ₖ, kpair.π₂ a⟩ₖ) (by definability) p

instance internalTagGraph_definable : ℒₛₑₜ-function₂[V] internalTagGraph := by
  have h : ℒₛₑₜ-relation₃[V] (fun G i p ↦ ∀ z,
    z ∈ G ↔ ∃ a ∈ p, z = ⟨⟨kpair.π₁ a, i⟩ₖ, kpair.π₂ a⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [internalTagGraph, repl_spec]
  rfl

theorem pair_mem_internalTagGraph (i p x c : V) [IsFunction p] :
    ⟨x, c⟩ₖ ∈ internalTagGraph i p ↔ ∃ a, x = ⟨a, i⟩ₖ ∧ ⟨a, c⟩ₖ ∈ p := by
  rw [internalTagGraph, repl_spec]
  constructor
  · rintro ⟨z, hz, he⟩
    obtain ⟨a, b, rfl⟩ := IsFunction.mem_eq_kpair hz
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at he
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact ⟨a, rfl, hz⟩
  · rintro ⟨a, rfl, ha⟩
    exact ⟨⟨a, c⟩ₖ, ha, by simp⟩

theorem pair_mem_internalTagGraph_tag (i j p x c : V) [IsFunction p] :
    ⟨⟨x, i⟩ₖ, c⟩ₖ ∈ internalTagGraph j p ↔ i = j ∧ ⟨x, c⟩ₖ ∈ p := by
  simp only [pair_mem_internalTagGraph, kpair_iff]
  constructor
  · rintro ⟨a, ⟨rfl, hij⟩, ha⟩
    exact ⟨hij, ha⟩
  · rintro ⟨rfl, hx⟩
    exact ⟨x, ⟨rfl, rfl⟩, hx⟩

theorem internalTagGraph_isFunction (i p : V) [IsFunction p] :
    IsFunction (internalTagGraph i p) := by
  apply isFunction_iff.mpr
  apply mem_function.intro
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := (repl_spec (show ℒₛₑₜ-function₁[V]
      (fun a ↦ ⟨⟨kpair.π₁ a, i⟩ₖ, kpair.π₂ a⟩ₖ) by definability)).mp hz
    exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hz, mem_range_of_kpair_mem hz⟩
  · intro x hx
    obtain ⟨c, hxc⟩ := mem_domain_iff.mp hx
    refine ⟨c, hxc, ?_⟩
    intro d hxd
    obtain ⟨a, hxa, hac⟩ := (pair_mem_internalTagGraph i p x c).mp hxc
    obtain ⟨b, hxb, hbd⟩ := (pair_mem_internalTagGraph i p x d).mp hxd
    have hab : a = b := (kpair_iff.mp (hxa.symm.trans hxb)).1
    subst b
    exact IsFunction.unique hbd hac

theorem internalTagGraph_mem_finitePartialFunctions {D B p i : V}
    (hp : p ∈ finitePartialFunctions D B) (hi : i ∈ (2 : V)) :
    internalTagGraph i p ∈ finitePartialFunctions (D ×ˢ (2 : V)) B := by
  obtain ⟨hpD, hpf, hpfin⟩ := (mem_finitePartialFunctions _ _ _).mp hp
  have : IsFunction p := hpf
  apply (mem_finitePartialFunctions _ _ _).mpr
  refine ⟨?_, internalTagGraph_isFunction i p, ?_⟩
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := (repl_spec (show ℒₛₑₜ-function₁[V]
      (fun a ↦ ⟨⟨kpair.π₁ a, i⟩ₖ, kpair.π₂ a⟩ₖ) by definability)).mp hz
    obtain ⟨x, c, rfl⟩ := IsFunction.mem_eq_kpair ha
    obtain ⟨hx, hc⟩ := kpair_mem_iff.mp (hpD _ ha)
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
      kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨hx, hi⟩, hc⟩
  · exact internallyFinite_domain (internallyFinite_repl _ _ (internallyFinite_function hpfin))

/-- Put the first condition on tag zero and the second on tag one. -/
noncomputable def internalPairedCondition (p q : V) : V :=
  internalTagGraph (0 : V) p ∪ internalTagGraph (1 : V) q

instance internalPairedCondition_definable : ℒₛₑₜ-function₂[V] internalPairedCondition := by
  unfold internalPairedCondition
  definability

theorem pair_mem_internalPairedCondition_zero (p q x c : V) [IsFunction p] [IsFunction q] :
    ⟨⟨x, (0 : V)⟩ₖ, c⟩ₖ ∈ internalPairedCondition p q ↔ ⟨x, c⟩ₖ ∈ p := by
  simp [internalPairedCondition, pair_mem_internalTagGraph_tag]

theorem pair_mem_internalPairedCondition_one (p q x c : V) [IsFunction p] [IsFunction q] :
    ⟨⟨x, (1 : V)⟩ₖ, c⟩ₖ ∈ internalPairedCondition p q ↔ ⟨x, c⟩ₖ ∈ q := by
  simp [internalPairedCondition, pair_mem_internalTagGraph_tag]

theorem internalPairedCondition_mem_specialization {D S p q : V}
    (hp : p ∈ internalSpecialization D S) (hq : q ∈ internalSpecialization D S) :
    internalPairedCondition p q ∈
      internalSpecialization (D ×ˢ (2 : V)) (internalTaggedOrder D S) := by
  obtain ⟨hpfin, hpstrict⟩ := (mem_internalSpecialization _ _ _).mp hp
  obtain ⟨hqfin, hqstrict⟩ := (mem_internalSpecialization _ _ _).mp hq
  have : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp hpfin).2.1
  have : IsFunction q := ((mem_finitePartialFunctions _ _ _).mp hqfin).2.1
  apply (mem_internalSpecialization _ _ _).mpr
  constructor
  · apply finitePartialFunction_union
      (internalTagGraph_mem_finitePartialFunctions hpfin (by simp : (0 : V) ∈ (2 : V)))
      (internalTagGraph_mem_finitePartialFunctions hqfin (by simp : (1 : V) ∈ (2 : V)))
    intro x c d hxc hxd
    obtain ⟨a, hxa, _⟩ := (pair_mem_internalTagGraph 0 p x c).mp hxc
    obtain ⟨b, hxb, _⟩ := (pair_mem_internalTagGraph 1 q x d).mp hxd
    exact False.elim (zero_ne_one (kpair_iff.mp (hxa.symm.trans hxb)).2)
  · intro x y c hx hy hxy
    rcases mem_union_iff.mp hx with hx | hx <;> rcases mem_union_iff.mp hy with hy | hy
    · obtain ⟨a, rfl, hac⟩ := (pair_mem_internalTagGraph 0 p x c).mp hx
      obtain ⟨b, rfl, hbc⟩ := (pair_mem_internalTagGraph 0 p y c).mp hy
      have hab := ((pair_mem_internalTaggedOrder_nodes _ _ _ _ _ _).mp hxy).2.2.2.2.2
      exact congrArg (fun z : V ↦ ⟨z, (0 : V)⟩ₖ) (hpstrict a b c hac hbc hab)
    · obtain ⟨a, rfl, _⟩ := (pair_mem_internalTagGraph 0 p x c).mp hx
      obtain ⟨b, rfl, _⟩ := (pair_mem_internalTagGraph 1 q y c).mp hy
      exact False.elim (zero_ne_one
        ((pair_mem_internalTaggedOrder_nodes _ _ _ _ _ _).mp hxy).2.2.2.2.1)
    · obtain ⟨a, rfl, _⟩ := (pair_mem_internalTagGraph 1 q x c).mp hx
      obtain ⟨b, rfl, _⟩ := (pair_mem_internalTagGraph 0 p y c).mp hy
      exact False.elim (one_ne_zero
        ((pair_mem_internalTaggedOrder_nodes _ _ _ _ _ _).mp hxy).2.2.2.2.1)
    · obtain ⟨a, rfl, hac⟩ := (pair_mem_internalTagGraph 1 q x c).mp hx
      obtain ⟨b, rfl, hbc⟩ := (pair_mem_internalTagGraph 1 q y c).mp hy
      have hab := ((pair_mem_internalTaggedOrder_nodes _ _ _ _ _ _).mp hxy).2.2.2.2.2
      exact congrArg (fun z : V ↦ ⟨z, (1 : V)⟩ₖ) (hqstrict a b c hac hbc hab)

theorem internalPairedCondition_injective (p q r s : V)
    [IsFunction p] [IsFunction q] [IsFunction r] [IsFunction s]
    (he : internalPairedCondition p q = internalPairedCondition r s) : p = r ∧ q = s := by
  have hfunext (a b : V) [IsFunction a] [IsFunction b]
      (h : ∀ x c : V, ⟨x, c⟩ₖ ∈ a ↔ ⟨x, c⟩ₖ ∈ b) : a = b := by
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨x, c, rfl⟩ := IsFunction.mem_eq_kpair hz
      exact (h x c).mp hz
    · intro hz
      obtain ⟨x, c, rfl⟩ := IsFunction.mem_eq_kpair hz
      exact (h x c).mpr hz
  constructor
  · apply hfunext p r
    intro x c
    rw [← pair_mem_internalPairedCondition_zero p q x c, he,
      pair_mem_internalPairedCondition_zero r s x c]
  · apply hfunext q s
    intro x c
    rw [← pair_mem_internalPairedCondition_one p q x c, he,
      pair_mem_internalPairedCondition_one r s x c]

/-- Compatibility of the tagged conditions implies compatibility in each
coordinate of the original product. -/
theorem internalPairedCondition_compatible_reflects {D S p q r s : V}
    (hp : p ∈ internalSpecialization D S) (hq : q ∈ internalSpecialization D S)
    (hr : r ∈ internalSpecialization D S) (hs : s ∈ internalSpecialization D S)
    (h : ForcingCompatible
      (internalSpecialization (D ×ˢ (2 : V)) (internalTaggedOrder D S))
      (reverseInclusionOrder (internalSpecialization (D ×ˢ (2 : V)) (internalTaggedOrder D S)))
      (internalPairedCondition p q) (internalPairedCondition r s)) :
    ForcingCompatible (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) p r ∧
    ForcingCompatible (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) q s := by
  have hfunc (a : V) (ha : a ∈ internalSpecialization D S) : IsFunction a :=
    ((mem_finitePartialFunctions _ _ _).mp ((mem_internalSpecialization _ _ _).mp ha).1).2.1
  have : IsFunction p := hfunc p hp
  have : IsFunction q := hfunc q hq
  have : IsFunction r := hfunc r hr
  have : IsFunction s := hfunc s hs
  obtain ⟨hfun, hstrict⟩ := (internalSpecialization_compatible_iff
    (internalPairedCondition_mem_specialization hp hq)
    (internalPairedCondition_mem_specialization hr hs)).mp h
  have hreflect (a b i : V) (ha : a ∈ internalSpecialization D S)
      (hb : b ∈ internalSpecialization D S) (hi : i ∈ (2 : V))
      (hea : ∀ x c : V, ⟨x, c⟩ₖ ∈ a → ⟨⟨x, i⟩ₖ, c⟩ₖ ∈ internalPairedCondition p q)
      (heb : ∀ x c : V, ⟨x, c⟩ₖ ∈ b → ⟨⟨x, i⟩ₖ, c⟩ₖ ∈ internalPairedCondition r s) :
      ForcingCompatible (internalSpecialization D S)
        (reverseInclusionOrder (internalSpecialization D S)) a b := by
    apply (internalSpecialization_compatible_iff ha hb).mpr
    refine ⟨fun x c d hxc hxd ↦ hfun ⟨x, i⟩ₖ c d (hea x c hxc) (heb x d hxd), ?_⟩
    intro x y c hx hy hxy
    have hxD : x ∈ D := finitePartialFunction_domain ((mem_internalSpecialization _ _ _).mp ha).1
      x (mem_domain_of_kpair_mem hx)
    have hyD : y ∈ D := finitePartialFunction_domain ((mem_internalSpecialization _ _ _).mp hb).1
      y (mem_domain_of_kpair_mem hy)
    have htagged : ⟨⟨x, i⟩ₖ, ⟨y, i⟩ₖ⟩ₖ ∈ internalTaggedOrder D S ∨
        ⟨⟨y, i⟩ₖ, ⟨x, i⟩ₖ⟩ₖ ∈ internalTaggedOrder D S :=
      hxy.imp (fun hxy ↦ (pair_mem_internalTaggedOrder_nodes _ _ _ _ _ _).mpr
        ⟨hxD, hi, hyD, hi, rfl, hxy⟩)
        (fun hyx ↦ (pair_mem_internalTaggedOrder_nodes _ _ _ _ _ _).mpr
          ⟨hyD, hi, hxD, hi, rfl, hyx⟩)
    exact (kpair_iff.mp (hstrict ⟨x, i⟩ₖ ⟨y, i⟩ₖ c (hea x c hx) (heb y c hy) htagged)).1
  exact ⟨hreflect p r 0 hp hr (by simp)
    (fun x c ↦ (pair_mem_internalPairedCondition_zero p q x c).mpr)
    (fun x c ↦ (pair_mem_internalPairedCondition_zero r s x c).mpr),
    hreflect q s 1 hq hs (by simp)
      (fun x c ↦ (pair_mem_internalPairedCondition_one p q x c).mpr)
      (fun x c ↦ (pair_mem_internalPairedCondition_one r s x c).mpr)⟩

theorem internalSpecialization_square_poset (D S : V) :
    let P := internalSpecialization D S
    let R := reverseInclusionOrder P
    IsForcingPoset (P ×ˢ P) (productOrder P R P R) := by
  let P := internalSpecialization D S
  let R := reverseInclusionOrder P
  have hP := internalSpecialization_poset D S
  refine ⟨productOrder_preorder hP.1 hP.1, ?_⟩
  intro x hx y hy hxy hyx
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hx
  obtain ⟨r, hr, s, hs, rfl⟩ := mem_prod_iff.mp hy
  obtain ⟨_, _, _, _, hpr, hqs⟩ := (pair_mem_productOrder_iff P R P R p q r s).mp hxy
  obtain ⟨_, _, _, _, hrp, hsq⟩ := (pair_mem_productOrder_iff P R P R r s p q).mp hyx
  exact kpair_iff.mpr ⟨hP.2 p hp r hr hpr hrp, hP.2 q hq s hs hqs hsq⟩

/-- The actual internal product of the specialization poset with itself has
only internally countable antichains. The proof uses the tagged tree. -/
theorem internalSpecialization_square_countable_antichains (hAC : InternalChoice V)
    {D S : V} (href : ∀ x ∈ D, ⟨x, x⟩ₖ ∈ S)
    (hbelow : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
      ⟨x, z⟩ₖ ∈ S → ⟨y, z⟩ₖ ∈ S → ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S)
    (hchains : ∀ C : V, C ⊆ D →
      (∀ x ∈ C, ∀ y ∈ C, ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S) → IsInternallyCountable C)
    (A : V)
    (hA : IsForcingAntichain
      (internalSpecialization D S ×ˢ internalSpecialization D S)
      (productOrder (internalSpecialization D S) (reverseInclusionOrder (internalSpecialization D S))
        (internalSpecialization D S) (reverseInclusionOrder (internalSpecialization D S))) A) :
    IsInternallyCountable A := by
  let P := internalSpecialization D S
  let R := reverseInclusionOrder P
  let Q := internalSpecialization (D ×ˢ (2 : V)) (internalTaggedOrder D S)
  let F : V → V := fun z ↦ internalPairedCondition (kpair.π₁ z) (kpair.π₂ z)
  have hF : ℒₛₑₜ-function₁ F := by dsimp [F]; definability
  have hfunc (p : V) (hp : p ∈ P) : IsFunction p :=
    ((mem_finitePartialFunctions _ _ _).mp ((mem_internalSpecialization _ _ _).mp hp).1).2.1
  have hmap (z : V) (hz : z ∈ A) : F z ∈ Q := by
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp (hA.1 z hz)
    simpa only [F, kpair.π₁_kpair, kpair.π₂_kpair] using
      internalPairedCondition_mem_specialization hp hq
  have hinj (z : V) (hz : z ∈ A) (w : V) (hw : w ∈ A) (he : F z = F w) : z = w := by
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp (hA.1 z hz)
    obtain ⟨r, hr, s, hs, rfl⟩ := mem_prod_iff.mp (hA.1 w hw)
    have : IsFunction p := hfunc p hp
    have : IsFunction q := hfunc q hq
    have : IsFunction r := hfunc r hr
    have : IsFunction s := hfunc s hs
    simp only [F, kpair.π₁_kpair, kpair.π₂_kpair] at he
    exact kpair_iff.mpr (internalPairedCondition_injective p q r s he)
  have hreflect (z : V) (hz : z ∈ A) (w : V) (hw : w ∈ A)
      (h : ForcingCompatible Q (reverseInclusionOrder Q) (F z) (F w)) :
      ForcingCompatible (P ×ˢ P) (productOrder P R P R) z w := by
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp (hA.1 z hz)
    obtain ⟨r, hr, s, hs, rfl⟩ := mem_prod_iff.mp (hA.1 w hw)
    simp only [F, kpair.π₁_kpair, kpair.π₂_kpair] at h
    exact (product_compatible_iff hp hq hr hs).mpr
      (internalPairedCondition_compatible_reflects hp hq hr hs h)
  have hanti : IsForcingAntichain Q (reverseInclusionOrder Q) (repl F hF A) := by
    constructor
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := (repl_spec hF).mp hx
      exact hmap z hz
    · intro x hx y hy hne hcomp
      obtain ⟨z, hz, rfl⟩ := (repl_spec hF).mp hx
      obtain ⟨w, hw, rfl⟩ := (repl_spec hF).mp hy
      exact hA.2 z hz w hw (fun he ↦ hne (congrArg F he)) (hreflect z hz w hw hcomp)
  have hcount := internalSpecialization_countable_antichains hAC
    (internalTaggedOrder_reflexive href) (internalTaggedOrder_below hbelow)
    (internalTaggedOrder_chains_countable hchains) (repl F hF A) hanti
  apply internallyCountable_of_cardLE hcount
  exact cardLE_of_injective_map F hF
    (fun z hz ↦ (repl_spec hF).mpr ⟨z, hz, rfl⟩) hinj

end ZFVP.Schmerl
