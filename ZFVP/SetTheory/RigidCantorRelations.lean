import ZFVP.SetTheory.CantorLexOrder
import ZFVP.SetTheory.NaturalPredecessor

/-! The remaining case of the Hamkins-Palumbo theorem that in ZF every set of reals carries a
rigid relation. A Dedekind infinite set of reals contains an injective `ω`-sequence `z`, and the
relation built from `z` below pins down every point: the sequence itself is rigidified by a chain
whose steps are visible in the relation, and each real outside the sequence is pinned by the
coordinates at which it takes the value `1`, read off from which members of the sequence relate
to it. Together with the Dedekind finite case this gives a rigid relation on every subset of
Cantor space. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The relation attached to an injective sequence -/

/-- The relation on `A` attached to a sequence `z`. The point `z ‘ 0` is the only loop, its
predecessors are exactly the values of `z`, the values `z ‘ (succ n)` form a chain along which
the index increases, and `z ‘ (succ n)` relates to a point outside the range of `z` exactly when
that point takes the value `1` at the coordinate `n`. -/
noncomputable def cantorChainRelation (A z : V) : V :=
  {w ∈ A ×ˢ A ;
    (kpair.π₁ w = z ‘ 0 ∧ kpair.π₂ w = z ‘ 0) ∨
    (∃ n ∈ (ω : V), kpair.π₁ w = z ‘ (succ n) ∧ kpair.π₂ w = z ‘ 0) ∨
    (∃ n ∈ (ω : V), kpair.π₁ w = z ‘ (succ n) ∧ kpair.π₂ w = z ‘ (succ (succ n))) ∨
    (∃ n ∈ (ω : V), kpair.π₁ w = z ‘ (succ n) ∧ kpair.π₂ w ∉ range z ∧ (kpair.π₂ w) ‘ n = 1)}

instance cantorChainRelation_definable : ℒₛₑₜ-function₂[V] cantorChainRelation := by
  have h : ℒₛₑₜ-relation₃ (fun S A z : V ↦ ∀ w, w ∈ S ↔ w ∈ A ×ˢ A ∧
      ((kpair.π₁ w = z ‘ 0 ∧ kpair.π₂ w = z ‘ 0) ∨
       (∃ n ∈ (ω : V), kpair.π₁ w = z ‘ (succ n) ∧ kpair.π₂ w = z ‘ 0) ∨
       (∃ n ∈ (ω : V), kpair.π₁ w = z ‘ (succ n) ∧ kpair.π₂ w = z ‘ (succ (succ n))) ∨
       (∃ n ∈ (ω : V), kpair.π₁ w = z ‘ (succ n) ∧ kpair.π₂ w ∉ range z ∧
         (kpair.π₂ w) ‘ n = 1))) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = cantorChainRelation (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp [cantorChainRelation]

theorem cantorChainRelation_subset (A z : V) : cantorChainRelation A z ⊆ A ×ˢ A :=
  fun _ hw ↦ (mem_sep_iff.mp hw).1

theorem kpair_mem_cantorChainRelation {A z : V} (x y : V) (hx : x ∈ A) (hy : y ∈ A) :
    ⟨x, y⟩ₖ ∈ cantorChainRelation A z ↔
      (x = z ‘ 0 ∧ y = z ‘ 0) ∨
      (∃ n ∈ (ω : V), x = z ‘ (succ n) ∧ y = z ‘ 0) ∨
      (∃ n ∈ (ω : V), x = z ‘ (succ n) ∧ y = z ‘ (succ (succ n))) ∨
      (∃ n ∈ (ω : V), x = z ‘ (succ n) ∧ y ∉ range z ∧ y ‘ n = 1) := by
  simp only [cantorChainRelation, mem_sep_iff, kpair.π₁_kpair, kpair.π₂_kpair,
    kpair_mem_iff, and_iff_right (And.intro hx hy)]

/-! ### The relation is rigid -/

set_option maxHeartbeats 1000000 in
/-- The relation attached to an injective sequence in a set of reals is rigid. -/
theorem isRigidRelation_cantorChainRelation {A z : V} (hA : A ⊆ cantorSpace V)
    (hz : z ∈ A ^ (ω : V)) (hinj : Injective z) :
    IsRigidRelation A (cantorChainRelation A z) := by
  classical
  refine ⟨cantorChainRelation_subset A z, ?_⟩
  have hzF : IsFunction z := IsFunction.of_mem hz
  have h0ω : (0 : V) ∈ (ω : V) := by simp
  have hmem : ∀ n ∈ (ω : V), z ‘ n ∈ A := fun n hn ↦ function_value_mem hz hn
  have hval : ∀ n ∈ (ω : V), z ‘ n ∈ range z := fun n hn ↦ value_mem_range hz hn
  have he : z ‘ 0 ∈ A := hmem 0 h0ω
  have hzinj : ∀ m ∈ (ω : V), ∀ n ∈ (ω : V), z ‘ m = z ‘ n → m = n :=
    fun m hm n hn h ↦ injective_value_eq hz hinj hm hn h
  -- basic separation facts about the values of `z`
  have hsuccne : ∀ n ∈ (ω : V), z ‘ (succ n) ≠ z ‘ 0 := by
    intro n hn h
    have hs : succ n = (0 : V) := hzinj _ (ω_succ_closed hn) _ h0ω h
    have hh : n ∈ succ n := mem_succ_self n
    rw [hs] at hh
    exact not_mem_empty hh
  have hsuccinj : ∀ m ∈ (ω : V), ∀ n ∈ (ω : V), z ‘ (succ m) = z ‘ (succ n) → m = n := by
    intro m hm n hn h
    have hs : succ m = succ n := hzinj _ (ω_succ_closed hm) _ (ω_succ_closed hn) h
    have : IsOrdinal m := IsOrdinal.of_mem hm
    have : IsOrdinal n := IsOrdinal.of_mem hn
    simpa only [sUnion_succ_of_transitive] using congrArg (fun w : V ↦ ⋃ˢ w) hs
  have hnotfix : ∀ n ∈ (ω : V), z ‘ (succ n) ≠ z ‘ (succ (succ n)) := by
    intro n hn h
    have hnn : n = succ n := hsuccinj n hn (succ n) (ω_succ_closed hn) h
    have hh : n ∈ succ n := mem_succ_self n
    rw [← hnn] at hh
    exact mem_irrefl n hh
  have hshape : ∀ a, a ∈ range z → a ≠ z ‘ 0 → ∃ i ∈ (ω : V), a = z ‘ (succ i) := by
    intro a har hane
    obtain ⟨n, hn⟩ := mem_range_iff.mp har
    have hnω : n ∈ (ω : V) := by
      have h := mem_domain_of_kpair_mem hn
      rwa [domain_eq_of_mem_function hz] at h
    have hav : a = z ‘ n := (value_eq_of_kpair_mem hn).symm
    rcases internalNatural_cases hnω with rfl | ⟨i, hi, rfl⟩
    · exact absurd hav hane
    · exact ⟨i, hi, hav⟩
  -- the four ways a pair can lie in the relation, read off case by case
  have hloop : ∀ a ∈ A, (⟨a, a⟩ₖ ∈ cantorChainRelation A z ↔ a = z ‘ 0) := by
    intro a ha
    rw [kpair_mem_cantorChainRelation a a ha ha]
    constructor
    · rintro (⟨h, -⟩ | ⟨n, hn, h1, h2⟩ | ⟨n, hn, h1, h2⟩ | ⟨n, hn, h1, h2, -⟩)
      · exact h
      · exact absurd (h1.symm.trans h2) (hsuccne n hn)
      · exact absurd (h1.symm.trans h2) (hnotfix n hn)
      · exact absurd (by rw [h1]; exact hval _ (ω_succ_closed hn)) h2
    · intro h
      exact Or.inl ⟨h, h⟩
  have hpred : ∀ a ∈ A, (⟨a, z ‘ 0⟩ₖ ∈ cantorChainRelation A z ↔ a ∈ range z) := by
    intro a ha
    rw [kpair_mem_cantorChainRelation a (z ‘ 0) ha he]
    constructor
    · rintro (⟨h, -⟩ | ⟨n, hn, h1, -⟩ | ⟨n, hn, -, h2⟩ | ⟨n, hn, -, h2, -⟩)
      · rw [h]; exact hval 0 h0ω
      · rw [h1]; exact hval _ (ω_succ_closed hn)
      · exact absurd h2.symm (hsuccne (succ n) (ω_succ_closed hn))
      · exact absurd (hval 0 h0ω) h2
    · intro har
      by_cases h : a = z ‘ 0
      · exact Or.inl ⟨h, rfl⟩
      · obtain ⟨i, hi, hai⟩ := hshape a har h
        exact Or.inr (Or.inl ⟨i, hi, hai, rfl⟩)
  have hchain : ∀ m ∈ (ω : V), ∀ n ∈ (ω : V),
      (⟨z ‘ (succ m), z ‘ (succ n)⟩ₖ ∈ cantorChainRelation A z ↔ n = succ m) := by
    intro m hm n hn
    rw [kpair_mem_cantorChainRelation _ _ (hmem _ (ω_succ_closed hm))
      (hmem _ (ω_succ_closed hn))]
    constructor
    · rintro (⟨h, -⟩ | ⟨k, hk, -, h2⟩ | ⟨k, hk, h1, h2⟩ | ⟨k, hk, -, h2, -⟩)
      · exact absurd h (hsuccne m hm)
      · exact absurd h2 (hsuccne n hn)
      · rw [hsuccinj n hn (succ k) (ω_succ_closed hk) h2, hsuccinj m hm k hk h1]
      · exact absurd (hval _ (ω_succ_closed hn)) h2
    · rintro rfl
      exact Or.inr (Or.inr (Or.inl ⟨m, hm, rfl, rfl⟩))
  have houter : ∀ n ∈ (ω : V), ∀ y ∈ A, y ∉ range z →
      (⟨z ‘ (succ n), y⟩ₖ ∈ cantorChainRelation A z ↔ y ‘ n = 1) := by
    intro n hn y hy hyr
    rw [kpair_mem_cantorChainRelation _ _ (hmem _ (ω_succ_closed hn)) hy]
    constructor
    · rintro (⟨h, -⟩ | ⟨k, hk, -, h2⟩ | ⟨k, hk, -, h2⟩ | ⟨k, hk, h1, -, h3⟩)
      · exact absurd h (hsuccne n hn)
      · exact absurd (by rw [h2]; exact hval 0 h0ω) hyr
      · exact absurd (by rw [h2]; exact hval _ (ω_succ_closed (ω_succ_closed hk))) hyr
      · rwa [hsuccinj n hn k hk h1]
    · intro h
      exact Or.inr (Or.inr (Or.inr ⟨n, hn, rfl, hyr, h⟩))
  -- now fix an automorphism and show it is the identity
  intro f hf
  have hfA : ∀ a ∈ A, f ‘ a ∈ A := fun a ha ↦ function_value_mem hf.1 ha
  -- the only loop is fixed
  have hfe : f ‘ (z ‘ 0) = z ‘ 0 := by
    have h1 : ⟨z ‘ 0, z ‘ 0⟩ₖ ∈ cantorChainRelation A z := (hloop _ he).mpr rfl
    exact (hloop _ (hfA _ he)).mp ((hf.2.2.2 _ he _ he).mp h1)
  -- the range of `z` is invariant, as are its complement in `A` and the point `z ‘ 0`
  have hrangeiff : ∀ a ∈ A, (f ‘ a ∈ range z ↔ a ∈ range z) := by
    intro a ha
    have key := hf.2.2.2 a ha (z ‘ 0) he
    rw [hfe] at key
    exact ((hpred _ (hfA a ha)).symm.trans key.symm).trans (hpred a ha)
  have hne0 : ∀ a ∈ A, a ≠ z ‘ 0 → f ‘ a ≠ z ‘ 0 := by
    intro a ha hane h
    exact hane (injective_value_eq hf.1 hf.2.1 ha he (h.trans hfe.symm))
  -- the first link of the chain is fixed, because it has no predecessor in the chain
  have hbase : f ‘ (z ‘ (succ 0)) = z ‘ (succ 0) := by
    have h1ω : succ (0 : V) ∈ (ω : V) := ω_succ_closed h0ω
    have haA : z ‘ (succ 0) ∈ A := hmem _ h1ω
    have hfr : f ‘ (z ‘ (succ 0)) ∈ range z := (hrangeiff _ haA).mpr (hval _ h1ω)
    have hfne : f ‘ (z ‘ (succ 0)) ≠ z ‘ 0 := hne0 _ haA (hsuccne 0 h0ω)
    obtain ⟨k, hk, hfk⟩ := hshape _ hfr hfne
    rcases internalNatural_cases hk with rfl | ⟨j, hj, rfl⟩
    · exact hfk
    · exfalso
      have hmemR : ⟨z ‘ (succ j), z ‘ (succ (succ j))⟩ₖ ∈ cantorChainRelation A z :=
        (hchain j hj (succ j) (ω_succ_closed hj)).mpr rfl
      rw [← hfk] at hmemR
      obtain ⟨c, hcA, hcf⟩ := hf.surjective (hmem _ (ω_succ_closed hj))
      rw [← hcf] at hmemR
      have hca : ⟨c, z ‘ (succ 0)⟩ₖ ∈ cantorChainRelation A z :=
        (hf.2.2.2 c hcA _ haA).mpr hmemR
      have hcr : c ∈ range z :=
        (hrangeiff c hcA).mp (by rw [hcf]; exact hval _ (ω_succ_closed hj))
      have hcne : c ≠ z ‘ 0 := by
        intro h
        rw [h, hfe] at hcf
        exact hsuccne j hj hcf.symm
      obtain ⟨i, hi, hci⟩ := hshape c hcr hcne
      rw [hci] at hca
      have h0 : (0 : V) = succ i := (hchain i hi 0 h0ω).mp hca
      have hh : i ∈ succ i := mem_succ_self i
      rw [← h0] at hh
      exact not_mem_empty hh
  -- every link of the chain is fixed
  have hfix : ∀ n ∈ (ω : V), f ‘ (z ‘ (succ n)) = z ‘ (succ n) := by
    apply naturalNumber_induction (fun n ↦ f ‘ (z ‘ (succ n)) = z ‘ (succ n)) (by definability)
    · exact hbase
    · intro n hn ih
      have haA : z ‘ (succ (succ n)) ∈ A := hmem _ (ω_succ_closed (ω_succ_closed hn))
      have hmemR : ⟨z ‘ (succ n), z ‘ (succ (succ n))⟩ₖ ∈ cantorChainRelation A z :=
        (hchain n hn (succ n) (ω_succ_closed hn)).mpr rfl
      have h2 := (hf.2.2.2 _ (hmem _ (ω_succ_closed hn)) _ haA).mp hmemR
      rw [ih] at h2
      have hfr : f ‘ (z ‘ (succ (succ n))) ∈ range z :=
        (hrangeiff _ haA).mpr (hval _ (ω_succ_closed (ω_succ_closed hn)))
      have hfne : f ‘ (z ‘ (succ (succ n))) ≠ z ‘ 0 :=
        hne0 _ haA (hsuccne _ (ω_succ_closed hn))
      obtain ⟨m, hm, hfm⟩ := hshape _ hfr hfne
      rw [hfm] at h2
      rw [hfm, (hchain n hn m hm).mp h2]
  intro x hxA
  by_cases hxr : x ∈ range z
  · by_cases hx0 : x = z ‘ 0
    · rw [hx0, hfe]
    · obtain ⟨i, hi, hxi⟩ := hshape x hxr hx0
      rw [hxi]
      exact hfix i hi
  · -- a real outside the range of `z` is pinned by its coordinates
    have hfx : f ‘ x ∈ A := hfA x hxA
    have hfxr : f ‘ x ∉ range z := fun h ↦ hxr ((hrangeiff x hxA).mp h)
    have hvals : ∀ n ∈ (ω : V), (f ‘ x) ‘ n = x ‘ n := by
      intro n hn
      have key := hf.2.2.2 _ (hmem _ (ω_succ_closed hn)) x hxA
      rw [hfix n hn] at key
      have hiff : x ‘ n = 1 ↔ (f ‘ x) ‘ n = 1 :=
        ((houter n hn x hxA hxr).symm.trans key).trans (houter n hn _ hfx hfxr)
      rcases cantor_value_mem_two (hA _ hfx) hn with h1 | h1
      · rcases cantor_value_mem_two (hA _ hxA) hn with h2 | h2
        · rw [h1, h2]
        · exact absurd (h1.symm.trans (hiff.mp h2)) zero_ne_one
      · rw [h1, hiff.mpr h1]
    exact cantor_eq_of_values (hA _ hfx) (hA _ hxA) hvals

/-! ### Every set of reals carries a rigid relation -/

/-- Hamkins and Palumbo, Theorem 2: in ZF every set of reals carries a rigid relation. -/
theorem hasRigidRelation_of_subset_cantorSpace {A : V} (hA : A ⊆ cantorSpace V) :
    HasRigidRelation A := by
  classical
  by_cases hdf : IsInternallyDedekindFinite A
  · exact hasRigidRelation_of_dedekindFinite_cantor hA hdf
  · obtain ⟨z, hz, hinj⟩ := omega_cardLE_of_not_dedekindFinite hdf
    exact ⟨cantorChainRelation A z, isRigidRelation_cantorChainRelation hA hz hinj⟩

end ZFVP
