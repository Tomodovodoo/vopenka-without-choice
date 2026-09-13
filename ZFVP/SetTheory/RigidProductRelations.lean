import ZFVP.SetTheory.RigidCantorRelations

/-! Theorem 4 of Hamkins and Palumbo: if a set `B` carries a hereditarily rigid irreflexive
relation `R₁`, then every subset `A` of `cantorSpace V ×ˢ B` carries a rigid relation. The proof
splits on whether `A` is Dedekind finite. In the infinite case the relation of
`ZFVP.RigidCantorRelations` is extended by a clause reading `R₁` off the second coordinates; in
the finite case the relation is the lexicographic order on first coordinates refined by `R₁` on
the second. In both cases an automorphism first turns out to fix all first coordinates, and then
hereditary rigidity of `R₁` on each slice finishes the argument. In particular every subset of
`cantorSpace V ×ˢ γ` for an ordinal `γ` carries a rigid relation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Points of a product -/

/-- A member of a product is the Kuratowski pair of its two projections. -/
theorem eq_kpair_of_mem_prod {X Y u : V} (h : u ∈ X ×ˢ Y) :
    u = ⟨kpair.π₁ u, kpair.π₂ u⟩ₖ ∧ kpair.π₁ u ∈ X ∧ kpair.π₂ u ∈ Y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp h
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simpa using ha
  · simpa using hb

/-! ### Fixing a slice -/

set_option maxRecDepth 8000 in
/-- Suppose `A₀` is a set of pairs invariant under an automorphism `f` of `⟨A, R⟩`, that `f`
fixes the first coordinate of every point of `A₀`, and that on pairs of `A₀` with equal first
coordinates `R` is read off `R₁` on the second coordinates. If `R₁` is hereditarily rigid on `B`
then `f` fixes every point of `A₀`. -/
theorem slice_fixed_of_hereditarilyRigid {A B R₁ R f A₀ : V}
    (hR : IsHereditarilyRigid B R₁)
    (hA : A ⊆ cantorSpace V ×ˢ B)
    (hA₀ : A₀ ⊆ A)
    (hinv : ∀ a ∈ A₀, f ‘ a ∈ A₀)
    (hsurj : ∀ a ∈ A₀, ∃ c ∈ A₀, f ‘ c = a)
    (hfst : ∀ a ∈ A₀, kpair.π₁ (f ‘ a) = kpair.π₁ a)
    (hrel : ∀ u ∈ A₀, ∀ v ∈ A₀, kpair.π₁ u = kpair.π₁ v →
      (⟨u, v⟩ₖ ∈ R ↔ ⟨kpair.π₂ u, kpair.π₂ v⟩ₖ ∈ R₁))
    (hf : IsAutomorphismOf A R f) :
    ∀ a ∈ A₀, f ‘ a = a := by
  classical
  intro a haA₀
  obtain ⟨x, hxdef⟩ : ∃ x : V, kpair.π₁ a = x := ⟨_, rfl⟩
  let S : V := {b ∈ B ; ⟨x, b⟩ₖ ∈ A₀}
  have hmemS : ∀ b : V, b ∈ S ↔ b ∈ B ∧ ⟨x, b⟩ₖ ∈ A₀ := fun b ↦ mem_sep_iff
  have hSB : S ⊆ B := fun b hb ↦ ((hmemS b).mp hb).1
  let G : V → V := fun b ↦ kpair.π₂ (f ‘ ⟨x, b⟩ₖ)
  have hG : ℒₛₑₜ-function₁ G := by unfold G; definability
  -- the value of `f` on a point of the slice stays in the slice
  have key : ∀ b ∈ S, f ‘ ⟨x, b⟩ₖ = ⟨x, G b⟩ₖ ∧ G b ∈ S := by
    intro b hb
    obtain ⟨hbB, hbA₀⟩ := (hmemS b).mp hb
    have hfmem : f ‘ ⟨x, b⟩ₖ ∈ A₀ := hinv _ hbA₀
    obtain ⟨hdec, -, hsnd⟩ := eq_kpair_of_mem_prod (hA _ (hA₀ _ hfmem))
    have hπ : kpair.π₁ (f ‘ ⟨x, b⟩ₖ) = x := by
      have := hfst _ hbA₀
      simpa only [kpair.π₁_kpair] using this
    have heq : f ‘ ⟨x, b⟩ₖ = ⟨x, G b⟩ₖ :=
      calc f ‘ (⟨x, b⟩ₖ : V)
          = ⟨kpair.π₁ (f ‘ (⟨x, b⟩ₖ : V)), kpair.π₂ (f ‘ (⟨x, b⟩ₖ : V))⟩ₖ := hdec
        _ = ⟨x, G b⟩ₖ := by rw [hπ]
    refine ⟨heq, (hmemS _).mpr ⟨hsnd, ?_⟩⟩
    rw [← heq]; exact hfmem
  have hGS : ∀ b ∈ S, G b ∈ S := fun b hb ↦ (key b hb).2
  have hpairA : ∀ b ∈ S, (⟨x, b⟩ₖ : V) ∈ A := fun b hb ↦ hA₀ _ ((hmemS b).mp hb).2
  -- the induced map on the slice
  let g : V := definableGraph S G hG
  have hgS : g ∈ S ^ S := definableGraph_mem_function_of_mapsTo _ _ _ _ hGS
  have hgval : ∀ b ∈ S, g ‘ b = G b := fun b hb ↦ value_definableGraph _ _ _ hb
  have hGinj : ∀ b ∈ S, ∀ c ∈ S, G b = G c → b = c := by
    intro b hb c hc h
    have h1 : f ‘ (⟨x, b⟩ₖ : V) = f ‘ (⟨x, c⟩ₖ : V) := by
      rw [(key b hb).1, (key c hc).1, h]
    have h2 : (⟨x, b⟩ₖ : V) = ⟨x, c⟩ₖ :=
      injective_value_eq hf.1 hf.2.1 (hpairA b hb) (hpairA c hc) h1
    exact (kpair_iff.mp h2).2
  have hauto : IsAutomorphismOf S (R₁ ∩ (S ×ˢ S)) g := by
    refine ⟨hgS, ?_, ?_, ?_⟩
    · intro b c y hb hc
      obtain ⟨hbS, hyb⟩ := (pair_mem_definableGraph_iff S G hG b y).mp hb
      obtain ⟨hcS, hyc⟩ := (pair_mem_definableGraph_iff S G hG c y).mp hc
      exact hGinj b hbS c hcS (hyb.symm.trans hyc)
    · refine range_eq_of_values hgS ?_
      intro y hy
      obtain ⟨hyB, hyA₀⟩ := (hmemS y).mp hy
      obtain ⟨c, hcA₀, hcf⟩ := hsurj _ hyA₀
      obtain ⟨hdec, -, hsnd⟩ := eq_kpair_of_mem_prod (hA _ (hA₀ _ hcA₀))
      have hπc : kpair.π₁ c = x := by
        have := hfst c hcA₀
        rw [hcf] at this
        simpa only [kpair.π₁_kpair] using this.symm
      have hcpair : c = ⟨x, kpair.π₂ c⟩ₖ := by rw [← hπc]; exact hdec
      have hcS : kpair.π₂ c ∈ S := (hmemS _).mpr ⟨hsnd, by rw [← hcpair]; exact hcA₀⟩
      refine ⟨kpair.π₂ c, hcS, ?_⟩
      rw [hgval _ hcS]
      show kpair.π₂ (f ‘ (⟨x, kpair.π₂ c⟩ₖ : V)) = y
      rw [← hcpair, hcf, kpair.π₂_kpair]
    · intro u hu v hv
      have hGu : G u ∈ S := hGS u hu
      have hGv : G v ∈ S := hGS v hv
      have huA₀ : (⟨x, u⟩ₖ : V) ∈ A₀ := ((hmemS u).mp hu).2
      have hvA₀ : (⟨x, v⟩ₖ : V) ∈ A₀ := ((hmemS v).mp hv).2
      have hGuA₀ : (⟨x, G u⟩ₖ : V) ∈ A₀ := ((hmemS _).mp hGu).2
      have hGvA₀ : (⟨x, G v⟩ₖ : V) ∈ A₀ := ((hmemS _).mp hGv).2
      have e1 : ⟨u, v⟩ₖ ∈ R₁ ↔ (⟨(⟨x, u⟩ₖ : V), (⟨x, v⟩ₖ : V)⟩ₖ : V) ∈ R := by
        have := hrel _ huA₀ _ hvA₀ (by simp)
        simpa only [kpair.π₂_kpair] using this.symm
      have e2 : (⟨(⟨x, u⟩ₖ : V), (⟨x, v⟩ₖ : V)⟩ₖ : V) ∈ R ↔
          (⟨(⟨x, G u⟩ₖ : V), (⟨x, G v⟩ₖ : V)⟩ₖ : V) ∈ R := by
        have := hf.2.2.2 _ (hpairA u hu) _ (hpairA v hv)
        rw [(key u hu).1, (key v hv).1] at this
        exact this
      have e3 : (⟨(⟨x, G u⟩ₖ : V), (⟨x, G v⟩ₖ : V)⟩ₖ : V) ∈ R ↔ ⟨G u, G v⟩ₖ ∈ R₁ := by
        have := hrel _ hGuA₀ _ hGvA₀ (by simp)
        simpa only [kpair.π₂_kpair] using this
      rw [hgval u hu, hgval v hv]
      constructor
      · intro h
        exact mem_inter_iff.mpr ⟨e3.mp (e2.mp (e1.mp (mem_inter_iff.mp h).1)),
          kpair_mem_iff.mpr ⟨hGu, hGv⟩⟩
      · intro h
        exact mem_inter_iff.mpr ⟨e1.mpr (e2.mpr (e3.mpr (mem_inter_iff.mp h).1)),
          kpair_mem_iff.mpr ⟨hu, hv⟩⟩
  have hfix : ∀ b ∈ S, G b = b := by
    intro b hb
    have := (hR S hSB).2 g hauto b hb
    rwa [hgval b hb] at this
  -- read the conclusion off at the point `a`
  obtain ⟨hdeca, -, hsnda⟩ := eq_kpair_of_mem_prod (hA _ (hA₀ _ haA₀))
  rw [hxdef] at hdeca
  have haS : kpair.π₂ a ∈ S := (hmemS _).mpr ⟨hsnda, by rw [← hdeca]; exact haA₀⟩
  have h1 : f ‘ a = ⟨x, G (kpair.π₂ a)⟩ₖ := by
    conv_lhs => rw [hdeca]
    exact (key _ haS).1
  rw [h1, hfix _ haS]
  exact hdeca.symm

/-! ### The Dedekind infinite case -/

/-- The relation on `A ⊆ cantorSpace V ×ˢ B` attached to an injective sequence `z` in `A` and a
relation `R₁` on `B`. The four clauses of `cantorChainRelation` are kept, with the coordinates of
a point read off its first component, and a fifth clause puts `R₁` on the second components of
the points outside the range of `z`. -/
noncomputable def productChainRelation (A z R₁ : V) : V :=
  {w ∈ A ×ˢ A ;
    (kpair.π₁ w = z ‘ 0 ∧ kpair.π₂ w = z ‘ 0) ∨
    (∃ n ∈ (ω : V), kpair.π₁ w = z ‘ (succ n) ∧ kpair.π₂ w = z ‘ 0) ∨
    (∃ n ∈ (ω : V), kpair.π₁ w = z ‘ (succ n) ∧ kpair.π₂ w = z ‘ (succ (succ n))) ∨
    (∃ n ∈ (ω : V), kpair.π₁ w = z ‘ (succ n) ∧ kpair.π₂ w ∉ range z ∧
      (kpair.π₁ (kpair.π₂ w)) ‘ n = 1) ∨
    (kpair.π₁ w ∉ range z ∧ kpair.π₂ w ∉ range z ∧
      ⟨kpair.π₂ (kpair.π₁ w), kpair.π₂ (kpair.π₂ w)⟩ₖ ∈ R₁)}

theorem productChainRelation_subset (A z R₁ : V) : productChainRelation A z R₁ ⊆ A ×ˢ A :=
  fun _ hw ↦ (mem_sep_iff.mp hw).1

theorem kpair_mem_productChainRelation {A z R₁ : V} (x y : V) (hx : x ∈ A) (hy : y ∈ A) :
    ⟨x, y⟩ₖ ∈ productChainRelation A z R₁ ↔
      (x = z ‘ 0 ∧ y = z ‘ 0) ∨
      (∃ n ∈ (ω : V), x = z ‘ (succ n) ∧ y = z ‘ 0) ∨
      (∃ n ∈ (ω : V), x = z ‘ (succ n) ∧ y = z ‘ (succ (succ n))) ∨
      (∃ n ∈ (ω : V), x = z ‘ (succ n) ∧ y ∉ range z ∧ (kpair.π₁ y) ‘ n = 1) ∨
      (x ∉ range z ∧ y ∉ range z ∧ ⟨kpair.π₂ x, kpair.π₂ y⟩ₖ ∈ R₁) := by
  simp only [productChainRelation, mem_sep_iff, kpair.π₁_kpair, kpair.π₂_kpair,
    kpair_mem_iff, and_iff_right (And.intro hx hy)]

set_option maxHeartbeats 2000000 in
/-- The relation attached to an injective sequence in `A ⊆ cantorSpace V ×ˢ B` is rigid, provided
`R₁` is hereditarily rigid and irreflexive on `B`. -/
theorem isRigidRelation_productChainRelation {A B R₁ z : V}
    (hR : IsHereditarilyRigid B R₁) (hirr : ∀ b ∈ B, ⟨b, b⟩ₖ ∉ R₁)
    (hA : A ⊆ cantorSpace V ×ˢ B) (hz : z ∈ A ^ (ω : V)) (hinj : Injective z) :
    IsRigidRelation A (productChainRelation A z R₁) := by
  classical
  refine ⟨productChainRelation_subset A z R₁, ?_⟩
  have hzF : IsFunction z := IsFunction.of_mem hz
  have h0ω : (0 : V) ∈ (ω : V) := by simp
  have hmem : ∀ n ∈ (ω : V), z ‘ n ∈ A := fun n hn ↦ function_value_mem hz hn
  have hval : ∀ n ∈ (ω : V), z ‘ n ∈ range z := fun n hn ↦ value_mem_range hz hn
  have he : z ‘ 0 ∈ A := hmem 0 h0ω
  have hzinj : ∀ m ∈ (ω : V), ∀ n ∈ (ω : V), z ‘ m = z ‘ n → m = n :=
    fun m hm n hn h ↦ injective_value_eq hz hinj hm hn h
  have hfstmem : ∀ a ∈ A, kpair.π₁ a ∈ cantorSpace V :=
    fun a ha ↦ (eq_kpair_of_mem_prod (hA a ha)).2.1
  have hsndmem : ∀ a ∈ A, kpair.π₂ a ∈ B :=
    fun a ha ↦ (eq_kpair_of_mem_prod (hA a ha)).2.2
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
  -- the five ways a pair can lie in the relation
  have hloop : ∀ a ∈ A, (⟨a, a⟩ₖ ∈ productChainRelation A z R₁ ↔ a = z ‘ 0) := by
    intro a ha
    rw [kpair_mem_productChainRelation a a ha ha]
    constructor
    · rintro (⟨h, -⟩ | ⟨n, hn, h1, h2⟩ | ⟨n, hn, h1, h2⟩ | ⟨n, hn, h1, h2, -⟩ | ⟨-, -, h3⟩)
      · exact h
      · exact absurd (h1.symm.trans h2) (hsuccne n hn)
      · exact absurd (h1.symm.trans h2) (hnotfix n hn)
      · exact absurd (by rw [h1]; exact hval _ (ω_succ_closed hn)) h2
      · exact absurd h3 (hirr _ (hsndmem a ha))
    · intro h
      exact Or.inl ⟨h, h⟩
  have hpred : ∀ a ∈ A, (⟨a, z ‘ 0⟩ₖ ∈ productChainRelation A z R₁ ↔ a ∈ range z) := by
    intro a ha
    rw [kpair_mem_productChainRelation a (z ‘ 0) ha he]
    constructor
    · rintro (⟨h, -⟩ | ⟨n, hn, h1, -⟩ | ⟨n, hn, -, h2⟩ | ⟨n, hn, -, h2, -⟩ | ⟨-, h2, -⟩)
      · rw [h]; exact hval 0 h0ω
      · rw [h1]; exact hval _ (ω_succ_closed hn)
      · exact absurd h2.symm (hsuccne (succ n) (ω_succ_closed hn))
      · exact absurd (hval 0 h0ω) h2
      · exact absurd (hval 0 h0ω) h2
    · intro har
      by_cases h : a = z ‘ 0
      · exact Or.inl ⟨h, rfl⟩
      · obtain ⟨i, hi, hai⟩ := hshape a har h
        exact Or.inr (Or.inl ⟨i, hi, hai, rfl⟩)
  have hchain : ∀ m ∈ (ω : V), ∀ n ∈ (ω : V),
      (⟨z ‘ (succ m), z ‘ (succ n)⟩ₖ ∈ productChainRelation A z R₁ ↔ n = succ m) := by
    intro m hm n hn
    rw [kpair_mem_productChainRelation _ _ (hmem _ (ω_succ_closed hm))
      (hmem _ (ω_succ_closed hn))]
    constructor
    · rintro (⟨h, -⟩ | ⟨k, hk, -, h2⟩ | ⟨k, hk, h1, h2⟩ | ⟨k, hk, -, h2, -⟩ | ⟨h1, -, -⟩)
      · exact absurd h (hsuccne m hm)
      · exact absurd h2 (hsuccne n hn)
      · rw [hsuccinj n hn (succ k) (ω_succ_closed hk) h2, hsuccinj m hm k hk h1]
      · exact absurd (hval _ (ω_succ_closed hn)) h2
      · exact absurd (hval _ (ω_succ_closed hm)) h1
    · rintro rfl
      exact Or.inr (Or.inr (Or.inl ⟨m, hm, rfl, rfl⟩))
  have houter : ∀ n ∈ (ω : V), ∀ y ∈ A, y ∉ range z →
      (⟨z ‘ (succ n), y⟩ₖ ∈ productChainRelation A z R₁ ↔ (kpair.π₁ y) ‘ n = 1) := by
    intro n hn y hy hyr
    rw [kpair_mem_productChainRelation _ _ (hmem _ (ω_succ_closed hn)) hy]
    constructor
    · rintro (⟨h, -⟩ | ⟨k, hk, -, h2⟩ | ⟨k, hk, -, h2⟩ | ⟨k, hk, h1, -, h3⟩ | ⟨h1, -, -⟩)
      · exact absurd h (hsuccne n hn)
      · exact absurd (by rw [h2]; exact hval 0 h0ω) hyr
      · exact absurd (by rw [h2]; exact hval _ (ω_succ_closed (ω_succ_closed hk))) hyr
      · rwa [hsuccinj n hn k hk h1]
      · exact absurd (hval _ (ω_succ_closed hn)) h1
    · intro h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, rfl, hyr, h⟩)))
  -- the fifth clause, on pairs outside the range of `z`
  have hslice : ∀ u ∈ A, u ∉ range z → ∀ v ∈ A, v ∉ range z →
      (⟨u, v⟩ₖ ∈ productChainRelation A z R₁ ↔ ⟨kpair.π₂ u, kpair.π₂ v⟩ₖ ∈ R₁) := by
    intro u hu hur v hv hvr
    rw [kpair_mem_productChainRelation u v hu hv]
    constructor
    · rintro (⟨h, -⟩ | ⟨n, hn, h1, -⟩ | ⟨n, hn, h1, -⟩ | ⟨n, hn, h1, -, -⟩ | ⟨-, -, h3⟩)
      · exact absurd (by rw [h]; exact hval 0 h0ω) hur
      · exact absurd (by rw [h1]; exact hval _ (ω_succ_closed hn)) hur
      · exact absurd (by rw [h1]; exact hval _ (ω_succ_closed hn)) hur
      · exact absurd (by rw [h1]; exact hval _ (ω_succ_closed hn)) hur
      · exact h3
    · intro h
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hur, hvr, h⟩)))
  -- now fix an automorphism
  intro f hf
  have hfA : ∀ a ∈ A, f ‘ a ∈ A := fun a ha ↦ function_value_mem hf.1 ha
  have hfe : f ‘ (z ‘ 0) = z ‘ 0 := by
    have h1 : ⟨z ‘ 0, z ‘ 0⟩ₖ ∈ productChainRelation A z R₁ := (hloop _ he).mpr rfl
    exact (hloop _ (hfA _ he)).mp ((hf.2.2.2 _ he _ he).mp h1)
  have hrangeiff : ∀ a ∈ A, (f ‘ a ∈ range z ↔ a ∈ range z) := by
    intro a ha
    have key := hf.2.2.2 a ha (z ‘ 0) he
    rw [hfe] at key
    exact ((hpred _ (hfA a ha)).symm.trans key.symm).trans (hpred a ha)
  have hne0 : ∀ a ∈ A, a ≠ z ‘ 0 → f ‘ a ≠ z ‘ 0 := by
    intro a ha hane h
    exact hane (injective_value_eq hf.1 hf.2.1 ha he (h.trans hfe.symm))
  have hbase : f ‘ (z ‘ (succ 0)) = z ‘ (succ 0) := by
    have h1ω : succ (0 : V) ∈ (ω : V) := ω_succ_closed h0ω
    have haA : z ‘ (succ 0) ∈ A := hmem _ h1ω
    have hfr : f ‘ (z ‘ (succ 0)) ∈ range z := (hrangeiff _ haA).mpr (hval _ h1ω)
    have hfne : f ‘ (z ‘ (succ 0)) ≠ z ‘ 0 := hne0 _ haA (hsuccne 0 h0ω)
    obtain ⟨k, hk, hfk⟩ := hshape _ hfr hfne
    rcases internalNatural_cases hk with rfl | ⟨j, hj, rfl⟩
    · exact hfk
    · exfalso
      have hmemR : ⟨z ‘ (succ j), z ‘ (succ (succ j))⟩ₖ ∈ productChainRelation A z R₁ :=
        (hchain j hj (succ j) (ω_succ_closed hj)).mpr rfl
      rw [← hfk] at hmemR
      obtain ⟨c, hcA, hcf⟩ := hf.surjective (hmem _ (ω_succ_closed hj))
      rw [← hcf] at hmemR
      have hca : ⟨c, z ‘ (succ 0)⟩ₖ ∈ productChainRelation A z R₁ :=
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
  have hfix : ∀ n ∈ (ω : V), f ‘ (z ‘ (succ n)) = z ‘ (succ n) := by
    apply naturalNumber_induction (fun n ↦ f ‘ (z ‘ (succ n)) = z ‘ (succ n)) (by definability)
    · exact hbase
    · intro n hn ih
      have haA : z ‘ (succ (succ n)) ∈ A := hmem _ (ω_succ_closed (ω_succ_closed hn))
      have hmemR : ⟨z ‘ (succ n), z ‘ (succ (succ n))⟩ₖ ∈ productChainRelation A z R₁ :=
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
  -- the points outside the range of `z`
  let A₀ : V := {a ∈ A ; a ∉ range z}
  have hmemA₀ : ∀ a : V, a ∈ A₀ ↔ a ∈ A ∧ a ∉ range z := fun a ↦ mem_sep_iff
  have hA₀A : A₀ ⊆ A := fun a ha ↦ ((hmemA₀ a).mp ha).1
  have hinvA₀ : ∀ a ∈ A₀, f ‘ a ∈ A₀ := by
    intro a ha
    obtain ⟨haA, har⟩ := (hmemA₀ a).mp ha
    exact (hmemA₀ _).mpr ⟨hfA a haA, fun h ↦ har ((hrangeiff a haA).mp h)⟩
  have hsurjA₀ : ∀ a ∈ A₀, ∃ c ∈ A₀, f ‘ c = a := by
    intro a ha
    obtain ⟨haA, har⟩ := (hmemA₀ a).mp ha
    obtain ⟨c, hcA, hcf⟩ := hf.surjective haA
    refine ⟨c, (hmemA₀ c).mpr ⟨hcA, fun h ↦ har ?_⟩, hcf⟩
    rw [← hcf]
    exact (hrangeiff c hcA).mpr h
  have hfstA₀ : ∀ a ∈ A₀, kpair.π₁ (f ‘ a) = kpair.π₁ a := by
    intro a ha
    obtain ⟨haA, har⟩ := (hmemA₀ a).mp ha
    have hfa : f ‘ a ∈ A := hfA a haA
    have hfar : f ‘ a ∉ range z := ((hmemA₀ _).mp (hinvA₀ a ha)).2
    have hvals : ∀ n ∈ (ω : V), (kpair.π₁ (f ‘ a)) ‘ n = (kpair.π₁ a) ‘ n := by
      intro n hn
      have key := hf.2.2.2 _ (hmem _ (ω_succ_closed hn)) a haA
      rw [hfix n hn] at key
      have hiff : (kpair.π₁ a) ‘ n = 1 ↔ (kpair.π₁ (f ‘ a)) ‘ n = 1 :=
        ((houter n hn a haA har).symm.trans key).trans (houter n hn _ hfa hfar)
      rcases cantor_value_mem_two (hfstmem _ hfa) hn with h1 | h1
      · rcases cantor_value_mem_two (hfstmem _ haA) hn with h2 | h2
        · rw [h1, h2]
        · exact absurd (h1.symm.trans (hiff.mp h2)) zero_ne_one
      · rw [h1, hiff.mpr h1]
    exact cantor_eq_of_values (hfstmem _ hfa) (hfstmem _ haA) hvals
  have hrelA₀ : ∀ u ∈ A₀, ∀ v ∈ A₀, kpair.π₁ u = kpair.π₁ v →
      (⟨u, v⟩ₖ ∈ productChainRelation A z R₁ ↔ ⟨kpair.π₂ u, kpair.π₂ v⟩ₖ ∈ R₁) := by
    intro u hu v hv _
    obtain ⟨huA, hur⟩ := (hmemA₀ u).mp hu
    obtain ⟨hvA, hvr⟩ := (hmemA₀ v).mp hv
    exact hslice u huA hur v hvA hvr
  have hfinal := slice_fixed_of_hereditarilyRigid hR hA hA₀A hinvA₀ hsurjA₀ hfstA₀ hrelA₀ hf
  intro x hxA
  by_cases hxr : x ∈ range z
  · by_cases hx0 : x = z ‘ 0
    · rw [hx0, hfe]
    · obtain ⟨i, hi, hxi⟩ := hshape x hxr hx0
      rw [hxi]
      exact hfix i hi
  · exact hfinal x ((hmemA₀ x).mpr ⟨hxA, hxr⟩)

/-! ### The Dedekind finite case -/

/-- The lexicographic order on first coordinates, refined by `R₁` on the second coordinates. -/
noncomputable def productLexRelation (A R₁ : V) : V :=
  {w ∈ A ×ˢ A ;
    ⟨kpair.π₁ (kpair.π₁ w), kpair.π₁ (kpair.π₂ w)⟩ₖ ∈ cantorLexOrder (cantorSpace V) ∨
    (kpair.π₁ (kpair.π₁ w) = kpair.π₁ (kpair.π₂ w) ∧
      ⟨kpair.π₂ (kpair.π₁ w), kpair.π₂ (kpair.π₂ w)⟩ₖ ∈ R₁)}

theorem productLexRelation_subset (A R₁ : V) : productLexRelation A R₁ ⊆ A ×ˢ A :=
  fun _ hw ↦ (mem_sep_iff.mp hw).1

theorem kpair_mem_productLexRelation {A R₁ : V} (u v : V) (hu : u ∈ A) (hv : v ∈ A) :
    ⟨u, v⟩ₖ ∈ productLexRelation A R₁ ↔
      ⟨kpair.π₁ u, kpair.π₁ v⟩ₖ ∈ cantorLexOrder (cantorSpace V) ∨
      (kpair.π₁ u = kpair.π₁ v ∧ ⟨kpair.π₂ u, kpair.π₂ v⟩ₖ ∈ R₁) := by
  simp only [productLexRelation, mem_sep_iff, kpair.π₁_kpair, kpair.π₂_kpair,
    kpair_mem_iff, and_iff_right (And.intro hu hv)]

/-- If an automorphism raises the first coordinate of a point strictly in the lexicographic
order, and every step of the relation leaves the first coordinate equal or raises it, then the
iterates of the point give an injection of `ω` into the set. -/
theorem omega_cardLE_of_automorphism_lex_increasing {A R f x : V}
    (hfstmem : ∀ a ∈ A, kpair.π₁ a ∈ cantorSpace V)
    (hstep : ∀ u ∈ A, ∀ v ∈ A, ⟨u, v⟩ₖ ∈ R →
      ⟨kpair.π₁ u, kpair.π₁ v⟩ₖ ∈ cantorLexOrder (cantorSpace V) ∨ kpair.π₁ u = kpair.π₁ v)
    (hf : IsAutomorphismOf A R f) (hxA : x ∈ A) (hxR : ⟨x, f ‘ x⟩ₖ ∈ R)
    (hlt : ⟨kpair.π₁ x, kpair.π₁ (f ‘ x)⟩ₖ ∈ cantorLexOrder (cantorSpace V)) :
    (ω : V) ≤# A := by
  classical
  let F : V → V := fun w ↦ f ‘ w
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let b := naturalIteration F hF x
  have hbdef : ℒₛₑₜ-function₁ b := naturalIteration_definable F hF x
  have hb (n : V) (hn : n ∈ (ω : V)) : b n ∈ A :=
    naturalIteration_invariant F hF x (fun w ↦ w ∈ A) (by definability) hxA
      (fun w hw ↦ function_value_mem hf.1 hw) n hn
  have hzero : b 0 = x := naturalIteration_zero F hF x
  have hsucc (n : V) (hn : n ∈ (ω : V)) : b (succ n) = f ‘ (b n) := naturalIteration_succ F hF x hn
  -- each iterate is related to the next
  have hchainR : ∀ n ∈ (ω : V), ⟨b n, b (succ n)⟩ₖ ∈ R := by
    apply naturalNumber_induction (fun n ↦ ⟨b n, b (succ n)⟩ₖ ∈ R) (by definability)
    · rw [hsucc 0 (by simp), hzero]
      exact hxR
    · intro n hn ih
      have h1 : ⟨f ‘ (b n), f ‘ (b (succ n))⟩ₖ ∈ R :=
        (hf.2.2.2 _ (hb n hn) _ (hb _ (ω_succ_closed hn))).mp ih
      rw [hsucc (succ n) (ω_succ_closed hn), hsucc n hn]
      rw [hsucc n hn] at h1
      exact h1
  -- the first coordinate stays strictly above where it started
  have hQ : ∀ n ∈ (ω : V),
      ⟨kpair.π₁ (b 0), kpair.π₁ (b (succ n))⟩ₖ ∈ cantorLexOrder (cantorSpace V) := by
    apply naturalNumber_induction
      (fun n ↦ ⟨kpair.π₁ (b 0), kpair.π₁ (b (succ n))⟩ₖ ∈ cantorLexOrder (cantorSpace V))
      (by definability)
    · rw [hsucc 0 (by simp), hzero]
      exact hlt
    · intro n hn ih
      have hsn : succ n ∈ (ω : V) := ω_succ_closed hn
      have hssn : succ (succ n) ∈ (ω : V) := ω_succ_closed hsn
      rcases hstep _ (hb _ hsn) _ (hb _ hssn) (hchainR _ hsn) with h | h
      · exact cantorLexOrder_trans (subset_refl (cantorSpace V))
          _ (hfstmem _ (hb 0 (by simp))) _ (hfstmem _ (hb _ hsn)) _ (hfstmem _ (hb _ hssn)) ih h
      · rwa [← h]
  have hne0 : ∀ n ∈ (ω : V), b 0 ≠ b (succ n) := by
    intro n hn h
    have := hQ n hn
    rw [← h] at this
    exact cantorLexOrder_irrefl _ _ (hfstmem _ (hb 0 (by simp))) this
  have hinjb : ∀ m ∈ (ω : V), ∀ n ∈ (ω : V), b m = b n → m = n := by
    apply naturalNumber_induction (fun m ↦ ∀ n ∈ (ω : V), b m = b n → m = n) (by definability)
    · intro n hn h
      rcases internalNatural_cases hn with rfl | ⟨k, hk, rfl⟩
      · rfl
      · exact absurd h (hne0 k hk)
    · intro m hm ih n hn h
      rcases internalNatural_cases hn with rfl | ⟨k, hk, rfl⟩
      · exact absurd h.symm (hne0 m hm)
      · rw [hsucc m hm, hsucc k hk] at h
        have := injective_value_eq hf.1 hf.2.1 (hb m hm) (hb k hk) h
        rw [ih k hk this]
  let g := definableGraph (ω : V) b hbdef
  have hg : g ∈ A ^ (ω : V) := definableGraph_mem_function_of_mapsTo _ _ _ _ hb
  refine ⟨g, hg, ?_⟩
  intro n m w hnw hmw
  obtain ⟨hn, hwn⟩ := (pair_mem_definableGraph_iff (ω : V) b hbdef n w).mp hnw
  obtain ⟨hm, hwm⟩ := (pair_mem_definableGraph_iff (ω : V) b hbdef m w).mp hmw
  exact hinjb n hn m hm (hwn.symm.trans hwm)

set_option maxHeartbeats 1000000 in
/-- On a Dedekind finite subset of `cantorSpace V ×ˢ B` the lexicographic order refined by `R₁`
is rigid. -/
theorem isRigidRelation_productLexRelation {A B R₁ : V}
    (hR : IsHereditarilyRigid B R₁)
    (hA : A ⊆ cantorSpace V ×ˢ B) (hdf : IsInternallyDedekindFinite A) :
    IsRigidRelation A (productLexRelation A R₁) := by
  classical
  refine ⟨productLexRelation_subset A R₁, ?_⟩
  have hfstmem : ∀ a ∈ A, kpair.π₁ a ∈ cantorSpace V :=
    fun a ha ↦ (eq_kpair_of_mem_prod (hA a ha)).2.1
  have hstep : ∀ u ∈ A, ∀ v ∈ A, ⟨u, v⟩ₖ ∈ productLexRelation A R₁ →
      ⟨kpair.π₁ u, kpair.π₁ v⟩ₖ ∈ cantorLexOrder (cantorSpace V) ∨
        kpair.π₁ u = kpair.π₁ v := by
    intro u hu v hv h
    rcases (kpair_mem_productLexRelation u v hu hv).mp h with h1 | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  intro f hf
  have hfA : ∀ a ∈ A, f ‘ a ∈ A := fun a ha ↦ function_value_mem hf.1 ha
  -- `f` fixes every first coordinate
  have hfst : ∀ a ∈ A, kpair.π₁ (f ‘ a) = kpair.π₁ a := by
    intro a ha
    have hfa : f ‘ a ∈ A := hfA a ha
    rcases cantorLexOrder_trichotomous (subset_refl (cantorSpace V))
      _ (hfstmem a ha) _ (hfstmem _ hfa) with h | h | h
    · exfalso
      have hxR : ⟨a, f ‘ a⟩ₖ ∈ productLexRelation A R₁ :=
        (kpair_mem_productLexRelation a (f ‘ a) ha hfa).mpr (Or.inl h)
      exact not_dedekindFinite_of_omega_cardLE
        (omega_cardLE_of_automorphism_lex_increasing hfstmem hstep hf ha hxR h) hdf
    · exact h.symm
    · exfalso
      have hinv : (converseGraph f) ‘ (f ‘ a) = a := converseGraph_value_value hf.1 hf.2.1 ha
      have hxR : ⟨f ‘ a, (converseGraph f) ‘ (f ‘ a)⟩ₖ ∈ productLexRelation A R₁ := by
        rw [hinv]
        exact (kpair_mem_productLexRelation (f ‘ a) a hfa ha).mpr (Or.inl h)
      refine not_dedekindFinite_of_omega_cardLE
        (omega_cardLE_of_automorphism_lex_increasing hfstmem hstep hf.converse hfa hxR ?_) hdf
      rw [hinv]
      exact h
  have hrel : ∀ u ∈ A, ∀ v ∈ A, kpair.π₁ u = kpair.π₁ v →
      (⟨u, v⟩ₖ ∈ productLexRelation A R₁ ↔ ⟨kpair.π₂ u, kpair.π₂ v⟩ₖ ∈ R₁) := by
    intro u hu v hv heq
    rw [kpair_mem_productLexRelation u v hu hv]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exfalso
        rw [heq] at h
        exact cantorLexOrder_irrefl _ _ (hfstmem v hv) h
      · exact h
    · intro h
      exact Or.inr ⟨heq, h⟩
  exact slice_fixed_of_hereditarilyRigid hR hA (subset_refl A) (fun a ha ↦ hfA a ha)
    (fun a ha ↦ hf.surjective ha) hfst hrel hf

/-! ### Theorem 4 -/

/-- Hamkins and Palumbo, Theorem 4: if `B` carries a hereditarily rigid irreflexive relation,
then every subset of `cantorSpace V ×ˢ B` carries a rigid relation. -/
theorem hasRigidRelation_of_subset_cantor_prod {A B R₁ : V}
    (hR : IsHereditarilyRigid B R₁) (hirr : ∀ b ∈ B, ⟨b, b⟩ₖ ∉ R₁)
    (hA : A ⊆ cantorSpace V ×ˢ B) : HasRigidRelation A := by
  classical
  by_cases hdf : IsInternallyDedekindFinite A
  · exact ⟨productLexRelation A R₁, isRigidRelation_productLexRelation hR hA hdf⟩
  · obtain ⟨z, hz, hinj⟩ := omega_cardLE_of_not_dedekindFinite hdf
    exact ⟨productChainRelation A z R₁, isRigidRelation_productChainRelation hR hirr hA hz hinj⟩

/-- Membership is a well order on an ordinal. -/
theorem isInternalWellOrder_membershipRelation_ordinal {γ : V} (hγ : IsOrdinal γ) :
    IsInternalWellOrder (membershipRelation γ) γ := by
  have : IsOrdinal γ := hγ
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, membershipRelation_wellFounded γ, ?_, ?_⟩
  · intro x hx y _ z hz hxy hyz
    have : IsOrdinal z := IsOrdinal.of_mem hz
    exact (pair_mem_membershipRelation γ x z).mpr ⟨hx, hz,
      IsOrdinal.toIsTransitive.mem_trans ((pair_mem_membershipRelation γ x y).mp hxy).2.2
        ((pair_mem_membershipRelation γ y z).mp hyz).2.2⟩
  · intro x hx y hy
    rcases hγ.trichotomy x hx y hy with h | h | h
    · exact Or.inl ((pair_mem_membershipRelation γ x y).mpr ⟨hx, hy, h⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ((pair_mem_membershipRelation γ y x).mpr ⟨hy, hx, h⟩))

/-- Every subset of `cantorSpace V ×ˢ γ` for an ordinal `γ` carries a rigid relation. -/
theorem hasRigidRelation_of_subset_cantor_ordinal {A γ : V} (hγ : IsOrdinal γ)
    (hA : A ⊆ cantorSpace V ×ˢ γ) : HasRigidRelation A := by
  refine hasRigidRelation_of_subset_cantor_prod
    (isHereditarilyRigid_of_isInternalWellOrder (isInternalWellOrder_membershipRelation_ordinal hγ))
    ?_ hA
  intro b hb hmem
  exact mem_irrefl b ((pair_mem_membershipRelation γ b b).mp hmem).2.2

end ZFVP
