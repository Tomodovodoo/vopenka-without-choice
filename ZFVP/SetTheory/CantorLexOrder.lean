import ZFVP.SetTheory.RigidRelation
import ZFVP.SetTheory.DedekindFinite
import ZFVP.SetTheory.CantorSpace
import ZFVP.SetTheory.NaturalIteration

/-! The third case of the Hamkins-Palumbo theorem that every set of reals carries a rigid
relation: a strict linear order on a Dedekind finite set is rigid, because a point moved by an
automorphism would start an infinite strictly increasing sequence of iterates. Applied to the
lexicographic order on a subset of Cantor space this gives a rigid relation on every Dedekind
finite set of reals. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The inverse of an automorphism -/

/-- The converse graph of an automorphism of `⟨A, R⟩` is again an automorphism. -/
theorem IsAutomorphismOf.converse {A R f : V} (hf : IsAutomorphismOf A R f) :
    IsAutomorphismOf A R (converseGraph f) := by
  have hfF : IsFunction f := IsFunction.of_mem hf.1
  have hran : range f = A := hf.2.2.1
  have hg : converseGraph f ∈ A ^ A := by
    have h := converseGraph_mem_function hf.1 hf.2.1
    rwa [hran] at h
  refine ⟨hg, converseGraph_injective f, ?_, ?_⟩
  · rw [range_converseGraph, domain_eq_of_mem_function hf.1]
  · intro u hu v hv
    have hgu : (converseGraph f) ‘ u ∈ A := function_value_mem hg hu
    have hgv : (converseGraph f) ‘ v ∈ A := function_value_mem hg hv
    have hur : u ∈ range f := by rw [hran]; exact hu
    have hvr : v ∈ range f := by rw [hran]; exact hv
    have hu' : f ‘ ((converseGraph f) ‘ u) = u := value_converseGraph_value hf.1 hf.2.1 hur
    have hv' : f ‘ ((converseGraph f) ‘ v) = v := value_converseGraph_value hf.1 hf.2.1 hvr
    have h := hf.2.2.2 _ hgu _ hgv
    rw [hu', hv'] at h
    exact h.symm

/-! ### A strict linear order on a Dedekind finite set is rigid -/

/-- If an automorphism moves a point strictly upwards then the set is Dedekind infinite. -/
theorem omega_cardLE_of_automorphism_increasing {A R f x : V}
    (htrans : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ⟨x, y⟩ₖ ∈ R → ⟨y, z⟩ₖ ∈ R → ⟨x, z⟩ₖ ∈ R)
    (hirr : ∀ x ∈ A, ⟨x, x⟩ₖ ∉ R)
    (hf : IsAutomorphismOf A R f) (hxA : x ∈ A) (hlt : ⟨x, f ‘ x⟩ₖ ∈ R) : (ω : V) ≤# A := by
  classical
  let F : V → V := fun z ↦ f ‘ z
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let b := naturalIteration F hF x
  have hbdef : ℒₛₑₜ-function₁ b := naturalIteration_definable F hF x
  have hb (n : V) (hn : n ∈ (ω : V)) : b n ∈ A :=
    naturalIteration_invariant F hF x (fun z ↦ z ∈ A) (by definability) hxA
      (fun z hz ↦ function_value_mem hf.1 hz) n hn
  have hzero : b 0 = x := naturalIteration_zero F hF x
  have hsucc (n : V) (hn : n ∈ (ω : V)) : b (succ n) = f ‘ (b n) := naturalIteration_succ F hF x hn
  -- each iterate is strictly below the next
  have hstep : ∀ n ∈ (ω : V), ⟨b n, b (succ n)⟩ₖ ∈ R := by
    apply naturalNumber_induction (fun n ↦ ⟨b n, b (succ n)⟩ₖ ∈ R) (by definability)
    · rw [hsucc 0 (by simp), hzero]
      exact hlt
    · intro n hn ih
      have h1 : ⟨f ‘ (b n), f ‘ (b (succ n))⟩ₖ ∈ R :=
        (hf.2.2.2 _ (hb n hn) _ (hb _ (ω_succ_closed hn))).mp ih
      rw [hsucc (succ n) (ω_succ_closed hn), hsucc n hn]
      rw [hsucc n hn] at h1
      exact h1
  -- hence strictly increasing along membership of natural numbers
  have hmono : ∀ n ∈ (ω : V), ∀ m ∈ n, ⟨b m, b n⟩ₖ ∈ R := by
    apply naturalNumber_induction (fun n ↦ ∀ m ∈ n, ⟨b m, b n⟩ₖ ∈ R) (by definability)
    · intro m hm
      simp [zero_def] at hm
    · intro n hn ih m hm
      rcases mem_succ_iff.mp hm with heqm | hmn
      · rw [heqm]
        exact hstep n hn
      · have hmω : m ∈ (ω : V) := IsOrdinal.toIsTransitive.mem_trans hmn hn
        exact htrans _ (hb m hmω) _ (hb n hn) _ (hb _ (ω_succ_closed hn)) (ih m hmn) (hstep n hn)
  have hdistinct : ∀ n ∈ (ω : V), ∀ m ∈ n, b m ≠ b n := by
    intro n hn m hm heq
    have hR := hmono n hn m hm
    rw [heq] at hR
    exact hirr _ (hb n hn) hR
  -- the iterates give an injection of `ω` into `A`
  let g := definableGraph (ω : V) b hbdef
  have hg : g ∈ A ^ (ω : V) := definableGraph_mem_function_of_mapsTo _ _ _ _ hb
  refine ⟨g, hg, ?_⟩
  intro n m z hnz hmz
  obtain ⟨hn, hzn⟩ := (pair_mem_definableGraph_iff (ω : V) b hbdef n z).mp hnz
  obtain ⟨hm, hzm⟩ := (pair_mem_definableGraph_iff (ω : V) b hbdef m z).mp hmz
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have : IsOrdinal m := IsOrdinal.of_mem hm
  have heq : b n = b m := hzn.symm.trans hzm
  rcases IsOrdinal.mem_trichotomy n m with hlt' | he | hgt
  · exact False.elim (hdistinct m hm n hlt' heq)
  · exact he
  · exact False.elim (hdistinct n hn m hgt heq.symm)

/-- A strict linear order on an infinite Dedekind finite set is rigid: a nontrivial automorphism
would move some point strictly up or strictly down, and its iterates would enumerate `ω` inside
the set. -/
theorem isRigidRelation_of_linearOrder_dedekindFinite {A R : V}
    (hRA : R ⊆ A ×ˢ A)
    (htrans : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ⟨x, y⟩ₖ ∈ R → ⟨y, z⟩ₖ ∈ R → ⟨x, z⟩ₖ ∈ R)
    (hirr : ∀ x ∈ A, ⟨x, x⟩ₖ ∉ R)
    (htri : ∀ x ∈ A, ∀ y ∈ A, ⟨x, y⟩ₖ ∈ R ∨ x = y ∨ ⟨y, x⟩ₖ ∈ R)
    (hdf : IsInternallyDedekindFinite A) :
    IsRigidRelation A R := by
  refine ⟨hRA, ?_⟩
  intro f hf x hxA
  by_contra hne
  have hfx : f ‘ x ∈ A := function_value_mem hf.1 hxA
  rcases htri x hxA (f ‘ x) hfx with h | h | h
  · exact not_dedekindFinite_of_omega_cardLE
      (omega_cardLE_of_automorphism_increasing htrans hirr hf hxA h) hdf
  · exact hne h.symm
  · have hinv : (converseGraph f) ‘ (f ‘ x) = x := converseGraph_value_value hf.1 hf.2.1 hxA
    refine not_dedekindFinite_of_omega_cardLE
      (omega_cardLE_of_automorphism_increasing htrans hirr hf.converse hfx ?_) hdf
    rw [hinv]
    exact h

/-! ### Restrictions of reals -/

/-- Two reals have the same restriction to `n` exactly when they agree below `n`. -/
theorem restrict_eq_iff_values {x y n : V} (hx : x ∈ cantorSpace V) (hy : y ∈ cantorSpace V)
    (hn : n ∈ (ω : V)) : x ↾ n = y ↾ n ↔ ∀ k ∈ n, x ‘ k = y ‘ k := by
  have hx' : x ∈ ((2 : ℕ) : V) ^ (ω : V) := (mem_cantorSpace_iff x).mp hx
  have hy' : y ∈ ((2 : ℕ) : V) ^ (ω : V) := (mem_cantorSpace_iff y).mp hy
  have : IsFunction x := IsFunction.of_mem hx'
  have : IsFunction y := IsFunction.of_mem hy'
  have hdx : domain x = (ω : V) := domain_eq_of_mem_function hx'
  have hdy : domain y = (ω : V) := domain_eq_of_mem_function hy'
  have hnω : n ⊆ (ω : V) := IsTransitive.transitive _ hn
  constructor
  · intro h k hk
    have hkω : k ∈ (ω : V) := hnω k hk
    have hkx : k ∈ domain x := hdx ▸ hkω
    have hky : k ∈ domain y := hdy ▸ hkω
    calc x ‘ k = (x ↾ n) ‘ k := (value_restrict hkx hk).symm
      _ = (y ↾ n) ‘ k := by rw [h]
      _ = y ‘ k := value_restrict hky hk
  · intro h
    exact restrict_eq_of_values (fun k hk ↦ hdx ▸ hnω k hk) (fun k hk ↦ hdy ▸ hnω k hk) h

/-- Reals agreeing at every natural number are equal. -/
theorem cantor_eq_of_values {x y : V} (hx : x ∈ cantorSpace V) (hy : y ∈ cantorSpace V)
    (h : ∀ k ∈ (ω : V), x ‘ k = y ‘ k) : x = y := by
  have hx' : x ∈ ((2 : ℕ) : V) ^ (ω : V) := (mem_cantorSpace_iff x).mp hx
  have hy' : y ∈ ((2 : ℕ) : V) ^ (ω : V) := (mem_cantorSpace_iff y).mp hy
  have : IsFunction x := IsFunction.of_mem hx'
  have : IsFunction y := IsFunction.of_mem hy'
  have hdx : domain x = (ω : V) := domain_eq_of_mem_function hx'
  have hdy : domain y = (ω : V) := domain_eq_of_mem_function hy'
  exact functions_eq_of_domain_values (hdx.trans hdy.symm) (fun k hk ↦ h k (hdx ▸ hk))

/-- The value of a real at a natural number is `0` or `1`. -/
theorem cantor_value_mem_two {x n : V} (hx : x ∈ cantorSpace V) (hn : n ∈ (ω : V)) :
    x ‘ n = 0 ∨ x ‘ n = 1 := by
  have hx' : x ∈ ((2 : ℕ) : V) ^ (ω : V) := (mem_cantorSpace_iff x).mp hx
  have h : x ‘ n ∈ ((2 : ℕ) : V) := function_value_mem hx' hn
  have h2 : x ‘ n ∈ (2 : V) := by simpa using h
  exact (mem_two_iff _).mp h2

/-! ### The lexicographic order on Cantor space -/

/-- `x` precedes `y` lexicographically: they agree below some `n` where `x` has a `0` and `y` a
`1`. -/
noncomputable def cantorLexOrder (A : V) : V :=
  {z ∈ A ×ˢ A ; ∃ n ∈ (ω : V), (kpair.π₁ z) ↾ n = (kpair.π₂ z) ↾ n ∧
    (kpair.π₁ z) ‘ n = 0 ∧ (kpair.π₂ z) ‘ n = 1}

instance cantorLexOrder_definable : ℒₛₑₜ-function₁[V] cantorLexOrder := by
  have h : ℒₛₑₜ-relation (fun S A : V ↦ ∀ z, z ∈ S ↔ z ∈ A ×ˢ A ∧ ∃ n ∈ (ω : V),
      (kpair.π₁ z) ↾ n = (kpair.π₂ z) ↾ n ∧
        (kpair.π₁ z) ‘ n = 0 ∧ (kpair.π₂ z) ‘ n = 1) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = cantorLexOrder (v 1) ↔ _
  rw [mem_ext_iff]
  simp [cantorLexOrder]

theorem kpair_mem_cantorLexOrder {A : V} (x y : V) (hx : x ∈ A) (hy : y ∈ A) :
    ⟨x, y⟩ₖ ∈ cantorLexOrder A ↔
      ∃ n ∈ (ω : V), x ↾ n = y ↾ n ∧ x ‘ n = 0 ∧ y ‘ n = 1 := by
  simp only [cantorLexOrder, mem_sep_iff, kpair.π₁_kpair, kpair.π₂_kpair,
    kpair_mem_iff, and_iff_right (And.intro hx hy)]

theorem cantorLexOrder_subset (A : V) : cantorLexOrder A ⊆ A ×ˢ A :=
  fun _ hz ↦ (mem_sep_iff.mp hz).1

theorem cantorLexOrder_irrefl (A : V) : ∀ x ∈ A, ⟨x, x⟩ₖ ∉ cantorLexOrder A := by
  intro x hx hmem
  obtain ⟨n, _, _, h0, h1⟩ := (kpair_mem_cantorLexOrder x x hx hx).mp hmem
  exact zero_ne_one (h0.symm.trans h1)

theorem cantorLexOrder_trans {A : V} (hA : A ⊆ cantorSpace V) :
    ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ⟨x, y⟩ₖ ∈ cantorLexOrder A → ⟨y, z⟩ₖ ∈ cantorLexOrder A →
      ⟨x, z⟩ₖ ∈ cantorLexOrder A := by
  intro x hx y hy z hz hxy hyz
  obtain ⟨n, hn, hres1, hx0, hy1⟩ := (kpair_mem_cantorLexOrder x y hx hy).mp hxy
  obtain ⟨m, hm, hres2, hy0, hz1⟩ := (kpair_mem_cantorLexOrder y z hy hz).mp hyz
  have hx' := hA x hx
  have hy' := hA y hy
  have hz' := hA z hz
  have e1 := (restrict_eq_iff_values hx' hy' hn).mp hres1
  have e2 := (restrict_eq_iff_values hy' hz' hm).mp hres2
  haveI : IsOrdinal n := IsOrdinal.of_mem hn
  haveI : IsOrdinal m := IsOrdinal.of_mem hm
  rcases IsOrdinal.mem_trichotomy n m with hlt | heq | hgt
  · -- the first difference of `x` and `y` comes before that of `y` and `z`
    refine (kpair_mem_cantorLexOrder x z hx hz).mpr ⟨n, hn, ?_, hx0, ?_⟩
    · refine (restrict_eq_iff_values hx' hz' hn).mpr (fun k hk ↦ ?_)
      exact (e1 k hk).trans (e2 k (IsOrdinal.toIsTransitive.mem_trans hk hlt))
    · rw [← e2 n hlt]
      exact hy1
  · rw [heq] at hy1
    exact absurd (hy1.symm.trans hy0) one_ne_zero
  · -- the first difference of `y` and `z` comes first
    refine (kpair_mem_cantorLexOrder x z hx hz).mpr ⟨m, hm, ?_, ?_, hz1⟩
    · refine (restrict_eq_iff_values hx' hz' hm).mpr (fun k hk ↦ ?_)
      exact (e1 k (IsOrdinal.toIsTransitive.mem_trans hk hgt)).trans (e2 k hk)
    · rw [e1 m hgt]
      exact hy0

theorem cantorLexOrder_trichotomous {A : V} (hA : A ⊆ cantorSpace V) :
    ∀ x ∈ A, ∀ y ∈ A,
      ⟨x, y⟩ₖ ∈ cantorLexOrder A ∨ x = y ∨ ⟨y, x⟩ₖ ∈ cantorLexOrder A := by
  classical
  intro x hx y hy
  by_cases hxy : x = y
  · exact Or.inr (Or.inl hxy)
  have hx' := hA x hx
  have hy' := hA y hy
  have hex : ∃ k ∈ (ω : V), x ‘ k ≠ y ‘ k := by
    by_contra hc
    push Not at hc
    exact hxy (cantor_eq_of_values hx' hy' (fun k hk ↦ hc k hk))
  obtain ⟨k₀, hk₀, hk₀ne⟩ := hex
  set S : V := {k ∈ (ω : V) ; x ‘ k ≠ y ‘ k} with hSdef
  haveI : IsNonempty S := ⟨k₀, mem_sep_iff.mpr ⟨hk₀, hk₀ne⟩⟩
  set n : V := ⋂ˢ S with hndef
  have hmS : n ∈ S :=
    IsOrdinal.sInter_mem (fun k hk ↦ IsOrdinal.of_mem (mem_sep_iff.mp hk).1)
  obtain ⟨hnω, hnne⟩ := mem_sep_iff.mp hmS
  -- below `n` the two reals agree
  have hmin : ∀ k ∈ n, x ‘ k = y ‘ k := by
    intro k hk
    by_contra hkne
    have hkω : k ∈ (ω : V) := IsOrdinal.toIsTransitive.mem_trans hk hnω
    have hsub : n ⊆ k := sInter_subset_of_mem_of_nonempty (mem_sep_iff.mpr ⟨hkω, hkne⟩)
    exact mem_irrefl k (hsub k hk)
  have hres : x ↾ n = y ↾ n := (restrict_eq_iff_values hx' hy' hnω).mpr hmin
  rcases cantor_value_mem_two hx' hnω with h0 | h1
  · rcases cantor_value_mem_two hy' hnω with g0 | g1
    · exact absurd (h0.trans g0.symm) hnne
    · exact Or.inl ((kpair_mem_cantorLexOrder x y hx hy).mpr ⟨n, hnω, hres, h0, g1⟩)
  · rcases cantor_value_mem_two hy' hnω with g0 | g1
    · exact Or.inr (Or.inr ((kpair_mem_cantorLexOrder y x hy hx).mpr
        ⟨n, hnω, hres.symm, g0, h1⟩))
    · exact absurd (h1.trans g1.symm) hnne

/-! ### Dedekind finite sets of reals are rigid -/

/-- Every Dedekind finite set of reals carries a rigid relation: the lexicographic order works,
because on a Dedekind finite set no automorphism of a linear order moves a point. -/
theorem hasRigidRelation_of_dedekindFinite_cantor {A : V} (hA : A ⊆ cantorSpace V)
    (hdf : IsInternallyDedekindFinite A) : HasRigidRelation A :=
  ⟨cantorLexOrder A, isRigidRelation_of_linearOrder_dedekindFinite (cantorLexOrder_subset A)
    (cantorLexOrder_trans hA) (cantorLexOrder_irrefl A) (cantorLexOrder_trichotomous hA) hdf⟩

end ZFVP
