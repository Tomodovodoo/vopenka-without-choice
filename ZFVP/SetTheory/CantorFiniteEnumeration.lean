import ZFVP.SetTheory.CantorLexOrder
import ZFVP.SetTheory.InternalOrderType
import ZFVP.SetTheory.FiniteSets
import ZFVP.SetTheory.Hessenberg

/-! Over ZF alone, an internally finite set of reals has exactly one enumeration that increases
in the lexicographic order of Cantor space. The transitive collapse of the lexicographic order
supplies the enumeration, and the collapse uniqueness theorem shows there is no other one. The
resulting map from finite sets of reals to finite sequences of reals is definable and injective,
which is what Jech's Lemma 5.25 needs to replace a finite support by a finite sequence. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Finite linear orders are well orders -/

/-- A nonempty internally finite subset of a linearly ordered set has a least element. -/
theorem exists_least_of_internallyFinite {A R : V}
    (htrans : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ⟨x, y⟩ₖ ∈ R → ⟨y, z⟩ₖ ∈ R → ⟨x, z⟩ₖ ∈ R)
    (hirr : ∀ x ∈ A, ⟨x, x⟩ₖ ∉ R)
    (htri : ∀ x ∈ A, ∀ y ∈ A, ⟨x, y⟩ₖ ∈ R ∨ x = y ∨ ⟨y, x⟩ₖ ∈ R)
    {B : V} (hBf : IsInternallyFinite B) (hBA : B ⊆ A) (hne : IsNonempty B) :
    ∃ x ∈ B, ∀ y ∈ B, ⟨y, x⟩ₖ ∉ R := by
  classical
  revert hBA hne
  refine internallyFinite_induction
    (fun B ↦ B ⊆ A → IsNonempty B → ∃ x ∈ B, ∀ y ∈ B, ⟨y, x⟩ₖ ∉ R) (by definability) ?_ ?_ B hBf
  · intro _ hne
    obtain ⟨x, hx⟩ := hne.nonempty
    exact absurd hx not_mem_empty
  · intro C a ih hsub _
    have haA : a ∈ A := hsub a (mem_insert.mpr (Or.inl rfl))
    have hCA : C ⊆ A := fun z hz ↦ hsub z (mem_insert.mpr (Or.inr hz))
    by_cases hC : IsNonempty C
    · obtain ⟨x, hxC, hxmin⟩ := ih hCA hC
      have hxA : x ∈ A := hCA x hxC
      rcases htri a haA x hxA with hax | heq | hxa
      · refine ⟨a, mem_insert.mpr (Or.inl rfl), ?_⟩
        intro y hy hya
        rcases mem_insert.mp hy with rfl | hyC
        · exact hirr y (hsub y hy) hya
        · exact hxmin y hyC (htrans y (hCA y hyC) a haA x hxA hya hax)
      · refine ⟨x, mem_insert.mpr (Or.inr hxC), ?_⟩
        intro y hy hyx
        rcases mem_insert.mp hy with rfl | hyC
        · exact hirr x hxA (heq ▸ hyx)
        · exact hxmin y hyC hyx
      · refine ⟨x, mem_insert.mpr (Or.inr hxC), ?_⟩
        intro y hy hyx
        rcases mem_insert.mp hy with rfl | hyC
        · exact hirr x hxA (htrans x hxA y (hsub y hy) x hxA hxa hyx)
        · exact hxmin y hyC hyx
    · refine ⟨a, mem_insert.mpr (Or.inl rfl), ?_⟩
      intro y hy hya
      rcases mem_insert.mp hy with rfl | hyC
      · exact hirr y (hsub y hy) hya
      · exact hC ⟨y, hyC⟩

/-- On an internally finite set of reals the lexicographic order is well founded. -/
theorem cantorLexOrder_wellFounded {A : V} (hA : A ⊆ cantorSpace V)
    (hAf : IsInternallyFinite A) : IsInternallyWellFounded (cantorLexOrder A) A := by
  intro B hBA hne
  exact exists_least_of_internallyFinite (cantorLexOrder_trans hA) (cantorLexOrder_irrefl A)
    (cantorLexOrder_trichotomous hA) (internallyFinite_subset hAf hBA) hBA hne

/-- On an internally finite set of reals the lexicographic order is a well order. -/
theorem cantorLexOrder_wellOrder {A : V} (hA : A ⊆ cantorSpace V)
    (hAf : IsInternallyFinite A) : IsInternalWellOrder (cantorLexOrder A) A :=
  ⟨cantorLexOrder_subset A, cantorLexOrder_wellFounded hA hAf, cantorLexOrder_trans hA,
    cantorLexOrder_trichotomous hA⟩

/-- The lexicographic order of a subset is the restriction of the one of Cantor space. -/
theorem kpair_mem_cantorLexOrder_iff {A x y : V} (hA : A ⊆ cantorSpace V)
    (hx : x ∈ A) (hy : y ∈ A) :
    ⟨x, y⟩ₖ ∈ cantorLexOrder A ↔ ⟨x, y⟩ₖ ∈ cantorLexOrder (cantorSpace V) := by
  rw [kpair_mem_cantorLexOrder x y hx hy, kpair_mem_cantorLexOrder x y (hA x hx) (hA y hy)]

/-- An internally finite ordinal is a natural number. -/
theorem mem_omega_of_internallyFinite_ordinal {α : V} [IsOrdinal α]
    (h : IsInternallyFinite α) : α ∈ (ω : V) := by
  obtain ⟨n, hn, hle, _⟩ := h
  have : IsOrdinal (ω : V) := IsOrdinal.ω
  have hcontra : (ω : V) ⊆ α → False := fun hsub ↦
    omega_not_cardLE_natural hn ((cardLE_of_subset hsub).trans hle)
  rcases IsOrdinal.mem_trichotomy α (ω : V) with hlt | heq | hgt
  · exact hlt
  · exact absurd (fun z hz ↦ heq ▸ hz) hcontra
  · exact absurd (IsOrdinal.toIsTransitive.transitive _ hgt) hcontra

/-- Inverting a function graph twice gives it back. -/
theorem converseGraph_converse (f : V) [IsFunction f] : converseGraph (converseGraph f) = f := by
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    exact (pair_mem_converseGraph f y x).mp ((pair_mem_converseGraph (converseGraph f) x y).mp hz)
  · intro hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    exact (pair_mem_converseGraph (converseGraph f) x y).mpr ((pair_mem_converseGraph f y x).mpr hz)

/-! ### Lexicographically increasing enumerations -/

/-- `s` lists the elements of `A` once each, in increasing lexicographic order. -/
def IsLexEnumeration (s A : V) : Prop :=
  (∃ n ∈ (ω : V), s ∈ A ^ n) ∧ range s = A ∧
    ∀ i ∈ domain s, ∀ j ∈ domain s, i ∈ j → ⟨s ‘ i, s ‘ j⟩ₖ ∈ cantorLexOrder (cantorSpace V)

instance isLexEnumeration_definable : ℒₛₑₜ-relation[V] IsLexEnumeration := by
  unfold IsLexEnumeration
  definability

theorem lexEnumeration_length {s A : V} (hs : IsLexEnumeration s A) :
    domain s ∈ (ω : V) ∧ s ∈ A ^ domain s := by
  obtain ⟨⟨n, hn, hsn⟩, _, _⟩ := hs
  have hd : domain s = n := domain_eq_of_mem_function hsn
  exact ⟨hd ▸ hn, hd ▸ hsn⟩

/-- A lexicographically increasing enumeration repeats no value. -/
theorem lexEnumeration_injective {s A : V} (hA : A ⊆ cantorSpace V)
    (hs : IsLexEnumeration s A) : Injective s := by
  obtain ⟨hnω, hsn⟩ := lexEnumeration_length hs
  have : IsFunction s := IsFunction.of_mem hsn
  intro i j y hi hj
  have hiD : i ∈ domain s := mem_domain_of_kpair_mem hi
  have hjD : j ∈ domain s := mem_domain_of_kpair_mem hj
  have hvi : s ‘ i = y := value_eq_of_kpair_mem hi
  have hvj : s ‘ j = y := value_eq_of_kpair_mem hj
  have hyA : y ∈ A := by
    rw [← hvi]
    exact function_value_mem hsn (by simpa [domain_eq_of_mem_function hsn] using hiD)
  have : IsOrdinal i := IsOrdinal.of_mem (IsOrdinal.toIsTransitive.mem_trans hiD hnω)
  have : IsOrdinal j := IsOrdinal.of_mem (IsOrdinal.toIsTransitive.mem_trans hjD hnω)
  rcases IsOrdinal.mem_trichotomy i j with hlt | heq | hgt
  · have h := hs.2.2 i hiD j hjD hlt
    rw [hvi, hvj] at h
    exact absurd h (cantorLexOrder_irrefl (cantorSpace V) y (hA y hyA))
  · exact heq
  · have h := hs.2.2 j hjD i hiD hgt
    rw [hvi, hvj] at h
    exact absurd h (cantorLexOrder_irrefl (cantorSpace V) y (hA y hyA))

/-- The set enumerated by a lexicographic enumeration is internally finite. -/
theorem internallyFinite_of_lexEnumeration {s A : V} (hA : A ⊆ cantorSpace V)
    (hs : IsLexEnumeration s A) : IsInternallyFinite A := by
  obtain ⟨hnω, hsn⟩ := lexEnumeration_length hs
  have : IsFunction s := IsFunction.of_mem hsn
  have hconv : converseGraph s ∈ domain s ^ A := by
    have h := converseGraph_mem_function hsn (lexEnumeration_injective hA hs)
    rwa [hs.2.1] at h
  exact internallyFinite_of_cardLE_natural hnω ⟨converseGraph s, hconv, converseGraph_injective s⟩

/-- Reading a lexicographic enumeration backwards is the transitive collapse of the
lexicographic order. -/
theorem lexEnumeration_transitiveCollapse {s A : V} (hA : A ⊆ cantorSpace V)
    (hs : IsLexEnumeration s A) :
    IsTransitiveCollapse (cantorLexOrder A) A (domain s) (converseGraph s) := by
  obtain ⟨hnω, hsn⟩ := lexEnumeration_length hs
  have : IsFunction s := IsFunction.of_mem hsn
  have hinj : Injective s := lexEnumeration_injective hA hs
  have hconv : converseGraph s ∈ domain s ^ A := by
    have h := converseGraph_mem_function hsn hinj
    rwa [hs.2.1] at h
  have : IsFunction (converseGraph s) := IsFunction.of_mem hconv
  have : IsOrdinal (domain s) := IsOrdinal.of_mem hnω
  have hback : ∀ x ∈ A, s ‘ ((converseGraph s) ‘ x) = x := fun x hx ↦
    value_converseGraph_value hsn hinj (hs.2.1.symm ▸ hx)
  have hindex : ∀ x ∈ A, (converseGraph s) ‘ x ∈ domain s := fun x hx ↦
    function_value_mem hconv hx
  refine ⟨IsOrdinal.toIsTransitive, hconv, ?_, ?_, ?_⟩
  · rw [range_converseGraph]
  · intro x hx y hy heq
    rw [← hback x hx, ← hback y hy, heq]
  · intro x hx y hy
    have hix := hindex x hx
    have hiy := hindex y hy
    have : IsOrdinal ((converseGraph s) ‘ x) :=
      IsOrdinal.of_mem (IsOrdinal.toIsTransitive.mem_trans hix hnω)
    have : IsOrdinal ((converseGraph s) ‘ y) :=
      IsOrdinal.of_mem (IsOrdinal.toIsTransitive.mem_trans hiy hnω)
    constructor
    · intro hmem
      have h := hs.2.2 _ hix _ hiy hmem
      rw [hback x hx, hback y hy] at h
      exact (kpair_mem_cantorLexOrder_iff hA hx hy).mpr h
    · intro hxy
      rcases IsOrdinal.mem_trichotomy ((converseGraph s) ‘ x) ((converseGraph s) ‘ y) with
        hlt | heq | hgt
      · exact hlt
      · have : x = y := by rw [← hback x hx, ← hback y hy, heq]
        exact absurd (this ▸ hxy) (cantorLexOrder_irrefl A x hx)
      · have h := hs.2.2 _ hiy _ hix hgt
        rw [hback x hx, hback y hy] at h
        exact absurd (cantorLexOrder_trans hA x hx y hy x hx hxy
            ((kpair_mem_cantorLexOrder_iff hA hy hx).mpr h))
          (cantorLexOrder_irrefl A x hx)

/-! ### Existence and uniqueness -/

/-- Every internally finite set of reals has a lexicographically increasing enumeration. -/
theorem exists_lexEnumeration {A : V} (hA : A ⊆ cantorSpace V) (hAf : IsInternallyFinite A) :
    ∃ s, IsLexEnumeration s A := by
  have hwo := cantorLexOrder_wellOrder hA hAf
  have hwf := hwo.2.1
  have hext := internalWellOrder_extensional hwo
  have hc := mostowskiMap_isTransitiveCollapse hwf hext
  set f := mostowskiMap (cantorLexOrder A) A with hfdef
  have hf : f ∈ range f ^ A := hc.2.1
  have : IsFunction f := IsFunction.of_mem hf
  have hdf : domain f = A := domain_eq_of_mem_function hf
  have hinj : Injective f := by
    intro x₁ x₂ y h1 h2
    exact hc.2.2.2.1 x₁ (hdf ▸ mem_domain_of_kpair_mem h1) x₂ (hdf ▸ mem_domain_of_kpair_mem h2)
      ((value_eq_of_kpair_mem h1).trans (value_eq_of_kpair_mem h2).symm)
  have hconv : converseGraph f ∈ A ^ range f := converseGraph_mem_function hf hinj
  have : IsFunction (converseGraph f) := IsFunction.of_mem hconv
  have hord : IsOrdinal (range f) := by
    have h := internalOrderType_ordinal hwo
    rwa [internalOrderType] at h
  have hfin : IsInternallyFinite (range f) :=
    internallyFinite_of_cardLE hAf ⟨converseGraph f, hconv, converseGraph_injective f⟩
  have hωn : range f ∈ (ω : V) := mem_omega_of_internallyFinite_ordinal hfin
  have hdconv : domain (converseGraph f) = range f := domain_eq_of_mem_function hconv
  refine ⟨converseGraph f, ⟨range f, hωn, hconv⟩, ?_, ?_⟩
  · rw [range_converseGraph, hdf]
  · intro i hi j hj hij
    rw [hdconv] at hi hj
    have hxi : (converseGraph f) ‘ i ∈ A := function_value_mem hconv hi
    have hxj : (converseGraph f) ‘ j ∈ A := function_value_mem hconv hj
    have hvi : f ‘ ((converseGraph f) ‘ i) = i := value_converseGraph_value hf hinj hi
    have hvj : f ‘ ((converseGraph f) ‘ j) = j := value_converseGraph_value hf hinj hj
    have h := (hc.2.2.2.2 _ hxi _ hxj).mp (by rw [hvi, hvj]; exact hij)
    exact (kpair_mem_cantorLexOrder_iff hA hxi hxj).mp h

/-- There is at most one lexicographically increasing enumeration of a set of reals. -/
theorem lexEnumeration_unique {A s t : V} (hA : A ⊆ cantorSpace V)
    (hs : IsLexEnumeration s A) (ht : IsLexEnumeration t A) : s = t := by
  have hAf : IsInternallyFinite A := internallyFinite_of_lexEnumeration hA hs
  have hwf := cantorLexOrder_wellFounded hA hAf
  have : IsFunction s := IsFunction.of_mem (lexEnumeration_length hs).2
  have : IsFunction t := IsFunction.of_mem (lexEnumeration_length ht).2
  have h1 := (transitiveCollapse_unique hwf (lexEnumeration_transitiveCollapse hA hs)).1
  have h2 := (transitiveCollapse_unique hwf (lexEnumeration_transitiveCollapse hA ht)).1
  have hconv : converseGraph s = converseGraph t := h1.trans h2.symm
  calc s = converseGraph (converseGraph s) := (converseGraph_converse s).symm
    _ = converseGraph (converseGraph t) := by rw [hconv]
    _ = t := converseGraph_converse t

/-! ### The definable enumeration operation -/

/-- The lexicographically increasing enumeration of a set of reals, read off from the unique
element of a bounded separation. -/
noncomputable def lexEnumeration (A : V) : V := ⋃ˢ {s ∈ ℘ ((ω : V) ×ˢ A) ; IsLexEnumeration s A}

instance lexEnumeration_definable : ℒₛₑₜ-function₁[V] lexEnumeration := by
  have h : ℒₛₑₜ-relation (fun u A : V ↦ ∀ z, z ∈ u ↔
      ∃ s, (s ∈ ℘ ((ω : V) ×ˢ A) ∧ IsLexEnumeration s A) ∧ z ∈ s) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = lexEnumeration (v 1) ↔ _
  rw [mem_ext_iff]
  simp [lexEnumeration, mem_sUnion_iff, mem_sep_iff]

theorem lexEnumeration_spec {A : V} (hA : A ⊆ cantorSpace V) (hAf : IsInternallyFinite A) :
    IsLexEnumeration (lexEnumeration A) A := by
  obtain ⟨s, hs⟩ := exists_lexEnumeration hA hAf
  obtain ⟨hnω, hsn⟩ := lexEnumeration_length hs
  have : IsFunction s := IsFunction.of_mem hsn
  have hsub : s ⊆ (ω : V) ×ˢ A :=
    subset_trans (subset_prod_of_mem_function hsn)
      (prod_subset_prod_of_subset (IsTransitive.transitive _ hnω) (subset_refl A))
  have hset : {u ∈ ℘ ((ω : V) ×ˢ A) ; IsLexEnumeration u A} = ({s} : V) := by
    apply mem_ext
    intro z
    rw [mem_sep_iff, mem_singleton_iff]
    constructor
    · rintro ⟨_, hz⟩
      exact lexEnumeration_unique hA hz hs
    · rintro rfl
      exact ⟨mem_power_iff.mpr hsub, hs⟩
  have hun : lexEnumeration A = s := by
    rw [lexEnumeration, hset]
    apply mem_ext
    intro z
    rw [mem_sUnion_iff]
    constructor
    · rintro ⟨u, hu, hzu⟩
      rwa [mem_singleton_iff.mp hu] at hzu
    · intro hz
      exact ⟨s, mem_singleton_iff.mpr rfl, hz⟩
  rw [hun]
  exact hs

theorem lexEnumeration_mem_finiteSequences {A : V} (hA : A ⊆ cantorSpace V)
    (hAf : IsInternallyFinite A) : lexEnumeration A ∈ finiteSequences (cantorSpace V) := by
  obtain ⟨⟨n, hn, hsn⟩, _, _⟩ := lexEnumeration_spec hA hAf
  exact (mem_finiteSequences_iff _ _).mpr
    ⟨n, hn, mem_function_of_mem_function_of_subset hsn hA⟩

theorem lexEnumeration_inj {A B : V} (hA : A ⊆ cantorSpace V) (hAf : IsInternallyFinite A)
    (hB : B ⊆ cantorSpace V) (hBf : IsInternallyFinite B)
    (h : lexEnumeration A = lexEnumeration B) : A = B := by
  have hsA := (lexEnumeration_spec hA hAf).2.1
  have hsB := (lexEnumeration_spec hB hBf).2.1
  rw [← hsA, ← hsB, h]

end ZFVP
