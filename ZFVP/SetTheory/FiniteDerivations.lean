import ZFVP.SetTheory.PathDependentChoice

/-! Internally finite derivations whose rules refer to earlier conclusions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsFiniteDerivation (R : V → V → Prop) (A s : V) : Prop :=
  s ∈ finiteSequences A ∧ ∀ i ∈ domain s, R (range (s ↾ i)) (s ‘ i)

theorem isFiniteDerivation_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) (A : V) :
    ℒₛₑₜ-predicate (IsFiniteDerivation R A) := by
  unfold IsFiniteDerivation
  definability

theorem isFiniteDerivation_empty (R : V → V → Prop) (A : V) : IsFiniteDerivation R A ∅ := by
  exact ⟨empty_mem_finiteSequences A, by simp⟩

theorem isFiniteDerivation_append_iff (R : V → V → Prop) {A s n x : V}
    (hn : n ∈ (ω : V)) (hs : s ∈ A ^ n) (hx : x ∈ A) :
    IsFiniteDerivation R A (insert ⟨n, x⟩ₖ s) ↔ IsFiniteDerivation R A s ∧ R (range s) x := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have happ := function_append_mem hs hx
  have hd := domain_eq_of_mem_function hs
  have hda := domain_eq_of_mem_function happ
  have hold (i : V) (hi : i ∈ n) :
      R (range ((insert ⟨n, x⟩ₖ s) ↾ i)) ((insert ⟨n, x⟩ₖ s) ‘ i) ↔ R (range (s ↾ i)) (s ‘ i) := by
    have hni : n ∉ i := fun hni ↦ mem_irrefl n (IsOrdinal.toIsTransitive.mem_trans hni hi)
    rw [restrict_insert_kpair_eq_restrict_of_not_mem hni, function_append_value_old hs hx hi]
  have hnew : R (range ((insert ⟨n, x⟩ₖ s) ↾ n)) ((insert ⟨n, x⟩ₖ s) ‘ n) ↔ R (range s) x := by
    rw [function_append_restrict hs, function_append_value_new hs hx]
  constructor
  · intro h
    refine ⟨⟨(mem_finiteSequences_iff A s).mpr ⟨n, hn, hs⟩, ?_⟩, ?_⟩
    · intro i hi
      have hin : i ∈ n := hd ▸ hi
      exact (hold i hin).mp (h.2 i (by rw [hda]; exact mem_succ_iff.mpr (Or.inr hin)))
    · exact hnew.mp (h.2 n (by rw [hda]; simp))
  · rintro ⟨hsd, hr⟩
    refine ⟨(mem_finiteSequences_iff A _).mpr ⟨succ n, ω_succ_closed hn, happ⟩, ?_⟩
    intro i hi
    rcases mem_succ_iff.mp (hda ▸ hi) with rfl | hi
    · exact hnew.mpr hr
    · exact (hold i hi).mpr (hsd.2 i (hd.symm ▸ hi))

theorem finiteDerivations_merge (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (hmono : ∀ S T x : V, S ⊆ T → R S x → R T x) {A s t : V}
    (hs : IsFiniteDerivation R A s) (ht : IsFiniteDerivation R A t) :
    ∃ u, IsFiniteDerivation R A u ∧ range s ⊆ range u ∧ range t ⊆ range u := by
  have hD := isFiniteDerivation_definable R hR A
  have hall : ∀ t ∈ finiteSequences A, IsFiniteDerivation R A t →
      ∃ u, IsFiniteDerivation R A u ∧ range s ⊆ range u ∧ range t ⊆ range u := by
    apply finiteSequence_induction A (fun t ↦ IsFiniteDerivation R A t →
      ∃ u, IsFiniteDerivation R A u ∧ range s ⊆ range u ∧ range t ⊆ range u) (by definability)
    · intro _
      exact ⟨s, hs, subset_refl _, by simp⟩
    · intro n hn t htf x hx ih hta
      obtain ⟨htd, hrx⟩ := (isFiniteDerivation_append_iff R hn htf hx).mp hta
      obtain ⟨u, hu, hsu, htu⟩ := ih htd
      obtain ⟨hnu, huf⟩ := (mem_finiteSequences_iff_domain A u).mp hu.1
      refine ⟨insert ⟨domain u, x⟩ₖ u,
        (isFiniteDerivation_append_iff R hnu huf hx).mpr ⟨hu, hmono _ _ _ htu hrx⟩, ?_, ?_⟩
      · intro y hy
        rw [range_insert]
        exact mem_insert.mpr (Or.inr (hsu y hy))
      · intro y hy
        rw [range_insert] at hy ⊢
        exact (mem_insert.mp hy).elim (fun hy ↦ mem_insert.mpr (Or.inl hy))
          (fun hy ↦ mem_insert.mpr (Or.inr (htu y hy)))
  exact hall t ht.1 ht

theorem finiteDerivation_extend (R : V → V → Prop) {A s x : V} (hs : IsFiniteDerivation R A s)
    (hx : x ∈ A) (hr : R (range s) x) :
    ∃ t, IsFiniteDerivation R A t ∧ x ∈ range t ∧ range s ⊆ range t := by
  obtain ⟨hn, hsf⟩ := (mem_finiteSequences_iff_domain A s).mp hs.1
  refine ⟨insert ⟨domain s, x⟩ₖ s, (isFiniteDerivation_append_iff R hn hsf hx).mpr ⟨hs, hr⟩, ?_, ?_⟩
  · simp only [range_insert]
    exact mem_insert.mpr (Or.inl rfl)
  · intro y hy
    simp only [range_insert]
    exact mem_insert.mpr (Or.inr hy)

theorem finiteDerivation_sound (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (A Q : V) (hclosed : ∀ S x : V, S ⊆ Q → R S x → x ∈ Q) :
    ∀ s, IsFiniteDerivation R A s → range s ⊆ Q := by
  have hD := isFiniteDerivation_definable R hR A
  have hall : ∀ s ∈ finiteSequences A, IsFiniteDerivation R A s → range s ⊆ Q := by
    apply finiteSequence_induction A (fun s ↦ IsFiniteDerivation R A s → range s ⊆ Q) (by definability)
    · intro _
      simp
    · intro n hn s hsf x hx ih hsa
      obtain ⟨hsd, hrx⟩ := (isFiniteDerivation_append_iff R hn hsf hx).mp hsa
      have hsq := ih hsd
      intro y hy
      rw [range_insert] at hy
      exact (mem_insert.mp hy).elim (fun hy ↦ hy ▸ hclosed _ _ hsq hrx) (hsq y)
  intro s hs
  exact hall s hs.1 hs

end ZFVP
