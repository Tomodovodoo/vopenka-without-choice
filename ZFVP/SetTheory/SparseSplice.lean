import ZFVP.SetTheory.SparseFunctionUnion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def sparsePrefixReplace (a q b : V) : V := b ∪ (q ↾ (domain q \ a))

instance sparsePrefixReplace_definable : ℒₛₑₜ-function₃[V] sparsePrefixReplace := by
  unfold sparsePrefixReplace
  definability

theorem kpair_mem_sparsePrefixReplace_iff {a q b x y : V} :
    ⟨x, y⟩ₖ ∈ sparsePrefixReplace a q b ↔ ⟨x, y⟩ₖ ∈ b ∨ (⟨x, y⟩ₖ ∈ q ∧ x ∉ a) := by
  simp only [sparsePrefixReplace, mem_union_iff, kpair_mem_restrict_iff, mem_sdiff_iff]
  constructor
  · rintro (h | ⟨h, _, hn⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h, hn⟩
  · rintro (h | ⟨h, hn⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h, mem_domain_of_kpair_mem h, hn⟩

theorem sparsePrefixReplace_isFunction {a q b : V} [IsFunction q] [IsFunction b]
    (hb : domain b ⊆ a) : IsFunction (sparsePrefixReplace a q b) := by
  apply isFunction_iff.mpr
  apply mem_function.intro
  · intro z hz
    rcases mem_union_iff.mp hz with hz | hz
    · obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
      have hz' := kpair_mem_sparsePrefixReplace_iff.mpr (Or.inl hz : ⟨x, y⟩ₖ ∈ b ∨ (⟨x, y⟩ₖ ∈ q ∧ x ∉ a))
      exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hz', mem_range_of_kpair_mem hz'⟩
    · have hzq := (mem_restrict_iff.mp hz).1
      obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hzq
      have hz' : ⟨x, y⟩ₖ ∈ sparsePrefixReplace a q b := mem_union_iff.mpr (Or.inr hz)
      exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hz', mem_range_of_kpair_mem hz'⟩
  · intro x hx
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
    refine ⟨y, hy, ?_⟩
    intro z hz
    rcases kpair_mem_sparsePrefixReplace_iff.mp hz with hz | ⟨hz, hnz⟩ <;>
      rcases kpair_mem_sparsePrefixReplace_iff.mp hy with hy | ⟨hy, hny⟩
    · exact IsFunction.unique hz hy
    · exact (hny (hb x (mem_domain_of_kpair_mem hz))).elim
    · exact (hnz (hb x (mem_domain_of_kpair_mem hy))).elim
    · exact IsFunction.unique hz hy

theorem mem_domain_sparsePrefixReplace_iff {a q b x : V} :
    x ∈ domain (sparsePrefixReplace a q b) ↔ x ∈ domain b ∨ (x ∈ domain q ∧ x ∉ a) := by
  simp only [mem_domain_iff, kpair_mem_sparsePrefixReplace_iff]
  constructor
  · rintro ⟨y, hy | ⟨hy, hn⟩⟩
    · exact Or.inl ⟨y, hy⟩
    · exact Or.inr ⟨⟨y, hy⟩, hn⟩
  · rintro (⟨y, hy⟩ | ⟨⟨y, hy⟩, hn⟩)
    · exact ⟨y, Or.inl hy⟩
    · exact ⟨y, Or.inr ⟨hy, hn⟩⟩

private theorem function_eq_of_pair_iff {f g : V} [IsFunction f] [IsFunction g]
    (h : ∀ x y, ⟨x, y⟩ₖ ∈ f ↔ ⟨x, y⟩ₖ ∈ g) : f = g := by
  apply mem_ext
  intro z
  constructor <;> intro hz
  · obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    exact (h x y).mp hz
  · obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    exact (h x y).mpr hz

theorem sparsePrefixReplace_restrict {a q b : V} [IsFunction q] [IsFunction b]
    (hb : domain b ⊆ a) : (sparsePrefixReplace a q b) ↾ a = b := by
  let := sparsePrefixReplace_isFunction (q := q) hb
  apply function_eq_of_pair_iff
  intro x y
  simp only [kpair_mem_restrict_iff, kpair_mem_sparsePrefixReplace_iff]
  constructor
  · rintro ⟨h | ⟨_, hn⟩, hx⟩
    · exact h
    · exact (hn hx).elim
  · intro h
    exact ⟨Or.inl h, hb x (mem_domain_of_kpair_mem h)⟩

theorem sparsePrefixReplace_value {a q b x : V} [IsFunction q] [IsFunction b]
    (hb : domain b ⊆ a) : (sparsePrefixReplace a q b) ‘ x =
      @ite V (x ∈ a) (Classical.propDecidable _) (b ‘ x) (q ‘ x) := by
  classical
  let := sparsePrefixReplace_isFunction (q := q) hb
  by_cases ha : x ∈ a
  · rw [ite_eq_left ha]
    by_cases hx : x ∈ domain b
    · exact value_eq_of_kpair_mem (kpair_mem_sparsePrefixReplace_iff.mpr (Or.inl (kpair_value_mem hx)))
    · rw [value_eq_empty_of_not_mem_domain hx]
      apply value_eq_empty_of_not_mem_domain
      rw [mem_domain_sparsePrefixReplace_iff]
      tauto
  · rw [ite_eq_right ha]
    by_cases hx : x ∈ domain q
    · exact value_eq_of_kpair_mem (kpair_mem_sparsePrefixReplace_iff.mpr (Or.inr ⟨kpair_value_mem hx, ha⟩))
    · rw [value_eq_empty_of_not_mem_domain hx]
      apply value_eq_empty_of_not_mem_domain
      rw [mem_domain_sparsePrefixReplace_iff]
      rintro (hb' | ⟨hq, _⟩)
      · exact ha (hb x hb')
      · exact hx hq

theorem IsSparseFunctionOn.prefixReplace {a B q b : V}
    (hq : IsSparseFunctionOn B q) (hb : IsSparseFunctionOn a b) (ha : a ⊆ B) :
    IsSparseFunctionOn B (sparsePrefixReplace a q b) := by
  let := hq.1
  let := hb.1
  refine ⟨sparsePrefixReplace_isFunction hb.2.1, ?_, ?_⟩
  · intro x hx
    rcases mem_domain_sparsePrefixReplace_iff.mp hx with hx | ⟨hx, _⟩
    · exact ha x (hb.2.1 x hx)
    · exact hq.2.1 x hx
  · intro x hx
    rw [sparsePrefixReplace_value hb.2.1]
    rcases mem_domain_sparsePrefixReplace_iff.mp hx with hx | ⟨hx, hn⟩
    · rw [ite_eq_left (hb.2.1 x hx)]
      exact hb.2.2 x hx
    · rw [ite_eq_right hn]
      exact hq.2.2 x hx

theorem sparsePrefixReplace_self {a q : V} [IsFunction q] :
    sparsePrefixReplace a q (q ↾ a) = q := by
  have hb : domain (q ↾ a) ⊆ a := by
    intro x hx
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
    exact (kpair_mem_restrict_iff.mp hy).2
  let := sparsePrefixReplace_isFunction (q := q) hb
  apply function_eq_of_pair_iff
  intro x y
  simp only [kpair_mem_sparsePrefixReplace_iff, kpair_mem_restrict_iff]
  tauto

theorem sparsePrefixReplace_restrict_larger {a d q b : V} [IsFunction q] [IsFunction b]
    (hb : domain b ⊆ a) (had : a ⊆ d) :
    (sparsePrefixReplace a q b) ↾ d = sparsePrefixReplace a (q ↾ d) b := by
  let := sparsePrefixReplace_isFunction (q := q) hb
  let := sparsePrefixReplace_isFunction (q := q ↾ d) hb
  apply function_eq_of_pair_iff
  intro x y
  simp only [kpair_mem_restrict_iff, kpair_mem_sparsePrefixReplace_iff]
  have hbd : ⟨x, y⟩ₖ ∈ b → x ∈ d := fun h ↦ had x (hb x (mem_domain_of_kpair_mem h))
  tauto

theorem sparsePrefixReplace_tail {a d q b : V} [IsFunction q] [IsFunction b]
    (hb : domain b ⊆ a) :
    (sparsePrefixReplace a q b) ↾ (d \ a) = q ↾ (d \ a) := by
  let := sparsePrefixReplace_isFunction (q := q) hb
  apply function_eq_of_pair_iff
  intro x y
  simp only [kpair_mem_restrict_iff, kpair_mem_sparsePrefixReplace_iff, mem_sdiff_iff]
  have hba : ⟨x, y⟩ₖ ∈ b → x ∈ a := fun h ↦ hb x (mem_domain_of_kpair_mem h)
  tauto

theorem sparsePrefixReplace_empty_tail {a q b : V} [IsFunction q] [IsFunction b]
    (hq : domain q ⊆ a) (hb : domain b ⊆ a) : sparsePrefixReplace a q b = b := by
  let := sparsePrefixReplace_isFunction (q := q) hb
  apply function_eq_of_pair_iff
  intro x y
  rw [kpair_mem_sparsePrefixReplace_iff]
  have hqa : ⟨x, y⟩ₖ ∈ q → x ∈ a := fun h ↦ hq x (mem_domain_of_kpair_mem h)
  tauto

theorem sparsePrefixReplace_append {a d p b τ : V}
    (hp : IsSparseFunctionOn d p) (hb : IsSparseFunctionOn a b) (had : a ⊆ d) :
    sparsePrefixReplace a (sparseAppend d p τ) b = sparseAppend d (sparsePrefixReplace a p b) τ := by
  classical
  let := hp.1
  let := hb.1
  let := sparseAppend_isFunction (τ := τ) hp.2.1
  let := sparsePrefixReplace_isFunction (q := sparseAppend d p τ) hb.2.1
  have hr := hp.prefixReplace hb had
  let := hr.1
  let := sparseAppend_isFunction (τ := τ) hr.2.1
  by_cases hτ : τ = ∅
  · simp only [hτ, sparseAppend_empty]
  · apply function_eq_of_pair_iff
    intro x y
    rw [kpair_mem_sparsePrefixReplace_iff, sparseAppend_nonempty hτ, sparseAppend_nonempty hτ]
    simp only [mem_insert, kpair_mem_sparsePrefixReplace_iff]
    have hda : d ∉ a := fun hd ↦ mem_irrefl d (had d hd)
    have hxy : ⟨x, y⟩ₖ = ⟨d, τ⟩ₖ → x ∉ a := by
      intro he
      have hx := congrArg kpair.π₁ he
      simp only [kpair.π₁_kpair] at hx
      exact hx ▸ hda
    tauto
theorem sparsePrefixReplace_restrict_smaller {a d q b : V} [IsFunction q] [IsFunction b]
    (hb : domain b ⊆ a) (hda : d ⊆ a) :
    (sparsePrefixReplace a q b) ↾ d = b ↾ d := by
  rw [← restrict_restrict_of_subset hda, sparsePrefixReplace_restrict hb]

theorem sparsePrefixReplace_domain (a q b : V) :
    domain (sparsePrefixReplace a q b) = domain b ∪ (domain q \ a) := by
  apply mem_ext
  intro x
  simp only [mem_domain_sparsePrefixReplace_iff, mem_union_iff, mem_sdiff_iff]
end ZFVP



