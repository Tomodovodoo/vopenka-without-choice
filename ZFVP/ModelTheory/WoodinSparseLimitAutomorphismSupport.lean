import ZFVP.ModelTheory.WoodinSparseActualLimitAutomorphisms

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sparse_domain_eq_of_restriction_domains {θ p q : V} [IsOrdinal θ]
    (hp : IsSparseFunctionOn θ p) (hq : IsSparseFunctionOn θ q)
    (hdom : ∀ i ∈ θ, domain (p ↾ (succ (woodinSourceIndex i))) =
      domain (q ↾ (succ (woodinSourceIndex i)))) : domain p = domain q := by
  let := hp.1
  let := hq.1
  apply mem_ext
  intro x
  constructor
  · intro hx
    have hxθ := hp.2.1 x hx
    have hxB : x ∈ succ (woodinSourceIndex x) := by
      simpa only [woodinSparseBounds_value hxθ] using woodinSparseBounds_self_mem hxθ
    have hh := hdom x hxθ
    rw [domain_restrict_eq, domain_restrict_eq] at hh
    exact (mem_inter_iff.mp (hh ▸ mem_inter_iff.mpr ⟨hx,hxB⟩)).1
  · intro hx
    have hxθ := hq.2.1 x hx
    have hxB : x ∈ succ (woodinSourceIndex x) := by
      simpa only [woodinSparseBounds_value hxθ] using woodinSparseBounds_self_mem hxθ
    have hh := hdom x hxθ
    rw [domain_restrict_eq, domain_restrict_eq] at hh
    exact (mem_inter_iff.mp (hh.symm ▸ mem_inter_iff.mpr ⟨hx,hxB⟩)).1

variable {Ω θ m : V} [IsOrdinal θ]
local notation "c" => woodinSparsePrefixCode θ
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
variable (hm : IsCoherentForcingAutomorphismFamily θ (woodinSparsePrefixCode θ) m)
variable (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
include hΩ hAC hθ hm h0 hlim

theorem woodinSparseActualInverseAutomorphism_domain
    (hdom : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, domain ((m ‘ i) ‘ p) = domain p)
    {q : V} (hq : q ∈ woodinSparseInverseBase θ c) :
    domain ((woodinSparseInverseAutomorphism θ c m) ‘ q) = domain q := by
  have hc := woodinSparsePrefixCode_valid hΩ hAC hθ
  have hg := function_value_mem (woodinSparseActualInverseAutomorphism hΩ hAC hθ hm h0 hlim).1 hq
  have hq' := (mem_woodinSparseInverseBase_iff hc).mp hq
  have hg' := (mem_woodinSparseInverseBase_iff hc).mp hg
  apply sparse_domain_eq_of_restriction_domains hg'.1 hq'.1
  intro i hi
  rw [woodinSparseActualInverseAutomorphism_restrict hΩ hAC hθ hm h0 hlim hq hi]
  exact hdom i hi _ (hq'.2 i hi)

theorem woodinSparseActualDirectAutomorphism_domain
    (hdom : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, domain ((m ‘ i) ‘ p) = domain p)
    {q : V} (hq : q ∈ woodinSparseDirectBase θ c) :
    domain ((woodinSparseDirectAutomorphism θ c m) ‘ q) = domain q := by
  have hc := woodinSparsePrefixCode_valid hΩ hAC hθ
  have hg := function_value_mem (woodinSparseActualDirectAutomorphism hΩ hAC hθ hm h0 hlim).1 hq
  have hq' := (mem_woodinSparseInverseBase_iff hc).mp (mem_woodinSparseDirectBase_iff.mp hq).1
  have hg' := (mem_woodinSparseInverseBase_iff hc).mp (mem_woodinSparseDirectBase_iff.mp hg).1
  apply sparse_domain_eq_of_restriction_domains hg'.1 hq'.1
  intro i hi
  rw [woodinSparseActualDirectAutomorphism_restrict hΩ hAC hθ hm h0 hlim hq hi]
  exact hdom i hi _ (hq'.2 i hi)

theorem woodinSparseActualInverseAutomorphism_top
    (htop : (m ‘ ∅) ‘ ∅ = ∅) :
    (∅ : V) ∈ woodinSparseInverseBase θ c ∧ (woodinSparseInverseAutomorphism θ c m) ‘ ∅ = ∅ := by
  have ht := (woodinSparsePrefixCode_valid hΩ hAC hθ).system.tops.top ∅ h0
  rw [woodinSparsePrefixCode_top hΩ hAC hθ h0] at ht
  have hh := woodinSparseActualInverseAutomorphism_section hΩ hAC hθ hm h0 hlim h0 ht.1
  exact ⟨hh.1, hh.2.trans htop⟩

theorem woodinSparseActualDirectAutomorphism_top
    (htop : (m ‘ ∅) ‘ ∅ = ∅) :
    (∅ : V) ∈ woodinSparseDirectBase θ c ∧ (woodinSparseDirectAutomorphism θ c m) ‘ ∅ = ∅ := by
  have ht := (woodinSparsePrefixCode_valid hΩ hAC hθ).system.tops.top ∅ h0
  rw [woodinSparsePrefixCode_top hΩ hAC hθ h0] at ht
  have hh := woodinSparseActualDirectAutomorphism_section hΩ hAC hθ hm h0 hlim h0 ht.1
  exact ⟨hh.1, hh.2.trans htop⟩

end ZFVP
