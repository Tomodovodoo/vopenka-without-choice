import ZFVP.ModelTheory.MaximalFilters
import ZFVP.ModelTheory.ConservativeExtension
import ZFVP.ModelTheory.RankPowersetExtension

/-! Enayat's Definition 5.16 (weakly Rubin models) and the second half of his Theorem 5.18 in
"Models of set theory: extensions and dead ends": every end extension of a weakly Rubin model to a
model of ZF is powerset preserving, hence a rank extension, hence conservative, and therefore, by
Enayat's Theorem 5.1, not proper.

Theorem 5.1 appears here as the named proposition `NoConservativeProperEndExtension`, so the
results of this file carry it as a visible hypothesis. It is proved in
`ZFVP.ModelTheory.NoConservativeEndExtension`, which imports this file and discharges the
hypothesis in `IsWeaklyRubin.isZFDeadEnd'`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

section Helpers

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Restriction is monotone in the restricting set. -/
theorem restrict_mono_right {f X Y : V} (h : X ⊆ Y) : f ↾ X ⊆ f ↾ Y := by
  intro z hz
  obtain ⟨hzf, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
  exact mem_restrict_iff.mpr ⟨hzf, x, h x hx, y, rfl⟩

/-- The restriction of a total function to a finite set is a finite partial function. -/
theorem restrict_mem_finitePartialFunctions {A B f X : V} (hf : f ∈ B ^ A)
    (hX : IsInternallyFinite X) : f ↾ X ∈ finitePartialFunctions A B := by
  have : IsFunction f := IsFunction.of_mem hf
  refine (mem_finitePartialFunctions _ _ _).mpr
    ⟨subset_trans (restrict_subset f X) (subset_prod_of_mem_function hf), inferInstance, ?_⟩
  rw [domain_restrict_eq]
  exact internallyFinite_subset hX (fun z hz ↦ (mem_inter_iff.mp hz).2)

/-- A finite partial function is itself internally finite. -/
theorem internallyFinite_of_mem_finitePartialFunctions {A B p : V}
    (hp : p ∈ finitePartialFunctions A B) : IsInternallyFinite p := by
  obtain ⟨-, hfun, hdom⟩ := (mem_finitePartialFunctions A B p).mp hp
  have := hfun
  exact internallyFinite_function hdom

end Helpers

/-- Enayat's Definition 5.16. -/
def IsWeaklyRubin (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  IsRatherClassless V ∧
    ∀ a : V, IsInternallyInfinite a →
      HasCofinalOmegaOneChain (fun x ↦ x ∈ finiteSubsets a) ∧
      ∀ F : V → Prop,
        IsMaximalInternalFilter (finitePartialFunctions a ((2 : ℕ) : V)) F →
        HasCofinalOmegaOneChain F → ∃ m : V, ∀ x : V, x ∈ m ↔ F x

section Main

variable {V W : Type*} [SetStructure V] [SetStructure W] [Nonempty V] [Nonempty W]
  [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The trace on `V` of the finite subsets of an internal function of `W` below `j a`. Along an
end extension this is exactly the pullback of the maximal filter of finite subsets of `χ`. -/
private def traceFilter (j : MembershipEndExtension V W) (a : V) (χ : W) : V → Prop :=
  fun p ↦ p ∈ finitePartialFunctions a ((2 : ℕ) : V) ∧ j p ⊆ χ

/-- Along an end extension, the finite subsets of `χ` are exactly the images of the members of
`traceFilter j a χ`, whenever `χ` is an internal function on `j a` with values in `2`. -/
private theorem traceFilter_map_iff (j : MembershipEndExtension V W) (a : V) {χ : W}
    (hχ : χ ∈ ((2 : ℕ) : W) ^ (j a)) (q : W) :
    (q ⊆ χ ∧ IsInternallyFinite q) ↔ ∃ p, traceFilter j a χ p ∧ q = j p := by
  have hjP : j (finitePartialFunctions a ((2 : ℕ) : V))
      = finitePartialFunctions (j a) ((2 : ℕ) : W) := j.map_finiteFunctionsTwo a
  constructor
  · rintro ⟨hqχ, hqfin⟩
    have hqP : q ∈ finitePartialFunctions (j a) ((2 : ℕ) : W) :=
      (isMaximalInternalFilter_finiteSubsets hχ).1.1 q ⟨hqχ, hqfin⟩
    rw [← hjP] at hqP
    obtain ⟨p, hp, rfl⟩ := j.endExtension _ _ hqP
    exact ⟨p, ⟨hp, hqχ⟩, rfl⟩
  · rintro ⟨p, ⟨hp, hpχ⟩, rfl⟩
    exact ⟨hpχ, j.map_internallyFinite (internallyFinite_of_mem_finitePartialFunctions hp)⟩

/-- The trace filter is a maximal filter of `Fin(a,2)`. -/
private theorem traceFilter_isMaximal (j : MembershipEndExtension V W) (a : V) {χ : W}
    (hχ : χ ∈ ((2 : ℕ) : W) ^ (j a)) :
    IsMaximalInternalFilter (finitePartialFunctions a ((2 : ℕ) : V)) (traceFilter j a χ) := by
  have hjP : j (finitePartialFunctions a ((2 : ℕ) : V))
      = finitePartialFunctions (j a) ((2 : ℕ) : W) := j.map_finiteFunctionsTwo a
  have hGmax : IsMaximalInternalFilter (finitePartialFunctions (j a) ((2 : ℕ) : W))
      (fun q ↦ q ⊆ χ ∧ IsInternallyFinite q) := isMaximalInternalFilter_finiteSubsets hχ
  have hkey := traceFilter_map_iff j a hχ
  refine ⟨⟨fun x hx ↦ hx.1, ?_⟩, ?_⟩
  · -- directedness, read off from directedness of the filter of finite subsets of `χ`
    intro x y hx hy
    obtain ⟨z, hz, hxz, hyz⟩ := hGmax.1.2 (j x) (j y)
      ((hkey (j x)).mpr ⟨x, hx, rfl⟩) ((hkey (j y)).mpr ⟨y, hy, rfl⟩)
    obtain ⟨p, hp, rfl⟩ := (hkey z).mp hz
    exact ⟨p, hp, (j.map_subset_iff x p).mp hxz, (j.map_subset_iff y p).mp hyz⟩
  · -- maximality, by pushing a candidate filter of `V` forward and using maximality in `W`
    intro F' hF' hle x hx
    have hF'' : IsInternalFilter (finitePartialFunctions (j a) ((2 : ℕ) : W))
        (fun q ↦ ∃ p, F' p ∧ q = j p) := by
      constructor
      · rintro q ⟨p, hp, rfl⟩
        rw [← hjP]
        exact (j.mem_iff _ _).mpr (hF'.1 p hp)
      · rintro q₁ q₂ ⟨p₁, hp₁, rfl⟩ ⟨p₂, hp₂, rfl⟩
        obtain ⟨p₃, hp₃, h₁, h₂⟩ := hF'.2 p₁ p₂ hp₁ hp₂
        exact ⟨j p₃, ⟨p₃, hp₃, rfl⟩, (j.map_subset_iff _ _).mpr h₁,
          (j.map_subset_iff _ _).mpr h₂⟩
    have hcontains : ∀ q : W, (q ⊆ χ ∧ IsInternallyFinite q) → ∃ p, F' p ∧ q = j p := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := (hkey q).mp hq
      exact ⟨p, hle p hp, rfl⟩
    have hjx := hGmax.2 (fun q ↦ ∃ p, F' p ∧ q = j p) hF'' hcontains (j x) ⟨x, hx, rfl⟩
    obtain ⟨p, hp, hxp⟩ := (hkey (j x)).mp hjx
    rwa [j.injective hxp]

/-- The trace filter has an increasing cofinal chain of order type `ω₁`, obtained by restricting
`χ` along a cofinal `ω₁`-chain of finite subsets of `a`. -/
private theorem traceFilter_hasChain (j : MembershipEndExtension V W) (a : V) {χ : W}
    (hχ : χ ∈ ((2 : ℕ) : W) ^ (j a))
    (hp : HasCofinalOmegaOneChain (fun x : V ↦ x ∈ finiteSubsets a)) :
    HasCofinalOmegaOneChain (traceFilter j a χ) := by
  classical
  have hjP : j (finitePartialFunctions a ((2 : ℕ) : V))
      = finitePartialFunctions (j a) ((2 : ℕ) : W) := j.map_finiteFunctionsTwo a
  have hdomχ : domain χ = j a := domain_eq_of_mem_function hχ
  obtain ⟨p, hp1, hp2, hp3⟩ := hp
  -- every restriction of `χ` to `j (p i)` is an image
  have hex : ∀ i, ∃ r : V, r ∈ finitePartialFunctions a ((2 : ℕ) : V)
      ∧ j r = χ ↾ (j (p i)) := by
    intro i
    obtain ⟨hsub, hfin⟩ := (mem_finiteSubsets_iff a (p i)).mp (hp1 i)
    have hmem : χ ↾ (j (p i)) ∈ finitePartialFunctions (j a) ((2 : ℕ) : W) :=
      restrict_mem_finitePartialFunctions hχ (j.map_internallyFinite hfin)
    rw [← hjP] at hmem
    obtain ⟨r, hr, hre⟩ := j.endExtension _ _ hmem
    exact ⟨r, hr, hre.symm⟩
  choose r hr1 hr2 using hex
  -- the domain of `j (r i)` is `j (p i)`
  have hdomr : ∀ i, domain (j (r i)) = j (p i) := by
    intro i
    have hsub : p i ⊆ a := ((mem_finiteSubsets_iff a (p i)).mp (hp1 i)).1
    rw [hr2 i, domain_restrict_eq, hdomχ]
    apply mem_ext
    intro z
    rw [mem_inter_iff]
    exact ⟨fun hz ↦ hz.2, fun hz ↦ ⟨(j.map_subset_iff (p i) a).mpr hsub z hz, hz⟩⟩
  refine ⟨r, fun i ↦ ⟨hr1 i, by rw [hr2 i]; exact restrict_subset _ _⟩, ?_, ?_⟩
  · intro i i' hlt
    obtain ⟨hle, hne⟩ := hp2 i i' hlt
    constructor
    · apply (j.map_subset_iff _ _).mp
      rw [hr2 i, hr2 i']
      exact restrict_mono_right ((j.map_subset_iff (p i) (p i')).mpr hle)
    · intro heq
      apply hne
      apply j.injective
      rw [← hdomr i, ← hdomr i', heq]
  · rintro q ⟨hq, hqχ⟩
    obtain ⟨-, hqfun, hqdom⟩ := (mem_finitePartialFunctions _ _ _).mp hq
    have := hqfun
    have hqmem : domain q ∈ finiteSubsets a :=
      (mem_finiteSubsets_iff a _).mpr ⟨finitePartialFunction_domain hq, hqdom⟩
    obtain ⟨i, hi⟩ := hp3 (domain q) hqmem
    refine ⟨i, (j.map_subset_iff q (r i)).mp ?_⟩
    rw [hr2 i]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := j.endExtension q z hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hw
    rw [j.map_kpair, kpair_mem_restrict_iff]
    refine ⟨?_, (j.mem_iff _ _).mpr (hi x (mem_domain_of_kpair_mem hw))⟩
    rw [← j.map_kpair]
    exact hqχ _ ((j.mem_iff _ _).mpr hw)

/-- Enayat's Theorem 5.18, first step: every end extension of a weakly Rubin model to a model of
ZF is powerset preserving. -/
theorem IsWeaklyRubin.isPowersetPreserving (h : IsWeaklyRubin V)
    (j : MembershipEndExtension V W) : j.IsPowersetPreserving := by
  classical
  intro a b hb
  by_cases hfin : IsInternallyFinite a
  · -- a finite old set has only finite subsets, and those are already old
    obtain ⟨c, -, hc⟩ := j.exists_eq_map_of_finite_subset hb
      (internallyFinite_subset (j.map_internallyFinite hfin) hb)
    exact ⟨c, hc.symm⟩
  · -- the infinite case: code `b` by its characteristic function and pull the code back
    have hχ : characteristicFunction (j a) b ∈ ((2 : ℕ) : W) ^ (j a) :=
      characteristicFunction_mem (j a) b
    set χ : W := characteristicFunction (j a) b with hχdef
    obtain ⟨hchain, hmax⟩ := h.2 a hfin
    obtain ⟨m, hm⟩ := hmax (traceFilter j a χ) (traceFilter_isMaximal j a hχ)
      (traceFilter_hasChain j a hχ hchain)
    -- `j m` is the set of finite subsets of `χ`, so its union is `χ`
    have hjm : j m = finiteSubsets χ := by
      apply mem_ext
      intro q
      rw [mem_finiteSubsets_iff, j.mem_map_iff, traceFilter_map_iff j a hχ q]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, (hm x).mp hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, (hm x).mpr hx, rfl⟩
    have hg : j (⋃ˢ m) = χ := by
      rw [j.map_sUnion, hjm, sUnion_finiteSubsets]
    -- read `b` off from the code
    refine ⟨{x ∈ a ; (⋃ˢ m) ‘ x = ((1 : ℕ) : V)}, ?_⟩
    have hsep : j {x ∈ a ; (⋃ˢ m) ‘ x = ((1 : ℕ) : V)}
        = {x ∈ j a ; χ ‘ x = ((1 : ℕ) : W)} := by
      apply j.map_separation a (fun x ↦ (⋃ˢ m) ‘ x = ((1 : ℕ) : V))
        (fun x ↦ χ ‘ x = ((1 : ℕ) : W)) (by definability) (by definability)
      intro x _
      constructor
      · intro hx
        rw [← hg, ← j.map_value_total, hx, j.map_numeral]
      · intro hx
        apply j.injective
        rw [j.map_value_total, j.map_numeral, hg, hx]
    rw [hsep]
    apply mem_ext
    intro y
    rw [mem_sep_iff]
    constructor
    · rintro ⟨hyA, hyv⟩
      exact (mem_iff_characteristicFunction hb hyA).mpr hyv
    · intro hy
      exact ⟨hb y hy, (mem_iff_characteristicFunction hb (hb y hy)).mp hy⟩

/-- Enayat's Theorem 5.18: every end extension of a weakly Rubin model to a model of ZF is a rank
extension. -/
theorem IsWeaklyRubin.isRankExtension (h : IsWeaklyRubin V)
    (j : MembershipEndExtension V W) : j.IsRankExtension :=
  (h.isPowersetPreserving j).isRankExtension

/-- Enayat's Theorem 5.18: every end extension of a weakly Rubin model to a model of ZF is
conservative. -/
theorem IsWeaklyRubin.isConservative (h : IsWeaklyRubin V)
    (j : MembershipEndExtension V W) : j.IsConservative :=
  h.1.isConservative_of_isPowersetPreserving (h.isPowersetPreserving j)

end Main

/-- Enayat's Theorem 5.1 as a proposition: no model of ZF has a conservative proper end extension
satisfying ZF. It is named here so that the results of this file can take it as a visible
hypothesis. The proof is `ZFVP.no_conservative_proper_end_extension` in
`ZFVP.ModelTheory.NoConservativeEndExtension`, which imports this file. -/
def NoConservativeProperEndExtension.{v} : Prop :=
  ∀ (M : Type v) [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (N : Type v) [SetStructure N] [Nonempty N] [N↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (j : MembershipEndExtension M N), j.IsConservative → ¬ j.IsProper

/-- Enayat's Theorem 5.18: with his Theorem 5.1 as a hypothesis, a weakly Rubin model has no
proper end extension to a model of ZF. The hypothesis is discharged in
`ZFVP.IsWeaklyRubin.isZFDeadEnd'`, in `ZFVP.ModelTheory.NoConservativeEndExtension`. -/
theorem IsWeaklyRubin.isZFDeadEnd {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (h51 : NoConservativeProperEndExtension.{u}) (h : IsWeaklyRubin V) : IsZFDeadEnd V := by
  intro W _ _ _ j
  exact h51 V W j (h.isConservative j)

end ZFVP
