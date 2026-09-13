import ZFVP.SetTheory.UltrapowerCollapse
import ZFVP.SetTheory.UltrapowerSeed
import ZFVP.SetTheory.NormalMeasureRegressive
import ZFVP.SetTheory.MeasureSmallClosure
import ZFVP.SetTheory.UltrapowerWitness

/-! # The ultrapower by a normal fine measure is closed under `lam`-indexed families

For a normal fine measure `U` on `P_κ(lam)` the target `ultraTarget P U A` of the collapse map is
closed under families indexed by `lam`: the range of a function from `lam` into the target is again
a member of the target. This is the closure property that lets the ultrapower see restrictions of
the embedding, and it uses fineness and normality but no form of Los's theorem.

The representing function is built pointwise. Choose for each `ξ ∈ lam` a function `r ‘ ξ` on the
index set whose collapse is `s ‘ ξ`, and let `F` send an index `x` to the set of values
`(r ‘ ξ) ‘ x` for `ξ ∈ x`. Since `x` is a subset of `lam` of size below `κ`, so is that set of
values, so `F ‘ x` is again a member of `A`. The a.e. members of `F` are then exactly the functions
a.e. equal to some `r ‘ ξ`: one direction is fineness, the other is normality applied to the choice
of a witness `ξ ∈ x` at each index.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The collapse target of a normal fine measure ultrapower is closed under `lam`-indexed
families: the range of a function from `lam` into the target belongs to the target. -/
theorem range_mem_ultraTarget (hAC : InternalChoice V) {P U A κ lam : V} [IsOrdinal κ]
    [IsTransitive A] (hU : IsNormalFineMeasure κ lam U) (hP : P = smallSubsetsBelow κ lam)
    (hcomp : IsOrdinalCompleteOn P κ U) (hω : (ω : V) ∈ κ) (hA : IsNonempty A)
    (hsmall : ∀ w, w ⊆ A → USmall κ w → w ∈ A)
    (h0 : (∅ : V) ∈ lam)
    {s : V} (hs : s ∈ (ultraTarget P U A) ^ lam) :
    range s ∈ ultraTarget P U A := by
  subst hP
  have hUf : IsSetUltrafilter (smallSubsetsBelow κ lam) U := hU.1
  have hwf : IsInternallyWellFounded (ultraMemRelation (smallSubsetsBelow κ lam) U A)
      (A ^ (smallSubsetsBelow κ lam)) :=
    ultraMemRelation_wellFounded hAC hUf hcomp hω
  have hcfun : IsFunction (ultraCollapse (smallSubsetsBelow κ lam) U A) :=
    ultraCollapse_isFunction hwf
  have hsfun : IsFunction s := IsFunction.of_mem hs
  have hsdom : domain s = lam := domain_eq_of_mem_function hs
  have hsublam : ∀ x ∈ smallSubsetsBelow κ lam, x ⊆ lam :=
    fun x hx ↦ ((mem_smallSubsetsBelow_iff _ _ _).mp hx).1
  have hxsmall : ∀ x ∈ smallSubsetsBelow κ lam, USmall κ x :=
    fun x hx ↦ ((mem_smallSubsetsBelow_iff _ _ _).mp hx).2
  -- ### Step 1: a representative for each value of `s`
  set W : V → V :=
    fun ξ ↦ {f ∈ A ^ (smallSubsetsBelow κ lam) ;
      (ultraCollapse (smallSubsetsBelow κ lam) U A) ‘ f = s ‘ ξ} with hWdef
  have hmemW : ∀ ξ f : V, f ∈ W ξ ↔ (f ∈ A ^ (smallSubsetsBelow κ lam) ∧
      (ultraCollapse (smallSubsetsBelow κ lam) U A) ‘ f = s ‘ ξ) := by
    intro ξ f
    simp only [hWdef, mem_sep_iff]
  have hW : ℒₛₑₜ-function₁[V] W := by
    have hd : ℒₛₑₜ-relation[V] (fun Y ξ ↦ ∀ f, f ∈ Y ↔
        f ∈ A ^ (smallSubsetsBelow κ lam) ∧
          (ultraCollapse (smallSubsetsBelow κ lam) U A) ‘ f = s ‘ ξ) := by definability
    apply Language.Definable.of_iff hd
    intro v
    change v 0 = W (v 1) ↔ _
    rw [mem_ext_iff]
    simp only [hWdef, mem_sep_iff]
  have hWne : ∀ ξ ∈ lam, IsNonempty (W ξ) := by
    intro ξ hξ
    obtain ⟨f, hf⟩ := mem_range_iff.mp (function_value_mem hs hξ)
    have hfd : f ∈ domain (ultraCollapse (smallSubsetsBelow κ lam) U A) :=
      mem_domain_of_kpair_mem hf
    rw [domain_ultraCollapse hwf] at hfd
    exact ⟨⟨f, (hmemW ξ f).mpr ⟨hfd, value_eq_of_kpair_mem hf⟩⟩⟩
  obtain ⟨r, hrfun, hrdom, hrval⟩ := choice_for_definable_family hAC lam W hW hWne
  have hrA : ∀ ξ ∈ lam, r ‘ ξ ∈ A ^ (smallSubsetsBelow κ lam) :=
    fun ξ hξ ↦ ((hmemW ξ _).mp (hrval ξ hξ)).1
  have hrc : ∀ ξ ∈ lam, (ultraCollapse (smallSubsetsBelow κ lam) U A) ‘ (r ‘ ξ) = s ‘ ξ :=
    fun ξ hξ ↦ ((hmemW ξ _).mp (hrval ξ hξ)).2
  clear_value W
  clear hWdef hWne hW hmemW
  -- ### Step 2: the representing function
  set G : V → V := fun x ↦ {z ∈ A ; ∃ ξ ∈ x, z = (r ‘ ξ) ‘ x} with hGdef
  have hmemG : ∀ x z : V, z ∈ G x ↔ (z ∈ A ∧ ∃ ξ ∈ x, z = (r ‘ ξ) ‘ x) := by
    intro x z
    simp only [hGdef, mem_sep_iff]
  have hG : ℒₛₑₜ-function₁[V] G := by
    have hd : ℒₛₑₜ-relation[V] (fun Y x ↦ ∀ z, z ∈ Y ↔
        z ∈ A ∧ ∃ ξ ∈ x, z = (r ‘ ξ) ‘ x) := by definability
    apply Language.Definable.of_iff hd
    intro v
    change v 0 = G (v 1) ↔ _
    rw [mem_ext_iff]
    simp only [hGdef, mem_sep_iff]
  clear_value G
  clear hGdef
  have hGsub : ∀ x, G x ⊆ A := fun x z hz ↦ ((hmemG x z).mp hz).1
  have hGval : ∀ x ∈ smallSubsetsBelow κ lam, ∀ ξ ∈ x, (r ‘ ξ) ‘ x ∈ G x := by
    intro x hx ξ hξ
    exact (hmemG x _).mpr ⟨function_value_mem (hrA ξ (hsublam x hx ξ hξ)) hx, ξ, hξ, rfl⟩
  have hGsmall : ∀ x ∈ smallSubsetsBelow κ lam, USmall κ (G x) := by
    intro x hx
    obtain ⟨μ, hμ, hle⟩ := hxsmall x hx
    refine ⟨μ, hμ, CardLE.trans ?_ hle⟩
    have hFx : ℒₛₑₜ-function₁[V] (fun ξ ↦ (r ‘ ξ) ‘ x) := by definability
    have hmem := definableGraph_mem_function_of_mapsTo x (G x) _ hFx (hGval x hx)
    refine cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC x) hmem ?_
    rw [range_definableGraph]
    apply mem_ext
    intro z
    rw [repl_spec, hmemG]
    constructor
    · rintro ⟨ξ, hξ, rfl⟩
      exact ⟨function_value_mem (hrA ξ (hsublam x hx ξ hξ)) hx, ξ, hξ, rfl⟩
    · rintro ⟨-, ξ, hξ, rfl⟩
      exact ⟨ξ, hξ, rfl⟩
  have hGA : ∀ x ∈ smallSubsetsBelow κ lam, G x ∈ A :=
    fun x hx ↦ hsmall (G x) (hGsub x) (hGsmall x hx)
  have hFmem : definableGraph (smallSubsetsBelow κ lam) G hG ∈ A ^ (smallSubsetsBelow κ lam) :=
    definableGraph_mem_function_of_mapsTo _ A G hG hGA
  have hFval : ∀ x ∈ smallSubsetsBelow κ lam,
      (definableGraph (smallSubsetsBelow κ lam) G hG) ‘ x = G x :=
    fun x hx ↦ value_definableGraph _ G hG hx
  set F : V := definableGraph (smallSubsetsBelow κ lam) G hG with hFdef
  clear_value F
  -- ### Step 3: the a.e. members of `F`
  have hkey : ∀ g, g ∈ A ^ (smallSubsetsBelow κ lam) →
      (UltraMem (smallSubsetsBelow κ lam) U g F ↔
        ∃ ξ ∈ lam, UltraEq (smallSubsetsBelow κ lam) U g (r ‘ ξ)) := by
    intro g hg
    constructor
    · intro hmem
      have hmem' : ultraMem (smallSubsetsBelow κ lam) g F ∈ U := hmem
      have hSP : ultraMem (smallSubsetsBelow κ lam) g F ⊆ smallSubsetsBelow κ lam :=
        ultraMem_subset _ g F
      set Wt : V → V := fun x ↦ {ξ ∈ lam ; ξ ∈ x ∧ g ‘ x = (r ‘ ξ) ‘ x} with hWtdef
      have hmemWt : ∀ x ξ : V, ξ ∈ Wt x ↔ (ξ ∈ lam ∧ ξ ∈ x ∧ g ‘ x = (r ‘ ξ) ‘ x) := by
        intro x ξ
        simp only [hWtdef, mem_sep_iff]
      have hWt : ℒₛₑₜ-function₁[V] Wt := by
        have hd : ℒₛₑₜ-relation[V] (fun Y x ↦ ∀ ξ, ξ ∈ Y ↔
            ξ ∈ lam ∧ (ξ ∈ x ∧ g ‘ x = (r ‘ ξ) ‘ x)) := by definability
        apply Language.Definable.of_iff hd
        intro v
        change v 0 = Wt (v 1) ↔ _
        rw [mem_ext_iff]
        simp only [hWtdef, mem_sep_iff]
      clear_value Wt
      clear hWtdef
      have hWtsub : ∀ x ∈ smallSubsetsBelow κ lam, Wt x ⊆ lam :=
        fun x _ ξ hξ ↦ ((hmemWt x ξ).mp hξ).1
      have hWtne : ∀ x ∈ ultraMem (smallSubsetsBelow κ lam) g F, IsNonempty (Wt x) := by
        intro x hx
        obtain ⟨hxP, hv⟩ := (mem_ultraMem_iff _ g F x).mp hx
        rw [hFval x hxP] at hv
        obtain ⟨-, ξ, hξx, hveq⟩ := (hmemG x _).mp hv
        exact ⟨⟨ξ, (hmemWt x ξ).mpr ⟨hsublam x hxP ξ hξx, hξx, hveq⟩⟩⟩
      obtain ⟨h, hhmem, hhval⟩ :=
        exists_ultraFunction_of_witnesses hAC hSP ⟨⟨∅, h0⟩⟩ Wt hWt hWtsub hWtne
      obtain ⟨ξ₀, hξ₀, hS0⟩ :=
        normalFineMeasure_regressive_constant hU h0 (IsFunction.of_mem hhmem)
          (domain_eq_of_mem_function hhmem)
          (hUf.upward hmem' (fun x hx ↦ (mem_sep_iff.mp hx).1)
            (fun x hx ↦ mem_sep_iff.mpr ⟨hSP x hx, ((hmemWt x _).mp (hhval x hx)).2.1⟩))
      refine ⟨ξ₀, hξ₀, ?_⟩
      show ultraAgree (smallSubsetsBelow κ lam) g (r ‘ ξ₀) ∈ U
      refine hUf.upward (hUf.inter hmem' hS0) (ultraAgree_subset _ g (r ‘ ξ₀)) ?_
      intro x hx
      rw [mem_inter_iff, mem_sep_iff] at hx
      obtain ⟨hxS, hxP, hhx⟩ := hx
      have hveq := ((hmemWt x _).mp (hhval x hxS)).2.2
      rw [hhx] at hveq
      exact (mem_ultraAgree_iff _ g (r ‘ ξ₀) x).mpr ⟨hxP, hveq⟩
    · rintro ⟨ξ, hξ, heq⟩
      have heq' : ultraAgree (smallSubsetsBelow κ lam) g (r ‘ ξ) ∈ U := heq
      show ultraMem (smallSubsetsBelow κ lam) g F ∈ U
      refine hUf.upward (hUf.inter (normalFineMeasure_fine hU hξ) heq')
        (ultraMem_subset _ g F) ?_
      intro x hx
      rw [mem_inter_iff, mem_sep_iff, mem_ultraAgree_iff] at hx
      obtain ⟨⟨hxP, hξx⟩, -, hvx⟩ := hx
      refine (mem_ultraMem_iff _ g F x).mpr ⟨hxP, ?_⟩
      rw [hFval x hxP]
      exact (hmemG x _).mpr ⟨function_value_mem hg hxP, ξ, hξx, hvx⟩
  -- ### Step 4: the collapse of `F` is the range of `s`
  have hcollapse : (ultraCollapse (smallSubsetsBelow κ lam) U A) ‘ F = range s := by
    apply mem_ext
    intro z
    rw [mem_ultraCollapse_value hwf hFmem]
    constructor
    · rintro ⟨g, hg, hgm, rfl⟩
      obtain ⟨ξ, hξ, heq⟩ := (hkey g hg).mp hgm
      have hgv : (ultraCollapse (smallSubsetsBelow κ lam) U A) ‘ g = s ‘ ξ := by
        rw [(ultraCollapse_eq_iff hAC hUf hcomp hω hA hg (hrA ξ hξ)).mpr heq]
        exact hrc ξ hξ
      rw [hgv]
      have hξd : ξ ∈ domain s := by rw [hsdom]; exact hξ
      exact mem_range_of_kpair_mem (kpair_value_mem hξd)
    · intro hz
      obtain ⟨ξ, hξp⟩ := mem_range_iff.mp hz
      have hξd : ξ ∈ domain s := mem_domain_of_kpair_mem hξp
      rw [hsdom] at hξd
      have hzv : s ‘ ξ = z := value_eq_of_kpair_mem hξp
      refine ⟨r ‘ ξ, hrA ξ hξd, (hkey _ (hrA ξ hξd)).mpr ⟨ξ, hξd, ultraEq_refl hUf⟩, ?_⟩
      rw [hrc ξ hξd]
      exact hzv
  rw [← hcollapse]
  exact ultraCollapse_value_mem hwf hFmem

/-- A nonempty subset of the collapse target that injects into `lam` is a member of the target.
An injection of `y` into `lam` is inverted into a function from `lam` onto `y`, with a fixed member
of `y` filling the indices outside the image, and the range form above applies to it. -/
theorem mem_ultraTarget_of_subset_cardLE (hAC : InternalChoice V) {P U A κ lam y : V}
    [IsOrdinal κ] [IsTransitive A] (hU : IsNormalFineMeasure κ lam U)
    (hP : P = smallSubsetsBelow κ lam) (hcomp : IsOrdinalCompleteOn P κ U) (hω : (ω : V) ∈ κ)
    (hA : IsNonempty A) (hsmall : ∀ w, w ⊆ A → USmall κ w → w ∈ A)
    (h0 : (∅ : V) ∈ lam)
    (hy : y ⊆ ultraTarget P U A) (hne : IsNonempty y) (hcard : y ≤# lam) :
    y ∈ ultraTarget P U A := by
  obtain ⟨e, he, hinj⟩ := hcard
  obtain ⟨d, hd⟩ := hne.nonempty
  set sval : V → V :=
    fun ξ ↦ ⋃ˢ {z ∈ y ; e ‘ z = ξ ∨ ((∀ w, w ∈ y → ¬ e ‘ w = ξ) ∧ z = d)} with hsvaldef
  -- at an index in the image of `e` the value is the unique preimage
  have hval_of : ∀ ξ z : V, z ∈ y → e ‘ z = ξ → sval ξ = z := by
    intro ξ z hz hez
    have hsingle : {z' ∈ y ; e ‘ z' = ξ ∨ ((∀ w, w ∈ y → ¬ e ‘ w = ξ) ∧ z' = d)} = ({z} : V) := by
      apply mem_ext
      intro u
      rw [mem_sep_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hu, h1 | h2⟩
        · exact injective_value_eq he hinj hu hz (by rw [h1, hez])
        · exact absurd hez (h2.1 z hz)
      · rintro rfl
        exact ⟨hz, Or.inl hez⟩
    simp only [hsvaldef]
    rw [hsingle, sUnion_singleton_eq]
  -- outside the image the value is the fixed member `d`
  have hval_off : ∀ ξ : V, (∀ w, w ∈ y → ¬ e ‘ w = ξ) → sval ξ = d := by
    intro ξ hoff
    have hsingle : {z' ∈ y ; e ‘ z' = ξ ∨ ((∀ w, w ∈ y → ¬ e ‘ w = ξ) ∧ z' = d)} = ({d} : V) := by
      apply mem_ext
      intro u
      rw [mem_sep_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hu, h1 | h2⟩
        · exact absurd h1 (hoff u hu)
        · exact h2.2
      · rintro rfl
        exact ⟨hd, Or.inr ⟨hoff, rfl⟩⟩
    simp only [hsvaldef]
    rw [hsingle, sUnion_singleton_eq]
  have hsvalmem : ∀ ξ : V, sval ξ ∈ y := by
    intro ξ
    by_cases hex : ∃ z, z ∈ y ∧ e ‘ z = ξ
    · obtain ⟨z, hz, hez⟩ := hex
      rw [hval_of ξ z hz hez]
      exact hz
    · rw [hval_off ξ (fun w hw hew ↦ hex ⟨w, hw, hew⟩)]
      exact hd
  have hsval : ℒₛₑₜ-function₁[V] sval := by
    have hd' : ℒₛₑₜ-relation[V] (fun Y ξ ↦ ∀ u, u ∈ Y ↔
        ∃ z, (z ∈ y ∧ (e ‘ z = ξ ∨ ((∀ w, w ∈ y → ¬ e ‘ w = ξ) ∧ z = d))) ∧ u ∈ z) := by
      definability
    apply Language.Definable.of_iff hd'
    intro v
    change v 0 = sval (v 1) ↔ _
    rw [mem_ext_iff]
    simp only [hsvaldef, mem_sUnion_iff, mem_sep_iff]
  clear_value sval
  have hsmem : definableGraph lam sval hsval ∈ (ultraTarget P U A) ^ lam :=
    definableGraph_mem_function_of_mapsTo _ _ _ hsval (fun ξ _ ↦ hy _ (hsvalmem ξ))
  have hrange : range (definableGraph lam sval hsval) = y := by
    rw [range_definableGraph]
    apply mem_ext
    intro z
    rw [repl_spec]
    constructor
    · rintro ⟨ξ, -, rfl⟩
      exact hsvalmem ξ
    · intro hz
      exact ⟨e ‘ z, function_value_mem he hz, (hval_of (e ‘ z) z hz rfl).symm⟩
  rw [← hrange]
  exact range_mem_ultraTarget hAC hU hP hcomp hω hA hsmall h0 hsmem

end ZFVP
