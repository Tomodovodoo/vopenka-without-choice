import ZFVP.SetTheory.LevyCollapseFull
import ZFVP.SetTheory.WoodinCollapseCones
import ZFVP.SetTheory.ForcingIsomorphism
import ZFVP.SetTheory.FiniteCofinality
import ZFVP.ModelTheory.LevyGaloisFactor

/-! Cone isomorphisms for the Levy collapse.

The cone of a condition `p` of `Coll(ω, <κ)` is `{r ; p ⊆ r}` with reverse inclusion. Renaming the
coordinates outside the finite domain of `p` identifies this cone with the whole collapse: on each
column `α` the free rows `ω \ {n ; (n, α) ∈ dom p}` form a cofinite subset of `ω`, and its
Mostowski collapse is an order isomorphism onto `ω`. This is the Levy analogue of
`woodinCollapse_cone_isomorphic` and needs no hypothesis on `κ`, because `ω` is regular outright.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Free rows of a condition -/

theorem levyCollapse_isFunction {κ p : V} (hp : p ∈ levyCollapse κ) : IsFunction p :=
  ((mem_finitePartialFunctions _ _ _).mp (levyCollapse_finitePartialFunction hp)).2.1


/-- The rows of the column `α` already used by `p`. -/
noncomputable def occupiedLevyRow (p α : V) : V := {n ∈ (ω : V) ; ⟨n, α⟩ₖ ∈ domain p}

instance occupiedLevyRow_definable : ℒₛₑₜ-function₂[V] occupiedLevyRow := by
  have h : ℒₛₑₜ-relation₃[V] (fun A p α ↦ ∀ n, n ∈ A ↔ n ∈ (ω : V) ∧ ⟨n, α⟩ₖ ∈ domain p) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [occupiedLevyRow]

theorem occupiedLevyRow_small {κ p : V} (hp : p ∈ levyCollapse κ) (α : V) :
    IsCardinalSmall (ω : V) (occupiedLevyRow p α) := by
  let F : V → V := fun n ↦ ⟨n, α⟩ₖ
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let f := definableGraph (occupiedLevyRow p α) F hF
  have hf : f ∈ (domain p) ^ (occupiedLevyRow p α) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun n hn ↦ (mem_sep_iff.mp hn).2)
  have hinj : Injective f := by
    intro n m z hn hm
    have ha := ((pair_mem_definableGraph_iff _ F hF n z).mp hn).2
    have hb := ((pair_mem_definableGraph_iff _ F hF m z).mp hm).2
    exact (kpair_iff.mp (ha.symm.trans hb)).1
  obtain ⟨N, hN, hdN, -⟩ :=
    ((mem_finitePartialFunctions _ _ _).mp (levyCollapse_finitePartialFunction hp)).2.2
  exact ⟨N, hN, (show occupiedLevyRow p α ≤# domain p from ⟨f, hf, hinj⟩).trans hdN⟩

/-- The rows of the column `α` still free for `p`. -/
noncomputable def freeLevyRow (p α : V) : V := (ω : V) \ occupiedLevyRow p α

instance freeLevyRow_definable : ℒₛₑₜ-function₂[V] freeLevyRow := by
  unfold freeLevyRow
  definability

theorem mem_freeLevyRow (p α n : V) :
    n ∈ freeLevyRow p α ↔ n ∈ (ω : V) ∧ ⟨n, α⟩ₖ ∉ domain p := by
  simp [freeLevyRow, occupiedLevyRow]
  tauto

/-- The increasing enumeration of the free rows of the column `α`. -/
noncomputable def levyRowMap (p α : V) : V :=
  mostowskiMap (membershipRelation (freeLevyRow p α)) (freeLevyRow p α)

instance levyRowMap_definable : ℒₛₑₜ-function₂[V] levyRowMap := by
  unfold levyRowMap
  definability

theorem levyRowMap_bijection {κ p : V} (hp : p ∈ levyCollapse κ) (α : V) :
    levyRowMap p α ∈ (ω : V) ^ (freeLevyRow p α) ∧
      Injective (levyRowMap p α) ∧ range (levyRowMap p α) = (ω : V) := by
  have hsub : freeLevyRow p α ⊆ (ω : V) := fun n hn ↦ ((mem_freeLevyRow _ _ _).mp hn).1
  have hw := ordinalSubset_membership_wellOrder hsub
  have hc := mostowskiMap_isTransitiveCollapse hw.2.1 (internalWellOrder_extensional hw)
  have he := smallComplement_orderType omega_regular (occupiedLevyRow_small hp α)
  change range (levyRowMap p α) = (ω : V) at he
  have hf : levyRowMap p α ∈ (ω : V) ^ (freeLevyRow p α) := by
    have hfunc := hc.2.1
    change levyRowMap p α ∈ (range (levyRowMap p α)) ^ (freeLevyRow p α) at hfunc
    rwa [he] at hfunc
  refine ⟨hf, ?_, he⟩
  let := IsFunction.of_mem hf
  intro n m z hn hm
  exact hc.2.2.2.1 n ((mem_of_mem_functions hf hn).1) m ((mem_of_mem_functions hf hm).1)
    ((value_eq_of_kpair_mem hn).trans (value_eq_of_kpair_mem hm).symm)

/-! ### The coordinate renaming -/

/-- The coordinates of `ω × κ` still free for `p`. -/
noncomputable def freeLevyCoordinates (κ p : V) : V := ((ω : V) ×ˢ κ) \ domain p

instance freeLevyCoordinates_definable : ℒₛₑₜ-function₂[V] freeLevyCoordinates := by
  unfold freeLevyCoordinates
  definability

theorem mem_freeLevyCoordinates (κ p z : V) :
    z ∈ freeLevyCoordinates κ p ↔ z ∈ (ω : V) ×ˢ κ ∧ z ∉ domain p := by
  simp [freeLevyCoordinates]

theorem kpair_mem_freeLevyCoordinates (κ p n α : V) :
    ⟨n, α⟩ₖ ∈ freeLevyCoordinates κ p ↔ n ∈ freeLevyRow p α ∧ α ∈ κ := by
  rw [mem_freeLevyCoordinates, mem_freeLevyRow, kpair_mem_iff]
  tauto

noncomputable def levyCoordinateValue (p z : V) : V :=
  ⟨(levyRowMap p (kpair.π₂ z)) ‘ (kpair.π₁ z), kpair.π₂ z⟩ₖ

instance levyCoordinateValue_definable : ℒₛₑₜ-function₂[V] levyCoordinateValue := by
  unfold levyCoordinateValue
  definability

/-- The bijection of the free coordinates of `p` with all of `ω × κ`, column by column. -/
noncomputable def levyCoordinateMap (κ p : V) : V :=
  definableGraph (freeLevyCoordinates κ p) (levyCoordinateValue p) (by definability)

instance levyCoordinateMap_definable : ℒₛₑₜ-function₂[V] levyCoordinateMap := by
  have h : ℒₛₑₜ-relation₃[V] (fun f κ p ↦ ∀ z, z ∈ f ↔
      ∃ x ∈ freeLevyCoordinates κ p, z = ⟨x, levyCoordinateValue p x⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [levyCoordinateMap, mem_definableGraph_iff]
  rfl

theorem levyCoordinateMap_value {κ p z : V} (hz : z ∈ freeLevyCoordinates κ p) :
    (levyCoordinateMap κ p) ‘ z = levyCoordinateValue p z := value_definableGraph _ _ _ hz

theorem levyCoordinateMap_function {κ p : V} (hp : p ∈ levyCollapse κ) :
    levyCoordinateMap κ p ∈ ((ω : V) ×ˢ κ) ^ (freeLevyCoordinates κ p) := by
  apply definableGraph_mem_function_of_mapsTo
  intro z hz
  obtain ⟨n, -, α, -, rfl⟩ := mem_prod_iff.mp ((mem_freeLevyCoordinates _ _ _).mp hz).1
  obtain ⟨hn, hα⟩ := (kpair_mem_freeLevyCoordinates _ _ _ _).mp hz
  simpa only [levyCoordinateValue, kpair.π₁_kpair, kpair.π₂_kpair] using
    kpair_mem_iff.mpr ⟨function_value_mem (levyRowMap_bijection hp α).1 hn, hα⟩

theorem levyCoordinateMap_injective {κ p : V} (hp : p ∈ levyCollapse κ) :
    Injective (levyCoordinateMap κ p) := by
  intro z w t hz hw
  obtain ⟨hzD, htz⟩ := (pair_mem_definableGraph_iff _ _ (by definability) z t).mp hz
  obtain ⟨hwD, htw⟩ := (pair_mem_definableGraph_iff _ _ (by definability) w t).mp hw
  obtain ⟨n, -, α, -, rfl⟩ := mem_prod_iff.mp ((mem_freeLevyCoordinates _ _ _).mp hzD).1
  obtain ⟨m, -, β, -, rfl⟩ := mem_prod_iff.mp ((mem_freeLevyCoordinates _ _ _).mp hwD).1
  have he : (levyRowMap p α) ‘ n = (levyRowMap p β) ‘ m ∧ α = β := by
    simpa only [levyCoordinateValue, kpair.π₁_kpair, kpair.π₂_kpair, kpair_iff] using
      htz.symm.trans htw
  obtain ⟨hval, rfl⟩ := he
  have hm := levyRowMap_bijection hp α
  have ha := ((kpair_mem_freeLevyCoordinates _ _ _ _).mp hzD).1
  have hb := ((kpair_mem_freeLevyCoordinates _ _ _ _).mp hwD).1
  exact kpair_iff.mpr ⟨injective_value_eq hm.1 hm.2.1 ha hb hval, rfl⟩

theorem levyCoordinateMap_range {κ p : V} (hp : p ∈ levyCollapse κ) :
    range (levyCoordinateMap κ p) = (ω : V) ×ˢ κ := by
  have hf := levyCoordinateMap_function hp
  let := IsFunction.of_mem hf
  apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
  intro z hz
  obtain ⟨n, hn, α, hα, rfl⟩ := mem_prod_iff.mp hz
  have hm := levyRowMap_bijection hp α
  let := IsFunction.of_mem hm.1
  obtain ⟨m, hmn⟩ := mem_range_iff.mp (hm.2.2.symm ▸ hn)
  have hmD := (mem_of_mem_functions hm.1 hmn).1
  have hbD := (kpair_mem_freeLevyCoordinates _ _ _ _).mpr ⟨hmD, hα⟩
  have hv : (levyCoordinateMap κ p) ‘ ⟨m, α⟩ₖ = ⟨n, α⟩ₖ := by
    rw [levyCoordinateMap_value hbD]
    simp only [levyCoordinateValue, kpair.π₁_kpair, kpair.π₂_kpair, value_eq_of_kpair_mem hmn]
  exact hv ▸ value_mem_range hf hbD

theorem levyCoordinateMap_preserves_column {κ p z : V} (hz : z ∈ freeLevyCoordinates κ p) :
    kpair.π₂ ((levyCoordinateMap κ p) ‘ z) = kpair.π₂ z := by
  rw [levyCoordinateMap_value hz]
  simp [levyCoordinateValue]

/-! ### Renaming conditions -/

/-- Reindexing a condition along an injection preserving columns gives a condition. -/
theorem levyCollapse_permuted {κ D π p : V} (hp : p ∈ levyCollapse κ)
    (hπ : π ∈ ((ω : V) ×ˢ κ) ^ D) (hinj : Injective π) (hdom : domain p ⊆ D)
    (hcol : ∀ z ∈ D, kpair.π₂ (π ‘ z) = kpair.π₂ z) :
    permutedGraph π p ∈ levyCollapse κ := by
  have hfp := levyCollapse_finitePartialFunction hp
  obtain ⟨hsub, hfun, hfin⟩ := (mem_finitePartialFunctions _ _ _).mp hfp
  let := hfun
  refine (mem_levyCollapse_iff κ _).mpr ⟨(mem_finitePartialFunctions _ _ _).mpr
    ⟨?_, permutedGraph_function_of_injection hπ hinj hdom,
      internallyFinite_of_cardLE hfin (permutedGraph_domain_cardLE hπ hinj hdom)⟩, ?_⟩
  · intro z hz
    obtain ⟨u, hu, rfl⟩ := (mem_permutedGraph π p z).mp hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hu
    have hy := (kpair_mem_iff.mp (hsub _ hu)).2
    simpa only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair] using
      kpair_mem_iff.mpr ⟨function_value_mem hπ (hdom x (mem_domain_of_kpair_mem hu)), hy⟩
  · intro n α β hx
    obtain ⟨u, hux, he⟩ := (pair_mem_permutedGraph π p _ β).mp hx
    have hud : u ∈ (ω : V) ×ˢ κ :=
      finitePartialFunction_domain hfp _ (mem_domain_of_kpair_mem hux)
    obtain ⟨m, -, ξ, -, rfl⟩ := mem_prod_iff.mp hud
    have hr := hcol _ (hdom _ (mem_domain_of_kpair_mem hux))
    rw [← he] at hr
    simp only [kpair.π₂_kpair] at hr
    exact hr.symm ▸ levyCollapse_value hp hux

/-! ### The cone of a condition -/

noncomputable def levyCollapseCone (κ p : V) : V := {r ∈ levyCollapse κ ; p ⊆ r}

theorem mem_levyCollapseCone (κ p r : V) :
    r ∈ levyCollapseCone κ p ↔ r ∈ levyCollapse κ ∧ p ⊆ r := mem_sep_iff

instance levyCollapseCone_definable : ℒₛₑₜ-function₂[V] levyCollapseCone := by
  have h : ℒₛₑₜ-relation₃[V] (fun C κ p ↦ ∀ r, r ∈ C ↔ r ∈ levyCollapse κ ∧ p ⊆ r) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_levyCollapseCone]
  rfl

theorem levyCollapseCone_poset (κ p : V) :
    IsForcingPoset (levyCollapseCone κ p) (reverseInclusionOrder (levyCollapseCone κ p)) :=
  reverseInclusionOrder_poset _

/-- The cone of the empty condition is the whole collapse. -/
theorem levyCollapseCone_empty (κ : V) : levyCollapseCone κ ∅ = levyCollapse κ := by
  apply mem_ext
  intro r
  rw [mem_levyCollapseCone]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, empty_subset r⟩⟩

/-! ### Encoding and decoding -/

noncomputable def levyConeEncode (κ p q : V) : V :=
  p ∪ permutedGraph (converseGraph (levyCoordinateMap κ p)) q

noncomputable def levyConeDecode (κ p r : V) : V :=
  permutedGraph (levyCoordinateMap κ p) (r ↾ (freeLevyCoordinates κ p))

instance levyConeEncode_definable : ℒₛₑₜ-function₃[V] levyConeEncode := by
  unfold levyConeEncode
  definability

instance levyConeDecode_definable : ℒₛₑₜ-function₃[V] levyConeDecode := by
  unfold levyConeDecode
  definability

theorem inverseLevyCoordinateMap_function {κ p : V} (hp : p ∈ levyCollapse κ) :
    converseGraph (levyCoordinateMap κ p) ∈ (freeLevyCoordinates κ p) ^ ((ω : V) ×ˢ κ) := by
  have h := converseGraph_mem_function (levyCoordinateMap_function hp)
    (levyCoordinateMap_injective hp)
  rwa [levyCoordinateMap_range hp] at h

theorem inverseLevyCoordinateMap_preserves_column {κ p z : V} (hp : p ∈ levyCollapse κ)
    (hz : z ∈ (ω : V) ×ˢ κ) :
    kpair.π₂ ((converseGraph (levyCoordinateMap κ p)) ‘ z) = kpair.π₂ z := by
  have hi := inverseLevyCoordinateMap_function hp
  have hr := levyCoordinateMap_preserves_column (function_value_mem hi hz)
  rw [value_converseGraph_value (levyCoordinateMap_function hp) (levyCoordinateMap_injective hp)
    ((levyCoordinateMap_range hp).symm ▸ hz)] at hr
  exact hr.symm

theorem levyCollapse_inverse_permuted {κ p q : V} (hp : p ∈ levyCollapse κ)
    (hq : q ∈ levyCollapse κ) :
    permutedGraph (converseGraph (levyCoordinateMap κ p)) q ∈ levyCollapse κ := by
  have hi := inverseLevyCoordinateMap_function hp
  have hisub : freeLevyCoordinates κ p ⊆ (ω : V) ×ˢ κ :=
    fun z hz ↦ ((mem_freeLevyCoordinates _ _ _).mp hz).1
  have hf := mem_function_of_mem_function_of_subset hi hisub
  let := IsFunction.of_mem (levyCoordinateMap_function hp)
  exact levyCollapse_permuted hq hf (converseGraph_injective _)
    (finitePartialFunction_domain (levyCollapse_finitePartialFunction hq))
    (fun z hz ↦ inverseLevyCoordinateMap_preserves_column hp hz)

theorem levyCollapse_inverse_permuted_domain {κ p q : V} (hp : p ∈ levyCollapse κ)
    (hq : q ∈ levyCollapse κ) :
    domain (permutedGraph (converseGraph (levyCoordinateMap κ p)) q) ⊆ freeLevyCoordinates κ p := by
  let := levyCollapse_isFunction hq
  intro z hz
  obtain ⟨u, hu, rfl⟩ := permutedGraph_domain_maps hz
  exact function_value_mem (inverseLevyCoordinateMap_function hp)
    (finitePartialFunction_domain (levyCollapse_finitePartialFunction hq) _ hu)

theorem levyConeEncode_condition {κ p q : V} (hp : p ∈ levyCollapse κ) (hq : q ∈ levyCollapse κ) :
    levyConeEncode κ p q ∈ levyCollapse κ := by
  apply levyCollapse_union hp (levyCollapse_inverse_permuted hp hq)
  intro x y _z hxy hxz
  have hfree := levyCollapse_inverse_permuted_domain hp hq x (mem_domain_of_kpair_mem hxz)
  exact False.elim (((mem_freeLevyCoordinates _ _ _).mp hfree).2 (mem_domain_of_kpair_mem hxy))

theorem levyConeEncode_extends (κ p q : V) : p ⊆ levyConeEncode κ p q :=
  fun z hz ↦ mem_union_iff.mpr (Or.inl hz)

theorem levyConeDecode_condition {κ p r : V} (hp : p ∈ levyCollapse κ) (hr : r ∈ levyCollapse κ) :
    levyConeDecode κ p r ∈ levyCollapse κ := by
  have hres := levyCollapse_subset hr (show r ↾ (freeLevyCoordinates κ p) ⊆ r from
    fun z hz ↦ (mem_restrict_iff.mp hz).1)
  have hdom : domain (r ↾ (freeLevyCoordinates κ p)) ⊆ freeLevyCoordinates κ p := by
    intro x hx
    obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
    exact (kpair_mem_restrict_iff.mp hxy).2
  exact levyCollapse_permuted hres (levyCoordinateMap_function hp)
    (levyCoordinateMap_injective hp) hdom (fun z hz ↦ levyCoordinateMap_preserves_column hz)

theorem levyConeDecode_encode {κ p q : V} (hp : p ∈ levyCollapse κ) (hq : q ∈ levyCollapse κ) :
    levyConeDecode κ p (levyConeEncode κ p q) = q := by
  let := levyCollapse_isFunction hp
  let := levyCollapse_isFunction hq
  let := levyCollapse_isFunction (levyCollapse_inverse_permuted hp hq)
  unfold levyConeDecode levyConeEncode
  rw [function_restrict_union_disjoint (p := p) (by
    intro x hx hfree
    exact ((mem_freeLevyCoordinates _ _ _).mp hfree).2 hx)
    (levyCollapse_inverse_permuted_domain hp hq)]
  apply permutedGraph_inverse_of_values
  intro x hx
  exact value_converseGraph_value (levyCoordinateMap_function hp) (levyCoordinateMap_injective hp)
    ((levyCoordinateMap_range hp).symm ▸
      finitePartialFunction_domain (levyCollapse_finitePartialFunction hq) x hx)

theorem levyConeEncode_decode {κ p r : V} (hp : p ∈ levyCollapse κ) (hr : r ∈ levyCollapse κ)
    (hpr : p ⊆ r) : levyConeEncode κ p (levyConeDecode κ p r) = r := by
  let := levyCollapse_isFunction hp
  let := levyCollapse_isFunction hr
  have hv : ∀ x ∈ domain (r ↾ (freeLevyCoordinates κ p)),
      (converseGraph (levyCoordinateMap κ p)) ‘ ((levyCoordinateMap κ p) ‘ x) = x := by
    intro x hx
    obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
    exact converseGraph_value_value (levyCoordinateMap_function hp)
      (levyCoordinateMap_injective hp) (kpair_mem_restrict_iff.mp hxy).2
  unfold levyConeEncode levyConeDecode
  rw [permutedGraph_inverse_of_values hv]
  exact function_union_restrict_complement hpr
    (finitePartialFunction_domain (levyCollapse_finitePartialFunction hr))

theorem levyConeEncode_mono {κ p q r : V} (hqr : q ⊆ r) :
    levyConeEncode κ p q ⊆ levyConeEncode κ p r := by
  intro z hz
  rcases mem_union_iff.mp hz with hz | hz
  · exact mem_union_iff.mpr (Or.inl hz)
  · exact mem_union_iff.mpr (Or.inr (permutedGraph_mono hqr _ hz))

theorem levyConeDecode_mono {κ p q r : V} (hqr : q ⊆ r) :
    levyConeDecode κ p q ⊆ levyConeDecode κ p r := by
  apply permutedGraph_mono
  intro z hz
  obtain ⟨hz, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
  exact kpair_mem_restrict_iff.mpr ⟨hqr _ hz, hx⟩

/-! ### The cone isomorphism -/

/-- Any two cones of the Levy collapse are forcing isomorphic. -/
theorem levyCollapse_cone_isomorphic_cone {κ p q : V} (hp : p ∈ levyCollapse κ)
    (hq : q ∈ levyCollapse κ) :
    ∃ f, IsForcingIsomorphism (levyCollapseCone κ p) (reverseInclusionOrder (levyCollapseCone κ p))
      (levyCollapseCone κ q) (reverseInclusionOrder (levyCollapseCone κ q)) f := by
  let F : V → V := fun r ↦ levyConeEncode κ q (levyConeDecode κ p r)
  let G : V → V := fun r ↦ levyConeEncode κ p (levyConeDecode κ q r)
  have hF : ℒₛₑₜ-function₁ F := by
    unfold F levyConeEncode levyConeDecode
    definability
  have hFP : ∀ r ∈ levyCollapseCone κ p, F r ∈ levyCollapseCone κ q := by
    intro r hr
    exact (mem_levyCollapseCone _ _ _).mpr
      ⟨levyConeEncode_condition hq (levyConeDecode_condition hp ((mem_levyCollapseCone _ _ _).mp hr).1),
        levyConeEncode_extends _ _ _⟩
  have hGQ : ∀ r ∈ levyCollapseCone κ q, G r ∈ levyCollapseCone κ p := by
    intro r hr
    exact (mem_levyCollapseCone _ _ _).mpr
      ⟨levyConeEncode_condition hp (levyConeDecode_condition hq ((mem_levyCollapseCone _ _ _).mp hr).1),
        levyConeEncode_extends _ _ _⟩
  have hGF : ∀ r ∈ levyCollapseCone κ p, G (F r) = r := by
    intro r hr
    have hr' := (mem_levyCollapseCone _ _ _).mp hr
    dsimp [F, G]
    rw [levyConeDecode_encode hq (levyConeDecode_condition hp hr'.1),
      levyConeEncode_decode hp hr'.1 hr'.2]
  have hFG : ∀ r ∈ levyCollapseCone κ q, F (G r) = r := by
    intro r hr
    have hr' := (mem_levyCollapseCone _ _ _).mp hr
    dsimp [F, G]
    rw [levyConeDecode_encode hp (levyConeDecode_condition hq hr'.1),
      levyConeEncode_decode hq hr'.1 hr'.2]
  exact ⟨definableGraph _ F hF, reverseInclusion_isomorphism_of_inverse F G hF hFP hGQ hGF hFG
    (fun _ _ _ _ h ↦ levyConeEncode_mono (levyConeDecode_mono h))
    (fun _ _ _ _ h ↦ levyConeEncode_mono (levyConeDecode_mono h))⟩

/-- The cone of any condition of the Levy collapse is forcing isomorphic to the whole collapse. -/
theorem levyCollapse_cone_isomorphic {κ p : V} (hp : p ∈ levyCollapse κ) :
    ∃ f, IsForcingIsomorphism (levyCollapseCone κ p) (reverseInclusionOrder (levyCollapseCone κ p))
      (levyCollapse κ) (levyOrder κ) f := by
  obtain ⟨f, hf⟩ := levyCollapse_cone_isomorphic_cone hp (empty_mem_levyCollapse κ)
  rw [levyCollapseCone_empty] at hf
  exact ⟨f, hf⟩


/-! ### A criterion for forcing isomorphisms -/

/-- A definable map with a two-sided inverse that transports the order is a forcing
isomorphism. -/
theorem isForcingIsomorphism_of_inverse {P R Q S : V} (F G : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hFP : ∀ p ∈ P, F p ∈ Q) (hGQ : ∀ q ∈ Q, G q ∈ P)
    (hGF : ∀ p ∈ P, G (F p) = p) (hFG : ∀ q ∈ Q, F (G q) = q)
    (hord : ∀ p ∈ P, ∀ q ∈ P, ⟨p, q⟩ₖ ∈ R ↔ ⟨F p, F q⟩ₖ ∈ S) :
    IsForcingIsomorphism P R Q S (definableGraph P F hF) := by
  let f := definableGraph P F hF
  have hf : f ∈ Q ^ P := definableGraph_mem_function_of_mapsTo _ _ _ _ hFP
  let := IsFunction.of_mem hf
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro p q z hp hq
    obtain ⟨hpP, hzp⟩ := (pair_mem_definableGraph_iff _ F hF p z).mp hp
    obtain ⟨hqP, hzq⟩ := (pair_mem_definableGraph_iff _ F hF q z).mp hq
    have he := congrArg G (hzp.symm.trans hzq)
    simpa only [hGF p hpP, hGF q hqP] using he
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro q hq
    have hv : f ‘ (G q) = q := (value_definableGraph _ _ _ (hGQ q hq)).trans (hFG q hq)
    exact hv ▸ value_mem_range hf (hGQ q hq)
  · intro p hp q hq
    rw [value_definableGraph _ _ _ hp, value_definableGraph _ _ _ hq]
    exact hord p hp q hq

/-- Composites of forcing isomorphisms are forcing isomorphisms. -/
theorem isForcingIsomorphism_compose {P R Q S T U f g : V}
    (hf : IsForcingIsomorphism P R Q S f) (hg : IsForcingIsomorphism Q S T U g) :
    IsForcingIsomorphism P R T U (compose f g) := by
  have : IsFunction f := IsFunction.of_mem hf.1
  have : IsFunction g := IsFunction.of_mem hg.1
  have hc := compose_function hf.1 hg.1
  have : IsFunction (compose f g) := IsFunction.of_mem hc
  refine ⟨hc, compose_injective hf.2.1 hg.2.1, ?_, ?_⟩
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hc)
    intro t ht
    obtain ⟨q, hqg⟩ := mem_range_iff.mp (hg.2.2.1.symm ▸ ht)
    have hq : q ∈ Q := (mem_of_mem_functions hg.1 hqg).1
    obtain ⟨p, hpf⟩ := mem_range_iff.mp (hf.2.2.1.symm ▸ hq)
    have hp : p ∈ P := (mem_of_mem_functions hf.1 hpf).1
    have he : (compose f g) ‘ p = t := by
      rw [value_compose_of_mem_function hf.1 hg.1 hp, value_eq_of_kpair_mem hpf,
        value_eq_of_kpair_mem hqg]
    exact he ▸ value_mem_range hc hp
  · intro p hp q hq
    rw [value_compose_of_mem_function hf.1 hg.1 hp, value_compose_of_mem_function hf.1 hg.1 hq]
    exact (hf.2.2.2 p hp q hq).trans
      (hg.2.2.2 _ (function_value_mem hf.1 hp) _ (function_value_mem hf.1 hq))

/-- The inverse of a forcing isomorphism. -/
theorem isForcingIsomorphism_inverse {P R Q S f : V} (hf : IsForcingIsomorphism P R Q S f) :
    IsForcingIsomorphism Q S P R (converseGraph f) := by
  have : IsFunction f := IsFunction.of_mem hf.1
  have hi : converseGraph f ∈ P ^ Q := by
    simpa only [hf.2.2.1] using converseGraph_mem_function hf.1 hf.2.1
  refine ⟨hi, converseGraph_injective f, ?_, ?_⟩
  · rw [range_converseGraph, domain_eq_of_mem_function hf.1]
  · intro a ha b hb
    have haf : a ∈ range f := hf.2.2.1.symm ▸ ha
    have hbf : b ∈ range f := hf.2.2.1.symm ▸ hb
    simpa only [value_converseGraph_value hf.1 hf.2.1 haf,
      value_converseGraph_value hf.1 hf.2.1 hbf] using
      (hf.2.2.2 _ (function_value_mem hi ha) _ (function_value_mem hi hb)).symm

theorem isForcingIsomorphism_surjective {P R Q S f : V} (hf : IsForcingIsomorphism P R Q S f) :
    ∀ b ∈ Q, ∃ a ∈ P, f ‘ a = b := by
  have : IsFunction f := IsFunction.of_mem hf.1
  intro b hb
  obtain ⟨a, ha⟩ := mem_range_iff.mp (hf.2.2.1.symm ▸ hb)
  exact ⟨a, (mem_of_mem_functions hf.1 ha).1, value_eq_of_kpair_mem ha⟩

theorem isForcingIsomorphism_compose_inverse {P R Q S f : V}
    (hf : IsForcingIsomorphism P R Q S f) : compose f (converseGraph f) = identity P := by
  have hi := (isForcingIsomorphism_inverse hf).1
  have : IsFunction (compose f (converseGraph f)) := IsFunction.of_mem (compose_function hf.1 hi)
  have : IsFunction (identity P : V) := IsFunction.of_mem (identity_mem_function P)
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function (compose_function hf.1 hi),
      domain_eq_of_mem_function (identity_mem_function P)]
  · intro a ha
    have haP : a ∈ P := domain_eq_of_mem_function (compose_function hf.1 hi) ▸ ha
    rw [value_compose_of_mem_function hf.1 hi haP,
      converseGraph_value_value hf.1 hf.2.1 haP, identity_value haP]

/-! ### Transporting the Boolean completion along an isomorphism -/

section Transfer

variable {P R Q S f : V}

theorem imageAction_subset_of_isomorphism (hf : IsForcingIsomorphism P R Q S f) {A : V}
    (hA : A ⊆ P) : imageAction f A ⊆ Q := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (mem_imageAction_iff _ _ _).mp hx
  exact function_value_mem hf.1 (hA a ha)

theorem value_mem_imageAction_iff_of_isomorphism (hf : IsForcingIsomorphism P R Q S f) {A x : V}
    (hA : A ⊆ P) (hx : x ∈ P) : f ‘ x ∈ imageAction f A ↔ x ∈ A := by
  constructor
  · intro h
    obtain ⟨a, ha, he⟩ := (mem_imageAction_iff _ _ _).mp h
    exact (injective_value_eq hf.1 hf.2.1 hx (hA a ha) he) ▸ ha
  · intro h
    exact (mem_imageAction_iff _ _ _).mpr ⟨x, h, rfl⟩

theorem imageAction_regular_of_isomorphism (hf : IsForcingIsomorphism P R Q S f) {A : V}
    (hA : IsForcingRegular P R A) : IsForcingRegular Q S (imageAction f A) := by
  refine ⟨imageAction_subset_of_isomorphism hf hA.1, ?_, ?_⟩
  · intro x hx b hb hbx
    obtain ⟨a, ha, rfl⟩ := (mem_imageAction_iff _ _ _).mp hx
    obtain ⟨c, hc, rfl⟩ := isForcingIsomorphism_surjective hf b hb
    exact (value_mem_imageAction_iff_of_isomorphism hf hA.1 hc).mpr
      (hA.2.1 a ha c hc ((hf.2.2.2 c hc a (hA.1 a ha)).mpr hbx))
  · intro x hx hd
    obtain ⟨a, ha, rfl⟩ := isForcingIsomorphism_surjective hf x hx
    refine (value_mem_imageAction_iff_of_isomorphism hf hA.1 ha).mpr (hA.2.2 a ha ?_)
    intro b hb hba
    obtain ⟨c, hc, hcb⟩ := hd (f ‘ b) (function_value_mem hf.1 hb) ((hf.2.2.2 b hb a ha).mp hba)
    obtain ⟨d, hd0, rfl⟩ := (mem_imageAction_iff _ _ _).mp hc
    exact ⟨d, hd0, (hf.2.2.2 d (hA.1 d hd0) b hb).mpr hcb⟩

theorem imageAction_subset_iff_of_isomorphism (hf : IsForcingIsomorphism P R Q S f) {A C : V}
    (hA : A ⊆ P) (hC : C ⊆ P) : imageAction f A ⊆ imageAction f C ↔ A ⊆ C := by
  constructor
  · intro h a ha
    exact (value_mem_imageAction_iff_of_isomorphism hf hC (hA a ha)).mp
      (h _ ((value_mem_imageAction_iff_of_isomorphism hf hA (hA a ha)).mpr ha))
  · intro h x hx
    obtain ⟨a, ha, rfl⟩ := (mem_imageAction_iff _ _ _).mp hx
    exact (value_mem_imageAction_iff_of_isomorphism hf hC (hA a ha)).mpr (h a ha)

theorem imageAction_mem_booleanConditions_of_isomorphism (hf : IsForcingIsomorphism P R Q S f)
    {A : V} (hA : A ∈ booleanConditions P R) : imageAction f A ∈ booleanConditions Q S := by
  obtain ⟨hreg, a, ha⟩ := (mem_booleanConditions_iff P R A).mp hA
  exact (mem_booleanConditions_iff Q S _).mpr ⟨imageAction_regular_of_isomorphism hf hreg,
    f ‘ a, (value_mem_imageAction_iff_of_isomorphism hf hreg.1 (hreg.1 a ha)).mpr ha⟩

theorem imageAction_inverse_image (hf : IsForcingIsomorphism P R Q S f) {A : V} (hA : A ⊆ P) :
    imageAction (converseGraph f) (imageAction f A) = A := by
  have : IsFunction f := IsFunction.of_mem hf.1
  apply mem_ext
  intro x
  simp only [mem_imageAction_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hy
    rwa [converseGraph_value_value hf.1 hf.2.1 (hA a ha)]
  · intro hx
    exact ⟨f ‘ x, ⟨x, hx, rfl⟩, (converseGraph_value_value hf.1 hf.2.1 (hA x hx)).symm⟩

theorem imageAction_image_inverse (hf : IsForcingIsomorphism P R Q S f) {C : V} (hC : C ⊆ Q) :
    imageAction f (imageAction (converseGraph f) C) = C := by
  have : IsFunction f := IsFunction.of_mem hf.1
  apply mem_ext
  intro x
  simp only [mem_imageAction_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := hy
    rwa [value_converseGraph_value hf.1 hf.2.1 (hf.2.2.1.symm ▸ hC c hc)]
  · intro hx
    exact ⟨(converseGraph f) ‘ x, ⟨x, hx, rfl⟩,
      (value_converseGraph_value hf.1 hf.2.1 (hf.2.2.1.symm ▸ hC x hx)).symm⟩

/-- A forcing isomorphism of preorders induces a forcing isomorphism of their Boolean
completions, by taking pointwise images. -/
theorem booleanConditions_isomorphic_of_isomorphism (hf : IsForcingIsomorphism P R Q S f) :
    ∃ F, IsForcingIsomorphism (booleanConditions P R) (booleanOrder P R)
      (booleanConditions Q S) (booleanOrder Q S) F := by
  have hi := isForcingIsomorphism_inverse hf
  refine ⟨definableGraph (booleanConditions P R) (imageAction f) (by definability),
    isForcingIsomorphism_of_inverse (imageAction f) (imageAction (converseGraph f))
      (by definability) (fun A hA ↦ imageAction_mem_booleanConditions_of_isomorphism hf hA)
      (fun C hC ↦ imageAction_mem_booleanConditions_of_isomorphism hi hC)
      (fun A hA ↦ imageAction_inverse_image hf ((mem_booleanConditions_iff P R A).mp hA).1.1)
      (fun C hC ↦ imageAction_image_inverse hf ((mem_booleanConditions_iff Q S C).mp hC).1.1)
      (fun A hA C hC ↦ ?_)⟩
  rw [kpair_mem_booleanOrder_iff, kpair_mem_booleanOrder_iff]
  have hAP : A ⊆ P := ((mem_booleanConditions_iff P R A).mp hA).1.1
  have hCP : C ⊆ P := ((mem_booleanConditions_iff P R C).mp hC).1.1
  exact ⟨fun h ↦ ⟨imageAction_mem_booleanConditions_of_isomorphism hf hA,
      imageAction_mem_booleanConditions_of_isomorphism hf hC,
      (imageAction_subset_iff_of_isomorphism hf hAP hCP).mpr h.2.2⟩,
    fun h ↦ ⟨hA, hC, (imageAction_subset_iff_of_isomorphism hf hAP hCP).mp h.2.2⟩⟩

end Transfer


/-! ### The completion of a cone of conditions -/

/-- The cone of conditions below `p`. -/
noncomputable def forcingCone (P R p : V) : V := {q ∈ P ; ⟨q, p⟩ₖ ∈ R}

theorem mem_forcingCone_iff (P R p q : V) :
    q ∈ forcingCone P R p ↔ q ∈ P ∧ ⟨q, p⟩ₖ ∈ R := mem_sep_iff

instance forcingCone_definable : ℒₛₑₜ-function₃[V] forcingCone := by
  have h : ℒₛₑₜ-relation₄[V] (fun C P R p ↦ ∀ q, q ∈ C ↔ q ∈ P ∧ ⟨q, p⟩ₖ ∈ R) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_forcingCone_iff]
  rfl

theorem forcingCone_subset (P R p : V) : forcingCone P R p ⊆ P := sep_subset

theorem coneRegular_eq_forcingClosure (P R p : V) :
    coneRegular P R p = forcingClosure P R (forcingCone P R p) := rfl

theorem forcingCone_downwardClosed {P R p : V} (hR : IsForcingPreorder P R) (hp : p ∈ P) :
    IsForcingDownwardClosed P R (forcingCone P R p) := by
  intro q hq r hr hrq
  obtain ⟨hqP, hqp⟩ := (mem_forcingCone_iff _ _ _ _).mp hq
  exact (mem_forcingCone_iff _ _ _ _).mpr ⟨hr, hR.2.2 r hr q hqP p hp hrq hqp⟩

theorem forcingCone_subset_coneRegular {P R p : V} (hR : IsForcingPreorder P R) (hp : p ∈ P) :
    forcingCone P R p ⊆ coneRegular P R p :=
  subset_forcingClosure hR (forcingCone_subset P R p) (forcingCone_downwardClosed hR hp)

/-- The cone of conditions is dense below every element of the regular cone. -/
theorem exists_forcingCone_below {P R p q r : V} (hq : q ∈ coneRegular P R p) (hr : r ∈ P)
    (hrq : ⟨r, q⟩ₖ ∈ R) : ∃ s ∈ forcingCone P R p, ⟨s, r⟩ₖ ∈ R := by
  obtain ⟨s, hsP, hsp, hsr⟩ := (mem_coneRegular_iff.mp hq).2 r hr hrq
  exact ⟨s, (mem_forcingCone_iff _ _ _ _).mpr ⟨hsP, hsp⟩, hsr⟩

theorem inter_forcingCone_regular {P R p b : V} (hR : IsForcingPreorder P R) (hp : p ∈ P)
    (hb : IsForcingRegular P R b) :
    IsForcingRegular (forcingCone P R p) (restrictedOrder R (forcingCone P R p))
      (b ∩ forcingCone P R p) := by
  refine ⟨fun z hz ↦ (mem_inter_iff.mp hz).2, ?_, ?_⟩
  · intro q hq r hr hrq
    obtain ⟨hqb, hqC⟩ := mem_inter_iff.mp hq
    have hrq' := ((kpair_mem_restrictedOrder_iff _ _ _ _).mp hrq).1
    exact mem_inter_iff.mpr ⟨hb.2.1 q hqb r (forcingCone_subset P R p r hr) hrq', hr⟩
  · intro q hqC hd
    obtain ⟨hqP, hqp⟩ := (mem_forcingCone_iff _ _ _ _).mp hqC
    refine mem_inter_iff.mpr ⟨hb.2.2 q hqP (fun r hr hrq ↦ ?_), hqC⟩
    have hrC : r ∈ forcingCone P R p :=
      (mem_forcingCone_iff _ _ _ _).mpr ⟨hr, hR.2.2 r hr q hqP p hp hrq hqp⟩
    obtain ⟨s, hs, hsr⟩ := hd r hrC ((kpair_mem_restrictedOrder_iff _ _ _ _).mpr ⟨hrq, hrC, hqC⟩)
    exact ⟨s, (mem_inter_iff.mp hs).1, ((kpair_mem_restrictedOrder_iff _ _ _ _).mp hsr).1⟩

theorem forcingClosure_inter_forcingCone {P R p b : V} (hR : IsForcingPreorder P R)
    (hb : IsForcingRegular P R b) (hbc : b ⊆ coneRegular P R p) :
    forcingClosure P R (b ∩ forcingCone P R p) = b := by
  apply SetTheory.subset_antisymm
  · intro q hq
    have h := forcingClosure_mono (P := P) (R := R) (A := b ∩ forcingCone P R p) (B := b)
      (fun z hz ↦ (mem_inter_iff.mp hz).1) q hq
    rwa [forcingClosure_eq hR hb] at h
  · intro q hq
    refine (mem_forcingClosure_iff _ _ _ _).mpr ⟨hb.1 q hq, fun r hr hrq ↦ ?_⟩
    obtain ⟨s, hs, hsr⟩ := exists_forcingCone_below (hbc q hq) hr hrq
    have hrb : r ∈ b := hb.2.1 q hq r hr hrq
    exact ⟨s, mem_inter_iff.mpr
      ⟨hb.2.1 r hrb s (forcingCone_subset P R p s hs) hsr, hs⟩, hsr⟩

theorem coneRegularSet_downwardClosed {P R p A : V} (hR : IsForcingPreorder P R) (hp : p ∈ P)
    (hA : IsForcingRegular (forcingCone P R p) (restrictedOrder R (forcingCone P R p)) A) :
    IsForcingDownwardClosed P R A := by
  intro q hq r hr hrq
  have hqC := hA.1 q hq
  have hrC : r ∈ forcingCone P R p := forcingCone_downwardClosed hR hp q hqC r hr hrq
  exact hA.2.1 q hq r hrC ((kpair_mem_restrictedOrder_iff _ _ _ _).mpr ⟨hrq, hrC, hqC⟩)

theorem coneRegularSet_subset_forcingClosure {P R p A : V} (hR : IsForcingPreorder P R)
    (hp : p ∈ P)
    (hA : IsForcingRegular (forcingCone P R p) (restrictedOrder R (forcingCone P R p)) A) :
    A ⊆ forcingClosure P R A :=
  subset_forcingClosure hR (subset_trans hA.1 (forcingCone_subset P R p))
    (coneRegularSet_downwardClosed hR hp hA)

theorem forcingClosure_inter_eq {P R p A : V} (hR : IsForcingPreorder P R) (hp : p ∈ P)
    (hA : IsForcingRegular (forcingCone P R p) (restrictedOrder R (forcingCone P R p)) A) :
    forcingClosure P R A ∩ forcingCone P R p = A := by
  apply SetTheory.subset_antisymm
  · intro q hq
    obtain ⟨hqcl, hqC⟩ := mem_inter_iff.mp hq
    refine hA.2.2 q hqC (fun r hrC hrq ↦ ?_)
    obtain ⟨s, hsA, hsr⟩ := ((mem_forcingClosure_iff _ _ _ _).mp hqcl).2 r
      (forcingCone_subset P R p r hrC) ((kpair_mem_restrictedOrder_iff _ _ _ _).mp hrq).1
    exact ⟨s, hsA, (kpair_mem_restrictedOrder_iff _ _ _ _).mpr ⟨hsr, hA.1 s hsA, hrC⟩⟩
  · intro a ha
    exact mem_inter_iff.mpr
      ⟨coneRegularSet_subset_forcingClosure hR hp hA a ha, hA.1 a ha⟩

/-- The conditions of the Boolean completion below the regular cone of `p`. -/
noncomputable def booleanCone (P R p : V) : V :=
  {b ∈ booleanConditions P R ; b ⊆ coneRegular P R p}

theorem mem_booleanCone_iff (P R p b : V) :
    b ∈ booleanCone P R p ↔ b ∈ booleanConditions P R ∧ b ⊆ coneRegular P R p := mem_sep_iff

/-- The Boolean completion of the cone of `p` is the part of the Boolean completion below the
regular cone of `p`: intersecting with the cone is a forcing isomorphism, with regularization
as inverse. -/
theorem booleanCone_isomorphic_completion_of_cone {P R p : V} (hR : IsForcingPreorder P R)
    (hp : p ∈ P) :
    ∃ F, IsForcingIsomorphism (booleanCone P R p)
      (restrictedOrder (booleanOrder P R) (booleanCone P R p))
      (booleanConditions (forcingCone P R p) (restrictedOrder R (forcingCone P R p)))
      (booleanOrder (forcingCone P R p) (restrictedOrder R (forcingCone P R p)))
      F := by
  have hFP : ∀ b ∈ booleanCone P R p, b ∩ forcingCone P R p ∈
      booleanConditions (forcingCone P R p) (restrictedOrder R (forcingCone P R p)) := by
    intro b hb
    obtain ⟨hbB, hbc⟩ := (mem_booleanCone_iff _ _ _ _).mp hb
    obtain ⟨hbreg, q, hq⟩ := (mem_booleanConditions_iff P R b).mp hbB
    refine (mem_booleanConditions_iff _ _ _).mpr ⟨inter_forcingCone_regular hR hp hbreg, ?_⟩
    obtain ⟨s, hs, hsq⟩ := exists_forcingCone_below (hbc q hq) (hbreg.1 q hq)
      (hR.2.1 q (hbreg.1 q hq))
    exact ⟨s, mem_inter_iff.mpr
      ⟨hbreg.2.1 q hq s (forcingCone_subset P R p s hs) hsq, hs⟩⟩
  have hGQ : ∀ A ∈ booleanConditions (forcingCone P R p) (restrictedOrder R (forcingCone P R p)),
      forcingClosure P R A ∈ booleanCone P R p := by
    intro A hA
    obtain ⟨hAreg, a, ha⟩ := (mem_booleanConditions_iff _ _ A).mp hA
    refine (mem_booleanCone_iff _ _ _ _).mpr ⟨(mem_booleanConditions_iff P R _).mpr
      ⟨forcingClosure_regular hR (subset_trans hAreg.1 (forcingCone_subset P R p)),
        a, coneRegularSet_subset_forcingClosure hR hp hAreg a ha⟩, ?_⟩
    exact forcingClosure_mono hAreg.1
  refine ⟨definableGraph (booleanCone P R p) (fun b ↦ b ∩ forcingCone P R p) (by definability),
    isForcingIsomorphism_of_inverse (fun b ↦ b ∩ forcingCone P R p) (forcingClosure P R)
      (by definability) hFP hGQ ?_ ?_ ?_⟩
  · intro b hb
    obtain ⟨hbB, hbc⟩ := (mem_booleanCone_iff _ _ _ _).mp hb
    exact forcingClosure_inter_forcingCone hR ((mem_booleanConditions_iff P R b).mp hbB).1 hbc
  · intro A hA
    exact forcingClosure_inter_eq hR hp ((mem_booleanConditions_iff _ _ A).mp hA).1
  · intro b hb c hc
    have hbc := (mem_booleanCone_iff _ _ _ _).mp hb
    have hcc := (mem_booleanCone_iff _ _ _ _).mp hc
    rw [kpair_mem_restrictedOrder_iff, kpair_mem_booleanOrder_iff, kpair_mem_booleanOrder_iff]
    simp only [hb, hc, hbc.1, hcc.1, hFP b hb, hFP c hc, true_and, and_true]
    constructor
    · intro h z hz
      exact mem_inter_iff.mpr ⟨h _ (mem_inter_iff.mp hz).1, (mem_inter_iff.mp hz).2⟩
    · intro h
      have h1 := forcingClosure_mono (P := P) (R := R) h
      rw [forcingClosure_inter_forcingCone hR ((mem_booleanConditions_iff P R b).mp hbc.1).1 hbc.2,
        forcingClosure_inter_forcingCone hR ((mem_booleanConditions_iff P R c).mp hcc.1).1 hcc.2]
        at h1
      exact h1

/-! ### The Boolean completion of the Levy collapse below a cone -/

theorem forcingCone_levy {κ p : V} (hp : p ∈ levyCollapse κ) :
    forcingCone (levyCollapse κ) (levyOrder κ) p = levyCollapseCone κ p := by
  apply mem_ext
  intro r
  rw [mem_forcingCone_iff, mem_levyCollapseCone]
  unfold levyOrder
  rw [pair_mem_reverseInclusionOrder]
  exact ⟨fun h ↦ ⟨h.1, h.2.2.2⟩, fun h ↦ ⟨h.1, h.1, hp, h.2⟩⟩

theorem restrictedOrder_levyOrder_cone (κ p : V) :
    restrictedOrder (levyOrder κ) (levyCollapseCone κ p) =
      reverseInclusionOrder (levyCollapseCone κ p) := by
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨hzR, hzQ⟩ := mem_inter_iff.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hzQ
    unfold levyOrder at hzR
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr
      ⟨ha, hb, ((pair_mem_reverseInclusionOrder _ _ _).mp hzR).2.2⟩
  · intro hz
    obtain ⟨hzQ, hsub⟩ := mem_sep_iff.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hzQ
    refine mem_inter_iff.mpr ⟨?_, hzQ⟩
    unfold levyOrder
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hsub
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr
      ⟨((mem_levyCollapseCone _ _ _).mp ha).1, ((mem_levyCollapseCone _ _ _).mp hb).1, hsub⟩

/-- The completion version of the cone isomorphism: the part of the Boolean completion of
`Coll(ω, <κ)` below the regular cone of a condition `p` is forcing isomorphic to the whole
Boolean completion. -/
theorem levy_booleanCone_isomorphic {κ p : V} (hp : p ∈ levyCollapse κ) :
    ∃ F, IsForcingIsomorphism
      (booleanCone (levyCollapse κ) (levyOrder κ) p)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (booleanCone (levyCollapse κ) (levyOrder κ) p))
      (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) F := by
  obtain ⟨F, hF⟩ := booleanCone_isomorphic_completion_of_cone (levyCollapse_poset κ).1 hp
  rw [forcingCone_levy hp, restrictedOrder_levyOrder_cone κ p] at hF
  obtain ⟨g, hg⟩ := levyCollapse_cone_isomorphic hp
  obtain ⟨G, hG⟩ := booleanConditions_isomorphic_of_isomorphism hg
  exact ⟨compose F G, isForcingIsomorphism_compose hF hG⟩


/-! ### Boolean algebra helpers -/

theorem inter_comm_set (A B : V) : A ∩ B = B ∩ A := by
  apply mem_ext
  intro z
  simp only [mem_inter_iff]
  tauto

theorem inter_eq_right_of_subset {A B : V} (h : A ⊆ B) : B ∩ A = A := by
  apply mem_ext
  intro z
  simp only [mem_inter_iff]
  exact ⟨fun hz ↦ hz.2, fun hz ↦ ⟨h z hz, hz⟩⟩

theorem inter_eq_left_of_subset {A B : V} (h : A ⊆ B) : A ∩ B = A := by
  apply mem_ext
  intro z
  simp only [mem_inter_iff]
  exact ⟨fun hz ↦ hz.1, fun hz ↦ ⟨hz, h z hz⟩⟩

theorem repl_pair (F : V → V) (hF : ℒₛₑₜ-function₁ F) (A B : V) :
    repl F hF ({A, B} : V) = ({F A, F B} : V) := by
  apply mem_ext
  intro z
  rw [repl_spec]
  constructor
  · rintro ⟨C, hC, rfl⟩
    rcases mem_insert.mp hC with rfl | hC
    · exact mem_insert.mpr (Or.inl rfl)
    · rw [mem_singleton_iff.mp hC]
      exact mem_insert.mpr (Or.inr (mem_singleton_iff.mpr rfl))
  · intro hz
    rcases mem_insert.mp hz with rfl | hz
    · exact ⟨A, mem_insert.mpr (Or.inl rfl), rfl⟩
    · exact ⟨B, mem_insert.mpr (Or.inr (mem_singleton_iff.mpr rfl)), mem_singleton_iff.mp hz⟩

theorem regularJoin_pair_empty {P R A : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingRegular P R A) : regularJoin P R ({A, ∅} : V) = A := by
  apply SetTheory.subset_antisymm
  · exact regularJoin_pair_subset hR hA (subset_refl _) (empty_subset A)
  · exact subset_regularJoin_pair_left hR hA

/-- A regular set splits as the join of its parts inside a regular set and its negation. -/
theorem regularJoin_pair_split {P R b a : V} (hR : IsForcingPreorder P R)
    (hb : IsForcingRegular P R b) (ha : IsForcingRegular P R a) :
    b = regularJoin P R ({b ∩ a, b ∩ forcingNegation P R a} : V) := by
  have hsub : ∀ C ∈ ({a, forcingNegation P R a} : V), C ⊆ P := by
    intro C hC
    rcases mem_insert.mp hC with rfl | hC
    · exact ha.1
    · rw [mem_singleton_iff.mp hC]
      exact forcingNegation_subset _ _ _
  have h2 := inter_regularJoin hR hb hsub
  rw [regularJoin_negation hR ha, repl_pair] at h2
  rwa [inter_eq_left_of_subset hb.1] at h2

/-- Reading off one half of a join of two disjoint halves. -/
theorem regularJoin_pair_inter {P R c A B : V} (hR : IsForcingPreorder P R)
    (hc : IsForcingRegular P R c) (hA : IsForcingRegular P R A) (hAc : A ⊆ c)
    (hB : B ⊆ forcingNegation P R c) : regularJoin P R ({A, B} : V) ∩ c = A := by
  have hsub : ∀ C ∈ ({A, B} : V), C ⊆ P := by
    intro C hC
    rcases mem_insert.mp hC with rfl | hC
    · exact hA.1
    · rw [mem_singleton_iff.mp hC]
      exact subset_trans hB (forcingNegation_subset _ _ _)
  have h2 := inter_regularJoin hR hc hsub
  rw [repl_pair] at h2
  have hcA : c ∩ A = A := inter_eq_right_of_subset hAc
  have hcB : c ∩ B = (∅ : V) := by
    apply mem_ext
    intro z
    simp only [mem_inter_iff, not_mem_empty, iff_false, not_and]
    intro hzc hzB
    have : z ∈ c ∩ forcingNegation P R c := mem_inter_iff.mpr ⟨hzc, hB z hzB⟩
    rw [inter_forcingNegation_eq_empty hR hc.1] at this
    exact not_mem_empty this
  rw [hcA, hcB, regularJoin_pair_empty hR hA] at h2
  rw [inter_comm_set]
  exact h2

/-! ### Extending a cone isomorphism to the zero condition -/

/-- The cone of the Boolean completion below a condition `b0`. -/
noncomputable def boolCone (P R b0 : V) : V :=
  forcingCone (booleanConditions P R) (booleanOrder P R) b0

instance boolCone_definable : ℒₛₑₜ-function₃[V] boolCone := by
  unfold boolCone
  definability

theorem mem_boolCone_iff (P R b0 x : V) :
    x ∈ boolCone P R b0 ↔ x ∈ booleanConditions P R ∧ ⟨x, b0⟩ₖ ∈ booleanOrder P R :=
  mem_forcingCone_iff _ _ _ _

/-- The elements of a set that are included in a given set. -/
noncomputable def subsetBelow (C a : V) : V := {x ∈ C ; x ⊆ a}

theorem mem_subsetBelow_iff (C a x : V) : x ∈ subsetBelow C a ↔ x ∈ C ∧ x ⊆ a := mem_sep_iff

instance subsetBelow_definable : ℒₛₑₜ-function₂[V] subsetBelow := by
  have h : ℒₛₑₜ-relation₃[V] (fun D C a ↦ ∀ x, x ∈ D ↔ x ∈ C ∧ x ⊆ a) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [subsetBelow, mem_sep_iff]
  rfl

noncomputable def coneBelow (P R b0 a : V) : V := subsetBelow (boolCone P R b0) a

theorem mem_coneBelow_iff (P R b0 a x : V) :
    x ∈ coneBelow P R b0 a ↔
      x ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b0 ∧ x ⊆ a :=
  mem_subsetBelow_iff _ _ _

noncomputable def unionImage (P f X : V) : V := {z ∈ P ; ∃ x ∈ X, z ∈ f ‘ x}

theorem mem_unionImage_iff (P f X z : V) :
    z ∈ unionImage P f X ↔ z ∈ P ∧ ∃ x ∈ X, z ∈ f ‘ x := mem_sep_iff

instance unionImage_definable : ℒₛₑₜ-function₃[V] unionImage := by
  have h : ℒₛₑₜ-relation₄[V] (fun C P f X ↦ ∀ z, z ∈ C ↔ z ∈ P ∧ ∃ x ∈ X, z ∈ f ‘ x) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [unionImage, mem_sep_iff]
  rfl

/-- The image of a regular set below `b0` under a map of the cone `B|b0`: the union of the
images of all conditions of the cone below it. On conditions of the cone this is the value of
the map, and on the empty set it is the empty set. -/
noncomputable def coneImage (P R b0 f a : V) : V := unionImage P f (coneBelow P R b0 a)

theorem mem_coneImage_iff (P R b0 f a z : V) :
    z ∈ coneImage P R b0 f a ↔ z ∈ P ∧ ∃ x ∈ coneBelow P R b0 a, z ∈ f ‘ x :=
  mem_unionImage_iff _ _ _ _

theorem coneImage_empty (P R b0 f : V) : coneImage P R b0 f (∅ : V) = (∅ : V) := by
  apply mem_ext
  intro z
  simp only [not_mem_empty, iff_false]
  intro hz
  obtain ⟨-, x, hx, -⟩ := (mem_coneImage_iff _ _ _ _ _ _).mp hz
  obtain ⟨hxc, hx0⟩ := (mem_coneBelow_iff _ _ _ _ _).mp hx
  obtain ⟨-, q, hq⟩ := (mem_booleanConditions_iff _ _ x).mp
    ((mem_forcingCone_iff _ _ _ _).mp hxc).1
  exact not_mem_empty (hx0 q hq)

theorem coneImage_mono {P R b0 f a a' : V} (h : a ⊆ a') :
    coneImage P R b0 f a ⊆ coneImage P R b0 f a' := by
  intro z hz
  obtain ⟨hzP, x, hx, hzx⟩ := (mem_coneImage_iff _ _ _ _ _ _).mp hz
  obtain ⟨hxc, hx0⟩ := (mem_coneBelow_iff _ _ _ _ _).mp hx
  exact (mem_coneImage_iff _ _ _ _ _ _).mpr
    ⟨hzP, x, (mem_coneBelow_iff _ _ _ _ _).mpr ⟨hxc, subset_trans hx0 h⟩, hzx⟩

theorem coneImage_subset (P R b0 f a : V) : coneImage P R b0 f a ⊆ P :=
  fun z hz ↦ ((mem_coneImage_iff _ _ _ _ _ _).mp hz).1

section ConeMaps

variable {P R b0 c0 f : V}

/-- A cone isomorphism is monotone. -/
theorem coneIsomorphism_mono
    (hf : IsForcingIsomorphism (forcingCone (booleanConditions P R) (booleanOrder P R) b0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b0))
      (forcingCone (booleanConditions P R) (booleanOrder P R) c0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) c0)) f)
    {x a : V} (hx : x ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b0)
    (ha : a ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b0) (hxa : x ⊆ a) :
    f ‘ x ⊆ f ‘ a := by
  have hxB := ((mem_forcingCone_iff _ _ _ _).mp hx).1
  have haB := ((mem_forcingCone_iff _ _ _ _).mp ha).1
  have hord : ⟨x, a⟩ₖ ∈ restrictedOrder (booleanOrder P R)
      (forcingCone (booleanConditions P R) (booleanOrder P R) b0) :=
    (kpair_mem_restrictedOrder_iff _ _ _ _).mpr
      ⟨(kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hxB, haB, hxa⟩, hx, ha⟩
  have h := (hf.2.2.2 x hx a ha).mp hord
  exact ((kpair_mem_booleanOrder_iff _ _ _ _).mp
    ((kpair_mem_restrictedOrder_iff _ _ _ _).mp h).1).2.2

/-- On a condition of the cone the extended map is the map. -/
theorem coneImage_value
    (hf : IsForcingIsomorphism (forcingCone (booleanConditions P R) (booleanOrder P R) b0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b0))
      (forcingCone (booleanConditions P R) (booleanOrder P R) c0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) c0)) f)
    {a : V} (ha : a ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b0) :
    coneImage P R b0 f a = f ‘ a := by
  have hfa := function_value_mem hf.1 ha
  have hfaP : f ‘ a ⊆ P :=
    ((mem_booleanConditions_iff _ _ _).mp ((mem_forcingCone_iff _ _ _ _).mp hfa).1).1.1
  apply SetTheory.subset_antisymm
  · intro z hz
    obtain ⟨-, x, hx, hzx⟩ := (mem_coneImage_iff _ _ _ _ _ _).mp hz
    obtain ⟨hxc, hx0⟩ := (mem_coneBelow_iff _ _ _ _ _).mp hx
    exact coneIsomorphism_mono hf hxc ha hx0 z hzx
  · intro z hz
    exact (mem_coneImage_iff _ _ _ _ _ _).mpr ⟨hfaP z hz, a,
      (mem_coneBelow_iff _ _ _ _ _).mpr ⟨ha, subset_refl _⟩, hz⟩

end ConeMaps

/-! ### Lifting a pair of cone isomorphisms to an automorphism of the completion -/

section Lift

variable {P R b0 c0 f g : V}

/-- A regular subset of `b0` is either empty or a condition of the cone `B|b0`. -/
theorem mem_forcingCone_boolean_of_nonempty {a : V} (hb0 : b0 ∈ booleanConditions P R)
    (ha : IsForcingRegular P R a) (hab : a ⊆ b0) (hne : ∃ q, q ∈ a) :
    a ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b0 := by
  have haB : a ∈ booleanConditions P R := (mem_booleanConditions_iff P R a).mpr ⟨ha, hne⟩
  exact (mem_forcingCone_iff _ _ _ _).mpr
    ⟨haB, (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨haB, hb0, hab⟩⟩

theorem coneImage_regular (hR : IsForcingPreorder P R) {a : V}
    (hf : IsForcingIsomorphism (forcingCone (booleanConditions P R) (booleanOrder P R) b0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b0))
      (forcingCone (booleanConditions P R) (booleanOrder P R) c0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) c0)) f)
    (hb0 : b0 ∈ booleanConditions P R)
    (ha : IsForcingRegular P R a) (hab : a ⊆ b0) :
    IsForcingRegular P R (coneImage P R b0 f a) ∧ coneImage P R b0 f a ⊆ c0 ∧
      ((∃ q, q ∈ a) → ∃ q, q ∈ coneImage P R b0 f a) := by
  by_cases hne : ∃ q, q ∈ a
  · have hac := mem_forcingCone_boolean_of_nonempty hb0 ha hab hne
    have hfa := function_value_mem hf.1 hac
    have hfaB := ((mem_forcingCone_iff _ _ _ _).mp hfa).1
    have hfac := ((kpair_mem_booleanOrder_iff _ _ _ _).mp
      ((mem_forcingCone_iff _ _ _ _).mp hfa).2).2.2
    rw [coneImage_value hf hac]
    exact ⟨(mem_booleanConditions_iff P R _).mp hfaB |>.1, hfac,
      fun _ ↦ (mem_booleanConditions_iff P R _).mp hfaB |>.2⟩
  · have ha0 : a = (∅ : V) :=
      mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hne, fun hz ↦ absurd hz not_mem_empty⟩)
    rw [ha0, coneImage_empty]
    exact ⟨forcingRegular_empty hR, empty_subset c0, fun h ↦ absurd (ha0 ▸ h) hne⟩

end Lift


theorem regularJoin_pair_eq_closure (P R A B : V) :
    regularJoin P R ({A, B} : V) = forcingClosure P R (A ∪ B) := by
  unfold regularJoin
  rw [sUnion_pair_eq]

theorem coneImageMap_definable (P R b0 f : V) :
    ℒₛₑₜ-function₁ (fun b : V ↦ coneImage P R b0 f (b ∩ b0)) := by
  unfold coneImage coneBelow
  definability

theorem coneJoinMap_definable (P R b0 n0 f g : V) :
    ℒₛₑₜ-function₁ (fun b : V ↦ regularJoin P R
      ({coneImage P R b0 f (b ∩ b0), coneImage P R n0 g (b ∩ n0)} : V)) := by
  have he : (fun b : V ↦ regularJoin P R
      ({coneImage P R b0 f (b ∩ b0), coneImage P R n0 g (b ∩ n0)} : V)) =
      (fun b : V ↦ forcingClosure P R
        (coneImage P R b0 f (b ∩ b0) ∪ coneImage P R n0 g (b ∩ n0))) := by
    funext b
    exact regularJoin_pair_eq_closure _ _ _ _
  have h1 := coneImageMap_definable P R b0 f
  have h2 := coneImageMap_definable P R n0 g
  rw [he]
  definability

theorem pair_comm_set (A B : V) : ({A, B} : V) = ({B, A} : V) := by
  apply mem_ext
  intro z
  simp only [mem_insert, mem_singleton_iff]
  tauto

section Lift2

variable {P R b0 c0 f : V}

/-- Round trip of the extended cone maps, from the source side. -/
theorem coneImage_inverse_right
    (hf : IsForcingIsomorphism (forcingCone (booleanConditions P R) (booleanOrder P R) b0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b0))
      (forcingCone (booleanConditions P R) (booleanOrder P R) c0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) c0)) f)
    (hb0 : b0 ∈ booleanConditions P R) {a : V} (ha : IsForcingRegular P R a) (hab : a ⊆ b0) :
    coneImage P R c0 (converseGraph f) (coneImage P R b0 f a) = a := by
  have : IsFunction f := IsFunction.of_mem hf.1
  by_cases hne : ∃ q, q ∈ a
  · have hac := mem_forcingCone_boolean_of_nonempty hb0 ha hab hne
    rw [coneImage_value hf hac,
      coneImage_value (isForcingIsomorphism_inverse hf) (function_value_mem hf.1 hac),
      converseGraph_value_value hf.1 hf.2.1 hac]
  · have ha0 : a = (∅ : V) :=
      mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hne, fun hz ↦ absurd hz not_mem_empty⟩)
    rw [ha0, coneImage_empty, coneImage_empty]

/-- Round trip of the extended cone maps, from the target side. -/
theorem coneImage_inverse_left
    (hf : IsForcingIsomorphism (forcingCone (booleanConditions P R) (booleanOrder P R) b0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b0))
      (forcingCone (booleanConditions P R) (booleanOrder P R) c0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) c0)) f)
    (hc0 : c0 ∈ booleanConditions P R) {a : V} (ha : IsForcingRegular P R a) (hac : a ⊆ c0) :
    coneImage P R b0 f (coneImage P R c0 (converseGraph f) a) = a := by
  have : IsFunction f := IsFunction.of_mem hf.1
  have hi := isForcingIsomorphism_inverse hf
  by_cases hne : ∃ q, q ∈ a
  · have hacone := mem_forcingCone_boolean_of_nonempty hc0 ha hac hne
    rw [coneImage_value hi hacone, coneImage_value hf (function_value_mem hi.1 hacone),
      value_converseGraph_value hf.1 hf.2.1 (hf.2.2.1.symm ▸ hacone)]
  · have ha0 : a = (∅ : V) :=
      mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hne, fun hz ↦ absurd hz not_mem_empty⟩)
    rw [ha0, coneImage_empty, coneImage_empty]

end Lift2

/-- Karagila-Schilhan Lemma 9.3, lifting step. Given an isomorphism `f` of the cone `B|b0` with
the cone `B|c0` and an isomorphism `g` of the complementary cones `B|¬b0` and `B|¬c0`, there is
an automorphism of the Boolean completion `B` that agrees with `f` below `b0`: it sends `b` to a
condition whose part below `c0` is `f (b ∩ b0)`. The complementary isomorphism is needed: an
automorphism of `B` restricts to one of `B|¬b0`, so without it the conclusion can fail. -/
theorem exists_booleanAutomorphism_of_cone_isomorphisms {P R b0 c0 f g : V}
    (hR : IsForcingPreorder P R)
    (hb0 : b0 ∈ booleanConditions P R) (hc0 : c0 ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (forcingCone (booleanConditions P R) (booleanOrder P R) b0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b0))
      (forcingCone (booleanConditions P R) (booleanOrder P R) c0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) c0)) f)
    (hg : IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R b0))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R b0)))
      (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R c0))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R c0))) g) :
    ∃ Θ ∈ forcingAutomorphisms (booleanConditions P R) (booleanOrder P R),
      (∀ b ∈ booleanConditions P R, b ∩ b0 ∈ booleanConditions P R →
        (Θ ‘ b) ∩ c0 = f ‘ (b ∩ b0)) ∧
      ∀ a ∈ booleanConditions P R,
        coneImage P R b0 f (a ∩ b0) = a ∩ c0 →
        coneImage P R (forcingNegation P R b0) g (a ∩ forcingNegation P R b0) =
          a ∩ forcingNegation P R c0 →
        Θ ‘ a = a := by
  classical
  have hb0r : IsForcingRegular P R b0 := ((mem_booleanConditions_iff P R b0).mp hb0).1
  have hc0r : IsForcingRegular P R c0 := ((mem_booleanConditions_iff P R c0).mp hc0).1
  have hn0r : IsForcingRegular P R (forcingNegation P R b0) :=
    forcingNegation_regular hR hb0r.2.1
  have hm0r : IsForcingRegular P R (forcingNegation P R c0) :=
    forcingNegation_regular hR hc0r.2.1
  set n0 := forcingNegation P R b0 with hn0
  set m0 := forcingNegation P R c0 with hm0
  -- the two halves of a condition
  have hsplit : ∀ b : V, IsForcingRegular P R b →
      b = regularJoin P R ({b ∩ b0, b ∩ n0} : V) := fun b hb ↦
    regularJoin_pair_split hR hb hb0r
  have hsplitc : ∀ c : V, IsForcingRegular P R c →
      c = regularJoin P R ({c ∩ c0, c ∩ m0} : V) := fun c hc ↦
    regularJoin_pair_split hR hc hc0r
  -- the map and its inverse
  let F : V → V := fun b ↦ regularJoin P R
    ({coneImage P R b0 f (b ∩ b0), coneImage P R n0 g (b ∩ n0)} : V)
  let G : V → V := fun c ↦ regularJoin P R
    ({coneImage P R c0 (converseGraph f) (c ∩ c0),
      coneImage P R m0 (converseGraph g) (c ∩ m0)} : V)
  have hFdef : ℒₛₑₜ-function₁ F := coneJoinMap_definable P R b0 n0 f g
  have hGdef : ℒₛₑₜ-function₁ G :=
    coneJoinMap_definable P R c0 m0 (converseGraph f) (converseGraph g)
  -- properties of the halves
  have hleft : ∀ b : V, IsForcingRegular P R b →
      IsForcingRegular P R (coneImage P R b0 f (b ∩ b0)) ∧
        coneImage P R b0 f (b ∩ b0) ⊆ c0 ∧
        ((∃ q, q ∈ b ∩ b0) → ∃ q, q ∈ coneImage P R b0 f (b ∩ b0)) := fun b hb ↦
    coneImage_regular hR hf hb0 (forcingRegular_inter hb hb0r) (fun z hz ↦ (mem_inter_iff.mp hz).2)
  have hright : ∀ b : V, IsForcingRegular P R b →
      IsForcingRegular P R (coneImage P R n0 g (b ∩ n0)) ∧
        coneImage P R n0 g (b ∩ n0) ⊆ m0 ∧
        ((∃ q, q ∈ b ∩ n0) → ∃ q, q ∈ coneImage P R n0 g (b ∩ n0)) := fun b hb ↦ by
    by_cases hn0B : n0 ∈ booleanConditions P R
    · exact coneImage_regular hR hg hn0B (forcingRegular_inter hb hn0r)
        (fun z hz ↦ (mem_inter_iff.mp hz).2)
    · have hn00 : n0 = (∅ : V) := by
        by_contra hne
        obtain ⟨q, hq⟩ : ∃ q, q ∈ n0 := by
          by_contra hno
          exact hne (mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hno,
            fun hz ↦ absurd hz not_mem_empty⟩))
        exact hn0B ((mem_booleanConditions_iff P R n0).mpr ⟨hn0r, q, hq⟩)
      have hbn : b ∩ n0 = (∅ : V) := by
        apply mem_ext
        intro z
        simp only [mem_inter_iff, hn00, not_mem_empty, and_false]
      rw [hbn, coneImage_empty]
      exact ⟨forcingRegular_empty hR, empty_subset m0, fun h ↦ absurd h (by
        rintro ⟨q, hq⟩; exact not_mem_empty hq)⟩
  have hFreg : ∀ b : V, IsForcingRegular P R b → IsForcingRegular P R (F b) := by
    intro b hb
    apply regularJoin_regular hR
    intro C hC
    rcases mem_insert.mp hC with rfl | hC
    · exact (hleft b hb).1.1
    · rw [mem_singleton_iff.mp hC]
      exact (hright b hb).1.1
  have hFleft : ∀ b : V, IsForcingRegular P R b → F b ∩ c0 = coneImage P R b0 f (b ∩ b0) := by
    intro b hb
    exact regularJoin_pair_inter hR hc0r (hleft b hb).1 (hleft b hb).2.1 (hright b hb).2.1
  have hFright : ∀ b : V, IsForcingRegular P R b → F b ∩ m0 = coneImage P R n0 g (b ∩ n0) := by
    intro b hb
    have hcm : coneImage P R b0 f (b ∩ b0) ⊆ forcingNegation P R m0 := by
      rw [hm0, forcingNegation_negation hR hc0r]
      exact (hleft b hb).2.1
    show regularJoin P R
      ({coneImage P R b0 f (b ∩ b0), coneImage P R n0 g (b ∩ n0)} : V) ∩ m0 = _
    rw [pair_comm_set]
    exact regularJoin_pair_inter hR hm0r (hright b hb).1 (hright b hb).2.1 hcm
  have hFnonempty : ∀ b : V, IsForcingRegular P R b → (∃ q, q ∈ b) → ∃ q, q ∈ F b := by
    intro b hb hne
    obtain ⟨q, hq⟩ := hne
    have hqj : q ∈ regularJoin P R ({b ∩ b0, b ∩ n0} : V) := (hsplit b hb) ▸ hq
    obtain ⟨hqP, hh⟩ := (mem_regularJoin_iff _ _ _ _).mp hqj
    obtain ⟨r, ⟨C, hC, hrC⟩, -⟩ := hh q hqP (hR.2.1 q hqP)
    rcases mem_insert.mp hC with rfl | hC
    · obtain ⟨s, hs⟩ := (hleft b hb).2.2 ⟨r, hrC⟩
      exact ⟨s, subset_regularJoin_pair_left hR (hleft b hb).1 s hs⟩
    · rw [mem_singleton_iff.mp hC] at hrC
      obtain ⟨s, hs⟩ := (hright b hb).2.2 ⟨r, hrC⟩
      exact ⟨s, subset_regularJoin_pair_right hR (hright b hb).1 s hs⟩
  have hFB : ∀ b ∈ booleanConditions P R, F b ∈ booleanConditions P R := by
    intro b hb
    obtain ⟨hbr, q, hq⟩ := (mem_booleanConditions_iff P R b).mp hb
    exact (mem_booleanConditions_iff P R _).mpr ⟨hFreg b hbr, hFnonempty b hbr ⟨q, hq⟩⟩
  -- the same for the inverse, obtained by symmetry of the hypotheses
  have hgi := isForcingIsomorphism_inverse hg
  have hfi := isForcingIsomorphism_inverse hf
  have hleft' : ∀ c : V, IsForcingRegular P R c →
      IsForcingRegular P R (coneImage P R c0 (converseGraph f) (c ∩ c0)) ∧
        coneImage P R c0 (converseGraph f) (c ∩ c0) ⊆ b0 ∧
        ((∃ q, q ∈ c ∩ c0) → ∃ q, q ∈ coneImage P R c0 (converseGraph f) (c ∩ c0)) := fun c hc ↦
    coneImage_regular hR hfi hc0 (forcingRegular_inter hc hc0r)
      (fun z hz ↦ (mem_inter_iff.mp hz).2)
  have hright' : ∀ c : V, IsForcingRegular P R c →
      IsForcingRegular P R (coneImage P R m0 (converseGraph g) (c ∩ m0)) ∧
        coneImage P R m0 (converseGraph g) (c ∩ m0) ⊆ n0 ∧
        ((∃ q, q ∈ c ∩ m0) → ∃ q, q ∈ coneImage P R m0 (converseGraph g) (c ∩ m0)) := fun c hc ↦ by
    by_cases hm0B : m0 ∈ booleanConditions P R
    · exact coneImage_regular hR hgi hm0B (forcingRegular_inter hc hm0r)
        (fun z hz ↦ (mem_inter_iff.mp hz).2)
    · have hm00 : m0 = (∅ : V) := by
        by_contra hne
        obtain ⟨q, hq⟩ : ∃ q, q ∈ m0 := by
          by_contra hno
          exact hne (mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hno,
            fun hz ↦ absurd hz not_mem_empty⟩))
        exact hm0B ((mem_booleanConditions_iff P R m0).mpr ⟨hm0r, q, hq⟩)
      have hcm : c ∩ m0 = (∅ : V) := by
        apply mem_ext
        intro z
        simp only [mem_inter_iff, hm00, not_mem_empty, and_false]
      rw [hcm, coneImage_empty]
      exact ⟨forcingRegular_empty hR, empty_subset n0, fun h ↦ absurd h (by
        rintro ⟨q, hq⟩; exact not_mem_empty hq)⟩
  have hGreg : ∀ c : V, IsForcingRegular P R c → IsForcingRegular P R (G c) := by
    intro c hc
    apply regularJoin_regular hR
    intro C hC
    rcases mem_insert.mp hC with rfl | hC
    · exact (hleft' c hc).1.1
    · rw [mem_singleton_iff.mp hC]
      exact (hright' c hc).1.1
  have hGnonempty : ∀ c : V, IsForcingRegular P R c → (∃ q, q ∈ c) → ∃ q, q ∈ G c := by
    intro c hc hne
    obtain ⟨q, hq⟩ := hne
    have hqj : q ∈ regularJoin P R ({c ∩ c0, c ∩ m0} : V) := (hsplitc c hc) ▸ hq
    obtain ⟨hqP, hh⟩ := (mem_regularJoin_iff _ _ _ _).mp hqj
    obtain ⟨r, ⟨C, hC, hrC⟩, -⟩ := hh q hqP (hR.2.1 q hqP)
    rcases mem_insert.mp hC with rfl | hC
    · obtain ⟨s, hs⟩ := (hleft' c hc).2.2 ⟨r, hrC⟩
      exact ⟨s, subset_regularJoin_pair_left hR (hleft' c hc).1 s hs⟩
    · rw [mem_singleton_iff.mp hC] at hrC
      obtain ⟨s, hs⟩ := (hright' c hc).2.2 ⟨r, hrC⟩
      exact ⟨s, subset_regularJoin_pair_right hR (hright' c hc).1 s hs⟩
  have hGB : ∀ c ∈ booleanConditions P R, G c ∈ booleanConditions P R := by
    intro c hc
    obtain ⟨hcr, q, hq⟩ := (mem_booleanConditions_iff P R c).mp hc
    exact (mem_booleanConditions_iff P R _).mpr ⟨hGreg c hcr, hGnonempty c hcr ⟨q, hq⟩⟩
  have hGleft : ∀ c : V, IsForcingRegular P R c →
      G c ∩ b0 = coneImage P R c0 (converseGraph f) (c ∩ c0) := by
    intro c hc
    exact regularJoin_pair_inter hR hb0r (hleft' c hc).1 (hleft' c hc).2.1 (hright' c hc).2.1
  have hGright : ∀ c : V, IsForcingRegular P R c →
      G c ∩ n0 = coneImage P R m0 (converseGraph g) (c ∩ m0) := by
    intro c hc
    have hcm : coneImage P R c0 (converseGraph f) (c ∩ c0) ⊆ forcingNegation P R n0 := by
      rw [hn0, forcingNegation_negation hR hb0r]
      exact (hleft' c hc).2.1
    show regularJoin P R
      ({coneImage P R c0 (converseGraph f) (c ∩ c0),
        coneImage P R m0 (converseGraph g) (c ∩ m0)} : V) ∩ n0 = _
    rw [pair_comm_set]
    exact regularJoin_pair_inter hR hn0r (hright' c hc).1 (hright' c hc).2.1 hcm
  -- round trips
  have hGF : ∀ b ∈ booleanConditions P R, G (F b) = b := by
    intro b hb
    have hbr := ((mem_booleanConditions_iff P R b).mp hb).1
    have h1 : G (F b) = regularJoin P R
        ({coneImage P R c0 (converseGraph f) (F b ∩ c0),
          coneImage P R m0 (converseGraph g) (F b ∩ m0)} : V) := rfl
    rw [h1, hFleft b hbr, hFright b hbr,
      coneImage_inverse_right hf hb0 (forcingRegular_inter hbr hb0r)
        (fun z hz ↦ (mem_inter_iff.mp hz).2)]
    by_cases hn0B : n0 ∈ booleanConditions P R
    · rw [coneImage_inverse_right hg hn0B (forcingRegular_inter hbr hn0r)
        (fun z hz ↦ (mem_inter_iff.mp hz).2)]
      exact (hsplit b hbr).symm
    · have hbn : b ∩ n0 = (∅ : V) := by
        have hn00 : n0 = (∅ : V) := by
          by_contra hne
          obtain ⟨q, hq⟩ : ∃ q, q ∈ n0 := by
            by_contra hno
            exact hne (mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hno,
              fun hz ↦ absurd hz not_mem_empty⟩))
          exact hn0B ((mem_booleanConditions_iff P R n0).mpr ⟨hn0r, q, hq⟩)
        apply mem_ext
        intro z
        simp only [mem_inter_iff, hn00, not_mem_empty, and_false]
      rw [hbn, coneImage_empty, coneImage_empty]
      have := hsplit b hbr
      rw [hbn] at this
      exact this.symm
  have hFG : ∀ c ∈ booleanConditions P R, F (G c) = c := by
    intro c hc
    have hcr := ((mem_booleanConditions_iff P R c).mp hc).1
    have h1 : F (G c) = regularJoin P R
        ({coneImage P R b0 f (G c ∩ b0), coneImage P R n0 g (G c ∩ n0)} : V) := rfl
    rw [h1, hGleft c hcr, hGright c hcr,
      coneImage_inverse_left hf hc0 (forcingRegular_inter hcr hc0r)
        (fun z hz ↦ (mem_inter_iff.mp hz).2)]
    by_cases hm0B : m0 ∈ booleanConditions P R
    · rw [coneImage_inverse_left hg hm0B (forcingRegular_inter hcr hm0r)
        (fun z hz ↦ (mem_inter_iff.mp hz).2)]
      exact (hsplitc c hcr).symm
    · have hcm : c ∩ m0 = (∅ : V) := by
        have hm00 : m0 = (∅ : V) := by
          by_contra hne
          obtain ⟨q, hq⟩ : ∃ q, q ∈ m0 := by
            by_contra hno
            exact hne (mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hno,
              fun hz ↦ absurd hz not_mem_empty⟩))
          exact hm0B ((mem_booleanConditions_iff P R m0).mpr ⟨hm0r, q, hq⟩)
        apply mem_ext
        intro z
        simp only [mem_inter_iff, hm00, not_mem_empty, and_false]
      rw [hcm, coneImage_empty, coneImage_empty]
      have := hsplitc c hcr
      rw [hcm] at this
      exact this.symm
  -- the order
  have hmonoF : ∀ b : V, IsForcingRegular P R b → ∀ c : V, IsForcingRegular P R c →
      b ⊆ c → F b ⊆ F c := by
    intro b hb c hc hbc
    refine regularJoin_pair_subset hR (hFreg c hc) ?_ ?_
    · exact subset_trans (coneImage_mono (fun z hz ↦ mem_inter_iff.mpr
        ⟨hbc z (mem_inter_iff.mp hz).1, (mem_inter_iff.mp hz).2⟩))
        (subset_regularJoin_pair_left hR (hleft c hc).1)
    · exact subset_trans (coneImage_mono (fun z hz ↦ mem_inter_iff.mpr
        ⟨hbc z (mem_inter_iff.mp hz).1, (mem_inter_iff.mp hz).2⟩))
        (subset_regularJoin_pair_right hR (hright c hc).1)
  have hmonoG : ∀ b : V, IsForcingRegular P R b → ∀ c : V, IsForcingRegular P R c →
      b ⊆ c → G b ⊆ G c := by
    intro b hb c hc hbc
    refine regularJoin_pair_subset hR (hGreg c hc) ?_ ?_
    · exact subset_trans (coneImage_mono (fun z hz ↦ mem_inter_iff.mpr
        ⟨hbc z (mem_inter_iff.mp hz).1, (mem_inter_iff.mp hz).2⟩))
        (subset_regularJoin_pair_left hR (hleft' c hc).1)
    · exact subset_trans (coneImage_mono (fun z hz ↦ mem_inter_iff.mpr
        ⟨hbc z (mem_inter_iff.mp hz).1, (mem_inter_iff.mp hz).2⟩))
        (subset_regularJoin_pair_right hR (hright' c hc).1)
  have hord : ∀ b ∈ booleanConditions P R, ∀ c ∈ booleanConditions P R,
      ⟨b, c⟩ₖ ∈ booleanOrder P R ↔ ⟨F b, F c⟩ₖ ∈ booleanOrder P R := by
    intro b hb c hc
    have hbr := ((mem_booleanConditions_iff P R b).mp hb).1
    have hcr := ((mem_booleanConditions_iff P R c).mp hc).1
    rw [kpair_mem_booleanOrder_iff, kpair_mem_booleanOrder_iff]
    simp only [hb, hc, hFB b hb, hFB c hc, true_and]
    refine ⟨hmonoF b hbr c hcr, fun h ↦ ?_⟩
    have h1 := hmonoG (F b) (hFreg b hbr) (F c) (hFreg c hcr) h
    rw [hGF b hb, hGF c hc] at h1
    exact h1
  refine ⟨definableGraph (booleanConditions P R) F hFdef,
    (mem_forcingAutomorphisms_iff _ _ _).mpr
      (isForcingIsomorphism_of_inverse F G hFdef hFB hGB hGF hFG hord), ?_, ?_⟩
  · intro b hb hbb0
    have hbr := ((mem_booleanConditions_iff P R b).mp hb).1
    rw [value_definableGraph _ _ _ hb, hFleft b hbr]
    exact coneImage_value hf (mem_forcingCone_boolean_of_nonempty hb0
      (forcingRegular_inter hbr hb0r) (fun z hz ↦ (mem_inter_iff.mp hz).2)
      ((mem_booleanConditions_iff P R _).mp hbb0).2)
  · intro a ha hfa hga
    have har := ((mem_booleanConditions_iff P R a).mp ha).1
    have hFa : F a = regularJoin P R
        ({coneImage P R b0 f (a ∩ b0), coneImage P R n0 g (a ∩ n0)} : V) := rfl
    rw [value_definableGraph _ _ _ ha, hFa, hfa, hga]
    exact (hsplitc a har).symm


/-! ### The stabilizer clause -/

theorem coneRegular_boolean_empty (P R : V) :
    coneRegular (booleanConditions P R) (booleanOrder P R) (∅ : V) = (∅ : V) := by
  apply mem_ext
  intro q
  simp only [not_mem_empty, iff_false]
  intro hq
  obtain ⟨hqB, hh⟩ := mem_coneRegular_iff.mp hq
  obtain ⟨s, -, hs0, -⟩ := hh q hqB
    ((kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hqB, hqB, subset_refl _⟩)
  obtain ⟨-, -, hsub⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hs0
  obtain ⟨-, p, hp⟩ := (mem_booleanConditions_iff _ _ _).mp
    ((kpair_mem_booleanOrder_iff _ _ _ _).mp hs0).1
  exact not_mem_empty (hsub p hp)

/-- An automorphism of the Boolean completion fixing every base support value lies in the forced
stabilizer of a set of saturated nice names. -/
theorem mem_forcedStabilizer_of_fixes_supportValuesBase {P R K E Θ : V}
    (hP : ∃ p, p ∈ P) (hR : IsForcingPreorder P R)
    (hΘ : IsForcingAutomorphism (booleanConditions P R) (booleanOrder P R) Θ)
    (hE : ∀ σ ∈ E, IsSaturatedNiceName (booleanConditions P R) (booleanOrder P R) P K σ)
    (hfix : ∀ a ∈ supportValuesBase P R P K E, a ∈ booleanConditions P R → Θ ‘ a = a) :
    Θ ∈ forcedStabilizer (booleanConditions P R) (booleanOrder P R)
      (forcingAutomorphisms (booleanConditions P R) (booleanOrder P R)) E := by
  rw [forcedStabilizer_eq_imageStabilizer (booleanOrder_poset P R)
    (forcingAutomorphisms_group _ _) (booleanOrder_top hP) hE]
  refine (mem_imageStabilizer_iff _ _ _).mpr
    ⟨(mem_forcingAutomorphisms_iff _ _ _).mpr hΘ, fun A hA ↦ ?_⟩
  obtain ⟨k, hk, σ, hσ, rfl⟩ := (mem_supportValues_iff _ _ _ _ _ _).mp hA
  rw [← coneRegular_booleanValueBase_eq hR]
  by_cases haB : booleanValueBase P R (checkName P k) σ ∈ booleanConditions P R
  · rw [imageAction_coneRegular hΘ haB,
      hfix _ (booleanValueBase_mem_supportValuesBase hk hσ) haB]
  · have ha0 : booleanValueBase P R (checkName P k) σ = (∅ : V) := by
      by_contra hne
      obtain ⟨q, hq⟩ : ∃ q, q ∈ booleanValueBase P R (checkName P k) σ := by
        by_contra hno
        exact hne (mem_ext (fun z ↦ ⟨fun hz ↦ absurd ⟨z, hz⟩ hno,
          fun hz ↦ absurd hz not_mem_empty⟩))
      exact haB ((mem_booleanConditions_iff P R _).mpr ⟨booleanValueBase_regular hR _ _, q, hq⟩)
    rw [ha0, coneRegular_boolean_empty, imageAction_empty]

/-- Karagila-Schilhan Lemma 9.3, lifting step with the stabilizer clause. If in addition the two
cone isomorphisms fix every base support value of `E`, the automorphism they lift to lies in the
forced stabilizer of `E`. -/
theorem exists_forcedStabilizer_automorphism_of_cone_isomorphisms {P R b0 c0 f g K E : V}
    (hP : ∃ p, p ∈ P) (hR : IsForcingPreorder P R)
    (hb0 : b0 ∈ booleanConditions P R) (hc0 : c0 ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (forcingCone (booleanConditions P R) (booleanOrder P R) b0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b0))
      (forcingCone (booleanConditions P R) (booleanOrder P R) c0)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) c0)) f)
    (hg : IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R b0))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R b0)))
      (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R c0))
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) (forcingNegation P R c0))) g)
    (hE : ∀ σ ∈ E, IsSaturatedNiceName (booleanConditions P R) (booleanOrder P R) P K σ)
    (hfix : ∀ a ∈ supportValuesBase P R P K E,
      coneImage P R b0 f (a ∩ b0) = a ∩ c0 ∧
        coneImage P R (forcingNegation P R b0) g (a ∩ forcingNegation P R b0) =
          a ∩ forcingNegation P R c0) :
    ∃ Θ ∈ forcedStabilizer (booleanConditions P R) (booleanOrder P R)
      (forcingAutomorphisms (booleanConditions P R) (booleanOrder P R)) E,
      ∀ b ∈ booleanConditions P R, b ∩ b0 ∈ booleanConditions P R →
        (Θ ‘ b) ∩ c0 = f ‘ (b ∩ b0) := by
  obtain ⟨Θ, hΘmem, hΘval, hΘfix⟩ :=
    exists_booleanAutomorphism_of_cone_isomorphisms hR hb0 hc0 hf hg
  refine ⟨Θ, mem_forcedStabilizer_of_fixes_supportValuesBase hP hR
    ((mem_forcingAutomorphisms_iff _ _ _).mp hΘmem) hE (fun a ha haB ↦ ?_), hΘval⟩
  exact hΘfix a haB (hfix a ha).1 (hfix a ha).2

/-- The Levy instance: for the collapse `Coll(ω, <κ)` and the Solovay parameter set `ω × ω`. -/
theorem levy_exists_forcedStabilizer_automorphism_of_cone_isomorphisms
    {κ b0 c0 f g E : V}
    (hb0 : b0 ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hc0 : c0 ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hf : IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) b0)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) b0))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) c0)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) c0)) f)
    (hg : IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingNegation (levyCollapse κ) (levyOrder κ) b0))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ) b0)))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingNegation (levyCollapse κ) (levyOrder κ) c0))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ) c0))) g)
    (hE : ∀ σ ∈ E, IsSaturatedNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ)
    (hfix : ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
        ((ω : V) ×ˢ (ω : V)) E,
      coneImage (levyCollapse κ) (levyOrder κ) b0 f (a ∩ b0) = a ∩ c0 ∧
        coneImage (levyCollapse κ) (levyOrder κ)
            (forcingNegation (levyCollapse κ) (levyOrder κ) b0) g
            (a ∩ forcingNegation (levyCollapse κ) (levyOrder κ) b0) =
          a ∩ forcingNegation (levyCollapse κ) (levyOrder κ) c0) :
    ∃ Θ ∈ forcedStabilizer (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ))
      (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))) E,
      ∀ b ∈ booleanConditions (levyCollapse κ) (levyOrder κ),
        b ∩ b0 ∈ booleanConditions (levyCollapse κ) (levyOrder κ) →
        (Θ ‘ b) ∩ c0 = f ‘ (b ∩ b0) :=
  exists_forcedStabilizer_automorphism_of_cone_isomorphisms
    ⟨∅, empty_mem_levyCollapse κ⟩ (levyCollapse_poset κ).1 hb0 hc0 hf hg hE hfix

end ZFVP
