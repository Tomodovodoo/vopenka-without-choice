import ZFVP.ModelTheory.CountableCodeDefinable
import ZFVP.ModelTheory.GroundRealsHODClosure
import ZFVP.ModelTheory.SolovayLocalization
import ZFVP.ModelTheory.LevyCollapseOmegaOne
import ZFVP.SetTheory.LevyCollapseFull
import ZFVP.SetTheory.MeasurableStrongLimit

/-! Every set of a bounded stage `V[G_ξ]` of the Levy collapse, `ξ < κ`, is definable in `V[G]`
from ground sets, reals and ordinals.

Two steps. First the cut `G_ξ` of the generic set is itself definable from a real: the ground
condition set `levyCollapse ξ` sits inside a transitive ground set of size below `κ`, so its check
has countable transitive closure in `V[G]` and the subset `G_ξ` gets a countable code. Second an
element of `V[G_ξ]` is the value of a checked name at `G_ξ`, and the name evaluation recursion is
written out as a first-order formula whose parameters are `G_ξ` and one check. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### A small transitive ground set holding the conditions of a bounded stage -/

theorem power_transitive {X : V} (hX : IsTransitive X) : IsTransitive (℘ X) :=
  ⟨fun y hy z hz ↦ mem_power_iff.mpr (hX.transitive z (mem_power_iff.mp hy z hz))⟩

theorem subset_power_of_transitive {X : V} (hX : IsTransitive X) : X ⊆ ℘ X :=
  fun x hx ↦ mem_power_iff.mpr (hX.transitive x hx)

/-- A Kuratowski pair of members of `X` lies two power sets above `X`. -/
theorem kpair_mem_power_power {X a b : V} (ha : a ∈ X) (hb : b ∈ X) :
    (⟨a, b⟩ₖ : V) ∈ ℘ (℘ X) := by
  have hsing : ({a} : V) ∈ ℘ X :=
    mem_power_iff.mpr (fun w hw ↦ by rw [mem_singleton_iff.mp hw]; exact ha)
  have hpair : ({a, b} : V) ∈ ℘ X := by
    refine mem_power_iff.mpr (fun w hw ↦ ?_)
    rcases mem_insert.mp hw with rfl | hw
    · exact ha
    · rw [mem_singleton_iff.mp hw]; exact hb
  refine mem_power_iff.mpr (fun u hu ↦ ?_)
  rw [show (⟨a, b⟩ₖ : V) = ({{a}, {a, b}} : V) from rfl] at hu
  rcases mem_insert.mp hu with rfl | hu
  · exact hsing
  · rw [mem_singleton_iff.mp hu]; exact hpair

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ)

include hAC hU hc hω in
/-- For `ξ < κ` there is a transitive set of size below `κ` having `levyCollapse ξ` as a member. -/
theorem exists_small_transitive_of_levyCollapse {ξ : V} (hξ : ξ ∈ κ) :
    ∃ T : V, IsTransitive T ∧ levyCollapse ξ ∈ T ∧ ∃ μ ∈ κ, T ≤# μ := by
  -- a common ordinal bound `lam` for `ω` and `ξ`
  haveI : IsOrdinal ξ := IsOrdinal.of_mem hξ
  obtain ⟨lam, hlam, hωlam, hξlam⟩ : ∃ lam ∈ κ, (ω : V) ⊆ lam ∧ ξ ⊆ lam := by
    rcases IsOrdinal.subset_or_supset (α := (ω : V)) (β := ξ) with h | h
    · exact ⟨ξ, hξ, h, fun x hx ↦ hx⟩
    · exact ⟨(ω : V), hω, fun x hx ↦ hx, h⟩
  haveI : IsOrdinal lam := IsOrdinal.of_mem hlam
  have t0 : IsTransitive lam := IsOrdinal.toIsTransitive
  -- six power sets above `lam`
  set P1 : V := ℘ lam with hP1
  set P2 : V := ℘ P1 with hP2
  set P3 : V := ℘ P2 with hP3
  set P4 : V := ℘ P3 with hP4
  set P5 : V := ℘ P4 with hP5
  set P6 : V := ℘ P5 with hP6
  have t1 : IsTransitive P1 := power_transitive t0
  have t2 : IsTransitive P2 := power_transitive t1
  have t3 : IsTransitive P3 := power_transitive t2
  have t4 : IsTransitive P4 := power_transitive t3
  have t5 : IsTransitive P5 := power_transitive t4
  have t6 : IsTransitive P6 := power_transitive t5
  have s0 : lam ⊆ P1 := subset_power_of_transitive t0
  have s1 : P1 ⊆ P2 := subset_power_of_transitive t1
  -- every condition of the stage is a subset of `P4`
  have hlamP2 : lam ⊆ P2 := fun x hx ↦ s1 x (s0 x hx)
  have hprod : ((ω : V) ×ˢ ξ) ×ˢ ξ ⊆ P4 := by
    intro z hz
    obtain ⟨u, hu, β, hβ, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨n, hn, α, hα, rfl⟩ := mem_prod_iff.mp hu
    have hnα : (⟨n, α⟩ₖ : V) ∈ P2 :=
      kpair_mem_power_power (hωlam n hn) (hξlam α hα)
    exact kpair_mem_power_power hnα (hlamP2 β (hξlam β hβ))
  have hmem : levyCollapse ξ ∈ P6 := by
    refine mem_power_iff.mpr (fun p hp ↦ ?_)
    refine mem_power_iff.mpr (fun z hz ↦ ?_)
    exact hprod z (mem_power_iff.mp (levyCollapse_subset_power ξ p hp) z hz)
  -- and `P6` is small because `κ` is a strong limit
  obtain ⟨ν1, hν1, hc1⟩ := power_small_of_measurable hAC hU hc hlam (CardLE.refl lam)
  obtain ⟨ν2, hν2, hc2⟩ := power_small_of_measurable hAC hU hc hν1 hc1
  obtain ⟨ν3, hν3, hc3⟩ := power_small_of_measurable hAC hU hc hν2 hc2
  obtain ⟨ν4, hν4, hc4⟩ := power_small_of_measurable hAC hU hc hν3 hc3
  obtain ⟨ν5, hν5, hc5⟩ := power_small_of_measurable hAC hU hc hν4 hc4
  obtain ⟨ν6, hν6, hc6⟩ := power_small_of_measurable hAC hU hc hν5 hc5
  exact ⟨P6, t6, hmem, ν6, hν6, hc6⟩

variable {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω in
/-- The check of the conditions of a bounded stage has countable transitive closure in `V[G]`. -/
theorem levy_stage_check_transitive_of_groundClosure_countable {ξ : V} (hξ : ξ ∈ κ) :
    IsInternallyCountable (transitiveClosure
      ({(levyContext κ hG).check (levyCollapse ξ)} : (levyContext κ hG).Model)) := by
  obtain ⟨T, hT, hmem, μ, hμ, hTμ⟩ := exists_small_transitive_of_levyCollapse hAC hU hc hω hξ
  have hcount : IsInternallyCountable ((levyContext κ hG).check T) :=
    internallyCountable_of_cardLE (levy_check_countable hG hμ)
      ((levyContext κ hG).checkEmbedding.map_cardLE hTμ)
  refine internallyCountable_subset hcount (transitiveClosure_minimal _ _ ?_
    (ForcingContext.check_transitive_of_ground hT))
  rw [singleton_subset_iff_mem]
  exact ((levyContext κ hG).check_mem_iff _ _).mpr hmem

include hAC hU hc hω in
/-- The cut of the generic set at a bounded stage is definable from ground sets, reals and
ordinals: it is a subset of a checked set with countable transitive closure. -/
theorem levy_subgeneric_groundRealDefinable {ξ : V} (hξ : ξ ∈ κ) :
    (levyContext κ hG).IsGroundRealDefinable
      ((levyContext κ hG).genericSet ∩ (levyContext κ hG).check (levyCollapse ξ)) :=
  ForcingContext.groundRealDefinable_of_countable_transitiveClosure_subset
    (fun _ hx ↦ (mem_inter_iff.mp hx).2)
    (levy_stage_check_transitive_of_groundClosure_countable hAC hU hc hω hG hξ)

end

/-! ### Composing a definable parameter with a Solovay parameter -/

/-- `∃ w, (∀ y, y ∈ w ↔ φ(y, v)) ∧ ψ(b, w, c)`, with free variables `b, c, v`. -/
def definedFrom₂ {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (ψ : SetTheorySemisentence 3) :
    SetTheorySemisentence (n + 2) :=
  ∃¹ ((∀¹ (((∼(memAtom.subst ![#0, #1])) ⋎
        (φ.subst (#0 :> fun i ↦ #i.succ.succ.succ.succ))) ⋏
      ((∼(φ.subst (#0 :> fun i ↦ #i.succ.succ.succ.succ))) ⋎
        (memAtom.subst ![#0, #1])))) ⋏
    (ψ.subst ![#1, #0, #2]))

theorem eval_definedFrom₂ {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (ψ : SetTheorySemisentence 3) (b c : V) (v : Fin n → V) :
    (definedFrom₂ φ ψ).Evalb (b :> c :> v) ↔
      ∃ w : V, (∀ y, y ∈ w ↔ φ.Evalb (y :> v)) ∧ ψ.Evalb ![b, w, c] := by
  simp [definedFrom₂, memAtom, Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton]
  constructor
  · rintro ⟨w, hw, hψ⟩
    exact ⟨w, fun y ↦ ⟨fun hy ↦ (hw y).1.resolve_left (not_not.mpr hy),
      fun hφ ↦ (hw y).2.resolve_left (not_not.mpr hφ)⟩, hψ⟩
  · rintro ⟨w, hw, hψ⟩
    refine ⟨w, fun y ↦ ⟨?_, ?_⟩, hψ⟩
    · by_cases hy : y ∈ w
      · exact Or.inr ((hw y).mp hy)
      · exact Or.inl hy
    · by_cases hφ : φ.Evalb (y :> v)
      · exact Or.inr ((hw y).mpr hφ)
      · exact Or.inl hφ

namespace ForcingContext

variable {A : ForcingContext V}

/-- A set defined from one definable set together with one allowed parameter is definable. -/
theorem groundRealDefinable_of_definable_from₂ {x c C : A.Model}
    (hx : A.IsGroundRealDefinable x) (hcp : A.IsSolovayParameter c)
    (ψ : SetTheorySemisentence 3) (hC : ∀ b, b ∈ C ↔ ψ.Evalb ![b, x, c]) :
    A.IsGroundRealDefinable C := by
  obtain ⟨n, φ, v, hv, hdef⟩ := hx
  refine ⟨n + 1, definedFrom₂ φ ψ, c :> v, ?_, fun b ↦ ?_⟩
  · intro i
    refine Fin.cases hcp (fun j ↦ hv j) i
  · rw [show (b :> c :> v) = (b :> (c :> v)) from rfl] at *
    rw [eval_definedFrom₂, hC]
    constructor
    · intro h
      exact ⟨x, fun y ↦ hdef y, h⟩
    · rintro ⟨w, hw, hψ⟩
      have hwx : w = x := by
        apply mem_ext
        intro y
        rw [hw y, hdef y]
      rw [hwx] at hψ
      exact hψ

end ForcingContext

/-! ### The name evaluation recursion as a formula -/

/-- `b ∈ nameValue g c`, where the parameter `a` is the pair of a subname-closed set `N`
containing `c` and of `c` itself. The recursion table over `N` is quantified out. -/
def nameEvalFormula : SetTheorySemisentence 3 :=
  f“b g a. ∃ N, ∃ c, a = !kpair.dfn N c ∧ ∃ F, !IsFunction.dfn F ∧ !domain.dfn F = N ∧
    (∀ σ ∈ N, ∀ z, (z ∈ !value.dfn F σ ↔
      ∃ ν, ∃ p ∈ g, !kpair.dfn ν p ∈ σ ∧ z = !value.dfn F ν)) ∧
    b ∈ !value.dfn F c”

theorem eval_nameEvalFormula (b g a : V) :
    nameEvalFormula.Evalb ![b, g, a] ↔
      ∃ N c : V, a = ⟨N, c⟩ₖ ∧ ∃ F : V, IsFunction F ∧ domain F = N ∧
        (∀ σ ∈ N, ∀ z, (z ∈ F ‘ σ ↔ ∃ ν : V, ∃ p ∈ g, ⟨ν, p⟩ₖ ∈ σ ∧ z = F ‘ ν)) ∧
        b ∈ F ‘ c := by
  simp [nameEvalFormula]

/-- The recursion clause of `nameEvalFormula` says exactly that `F` is the name evaluation table
over the subname-closed set `N`. -/
theorem isSubnameRecursion_iff_values {g N F : V} (hN : IsSubnameClosed N) (hF : IsFunction F)
    (hdom : domain F = N) :
    IsSubnameRecursion N (nameValueStep g) F ↔
      ∀ σ ∈ N, ∀ z, (z ∈ F ‘ σ ↔ ∃ ν : V, ∃ p ∈ g, ⟨ν, p⟩ₖ ∈ σ ∧ z = F ‘ ν) := by
  haveI : IsFunction F := hF
  have key : ∀ σ ∈ N, ∀ z : V, z ∈ nameValueStep g σ (F ↾ (domain σ)) ↔
      ∃ ν : V, ∃ p ∈ g, ⟨ν, p⟩ₖ ∈ σ ∧ z = F ‘ ν := by
    intro σ hσ z
    rw [mem_nameValueStep_iff]
    constructor
    · rintro ⟨ν, p, hp, hνp, he⟩
      have hνd : ν ∈ domain σ := mem_domain_of_kpair_mem hνp
      have hνF : ν ∈ domain F := by rw [hdom]; exact hN σ hσ ν hνd
      exact ⟨ν, p, hp, hνp, by rwa [value_restrict hνF hνd] at he⟩
    · rintro ⟨ν, p, hp, hνp, he⟩
      have hνd : ν ∈ domain σ := mem_domain_of_kpair_mem hνp
      have hνF : ν ∈ domain F := by rw [hdom]; exact hN σ hσ ν hνd
      exact ⟨ν, p, hp, hνp, by rwa [value_restrict hνF hνd]⟩
  constructor
  · intro h σ hσ z
    rw [h.2.2 σ hσ]
    exact key σ hσ z
  · intro h
    refine ⟨hF, hdom, fun σ hσ ↦ ?_⟩
    apply mem_ext
    intro z
    rw [h σ hσ z, key σ hσ z]

/-- Any name evaluation table over a subname-closed set computes `nameValue` at its points. -/
theorem value_eq_nameValue_of_subnameRecursion {g N F c : V} (hN : IsSubnameClosed N)
    (hcN : c ∈ N) (hF : IsSubnameRecursion N (nameValueStep g) F) : F ‘ c = nameValue g c := by
  have ht : IsSubnameRecursion (nameClosure c) (nameValueStep g)
      (subnameRecursionTable (nameValueStep g) (by definability) c) :=
    subnameRecursionTable_spec _ _ c
  have he : nameValue g c = (subnameRecursionTable (nameValueStep g) (by definability) c) ‘ c := rfl
  rw [he]
  exact subnameRecursion_coherent hN (nameClosure_closed c) hF ht c hcN (mem_nameClosure_self c)

/-- Membership in the value of a name is defined by `nameEvalFormula` from the filter and the pair
of a subname-closed set containing the name and the name. -/
theorem mem_nameValue_iff_nameEval {g N c : V} (hN : IsSubnameClosed N) (hcN : c ∈ N) (b : V) :
    b ∈ nameValue g c ↔ nameEvalFormula.Evalb ![b, g, ⟨N, c⟩ₖ] := by
  rw [eval_nameEvalFormula]
  constructor
  · intro hb
    obtain ⟨F, hF⟩ := subnameRecursion_exists hN (nameValueStep g) (by definability)
    refine ⟨N, c, rfl, F, hF.1, hF.2.1, ?_, ?_⟩
    · exact (isSubnameRecursion_iff_values hN hF.1 hF.2.1).mp hF
    · rwa [value_eq_nameValue_of_subnameRecursion hN hcN hF]
  · rintro ⟨N', c', hpair, F, hfun, hdom, hrec, hb⟩
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hpair
    have hF : IsSubnameRecursion N (nameValueStep g) F :=
      (isSubnameRecursion_iff_values hN hfun hdom).mpr hrec
    rwa [value_eq_nameValue_of_subnameRecursion hN hcN hF] at hb

/-! ### Sets of a bounded stage are definable -/

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω in
/-- Every set of a bounded stage `V[G_ξ]`, `ξ < κ`, is definable in `V[G]` from ground sets, reals
and ordinals. -/
theorem inLevySubmodel_groundRealDefinable {ξ : V} [IsOrdinal ξ] (hξ : ξ ∈ κ)
    {x : (levyContext κ hG).Model}
    (hx : InLevySubmodel ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG x) :
    (levyContext κ hG).IsGroundRealDefinable x := by
  have hξ' : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξ
  obtain ⟨τ, rfl⟩ := (inLevySubmodel_iff ξ hξ' hG x).mp hx
  set A := levyContext κ hG with hA
  set T : V := transitiveClosure ({τ.val} : V) with hT
  set N : A.Model := A.check T with hN
  set c : A.Model := A.check τ.val with hc'
  have hτT : τ.val ∈ T := subset_transitiveClosure _ _ (mem_singleton_iff.mpr rfl)
  have hNclosed : IsSubnameClosed N :=
    transitive_subnameClosed (ForcingContext.check_transitive_of_ground (transitiveClosure_transitive _))
  have hcN : c ∈ N := (A.check_mem_iff _ _).mpr hτT
  have hpair : A.check (⟨T, τ.val⟩ₖ : V) = (⟨N, c⟩ₖ : A.Model) := A.checkEmbedding.map_kpair T τ.val
  have hval : A.ofName ⟨τ.val, τ.property.mono (levyCollapse_mono hξ')⟩ =
      nameValue (A.genericSet ∩ A.check (levyCollapse ξ)) c := by
    rw [← levySubRealization_value_ofName ξ hξ' hG τ]
    rfl
  refine ForcingContext.groundRealDefinable_of_definable_from₂
    (levy_subgeneric_groundRealDefinable hAC hU hc hω hG hξ)
    (Or.inl ⟨(⟨T, τ.val⟩ₖ : V), hpair.symm⟩) nameEvalFormula (fun b ↦ ?_)
  rw [hval]
  exact mem_nameValue_iff_nameEval hNclosed hcN b

include hAC hU hc hω in
/-- A localized set of `V[G]` is definable from ground sets, reals and ordinals. -/
theorem groundRealDefinable_of_isLocalized {x : (levyContext κ hG).Model}
    (hx : IsLocalized hG x) : (levyContext κ hG).IsGroundRealDefinable x := by
  obtain ⟨ξ, hξ, hmem⟩ := hx
  haveI : IsOrdinal ξ := IsOrdinal.of_mem hξ
  exact inLevySubmodel_groundRealDefinable hAC hU hc hω hG hξ hmem

end

end ZFVP
