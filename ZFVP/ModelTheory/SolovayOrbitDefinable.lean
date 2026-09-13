import ZFVP.ModelTheory.SubalgebraModelDefinable
import ZFVP.ModelTheory.SolovaySymmetricSupport
import ZFVP.ModelTheory.SolovaySymmetricReals
import ZFVP.ModelTheory.SolovayCorollaryFinal
import ZFVP.SetTheory.EndExtensionLevyCollapse
import ZFVP.ModelTheory.SolovayFactorHomogeneity

/-! The orbit union of Karagila and Schilhan, Proposition 9.4.

Let `ż` be a symmetric name whose forced stabilizer over a finite set `E` of names of reals is
contained in its own stabilizer. The paper defines

  `z = ⋃ { ż^H : H a generic filter over the ground model lying in the extension, giving the same
                 extension as `G`, with `ẋ^H = ẋ^G` for every `ẋ ∈ E }`,

and shows `z = ż^G`. The point of the definition is that its parameters are ground sets and the
finitely many reals `ẋ^G`, so `ż^G` is definable from ground sets, reals and ordinals.

This module builds the set `z` inside the extension and proves that it is so definable, that it
contains `ż^G`, and that it is contained in `ż^G` once the transfer statement of the paper's
Lemma 9.3 is assumed.

The filters `H` are described inside the extension by the antichain-generic clauses already used
by `familyTraceFormula`, together with the top of the algebra and the side condition that every
set of the extension is the value at `H` of a name in the ground model. That side condition is
the paper's `V[H] = V[G]`: the ground model is a definable class of the extension, and the class
formula is carried through the development as the parameter `Pf` with its parameter `p`, so the
condition costs no parameter beyond ground sets. For the Levy collapse `Pf` is `groundFormula`
and `p` is `solovayParam`.

The valuation `ż^H` is put into the defining formula by quantifying over a name evaluation table
on a subname-closed checked set covering `ż` and all the names of `E` at once, which is the same
device `nameEvalFormula` uses for one name. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ### The defining formula -/

/-- `b` lies in the value at some subset `H` of `Pc` of the name `ct`, computed by a name
evaluation table on the subname-closed set `N`. This bounds the orbit union. -/
def orbitBoundFormula : SetTheorySemisentence 4 :=
  f“b Pc N ct. ∃ H, H ⊆ Pc ∧ ∃ F, !IsFunction.dfn F ∧ !domain.dfn F = N ∧
    (∀ σ ∈ N, ∀ z, (z ∈ !value.dfn F σ ↔
      ∃ ν, ∃ p ∈ H, !kpair.dfn ν p ∈ σ ∧ z = !value.dfn F ν)) ∧
    b ∈ !value.dfn F ct”

/-- `b` lies in the orbit union: `b ∈ Q` and there are a filter `H` and a name evaluation table
`F` on the subname-closed set `N` such that `H` is an antichain-generic ultrafilter on `Reg`
relative to `MA` containing the top `one`, the value at `H` of the `i`-th name of the support
sequence `cs` is the `i`-th section of `W` for every `i ∈ ck`, and `b` lies in the value at `H`
of the name `ct`. -/
def solovayOrbitFormula (Pf : SetTheorySemisentence 2) : SetTheorySemisentence 11 :=
  f“b Q Reg MA one N ct cs ck W p. b ∈ Q ∧ ∃ H, ∃ F,
    (∀ u ∈ H, u ∈ Reg) ∧
    (∀ u ∈ H, ∀ u' ∈ Reg, u ⊆ u' → u' ∈ H) ∧
    (∀ u ∈ H, ∀ u' ∈ H, !inter.dfn u u' ∈ H) ∧
    (∀ u ∈ H, ∃ z, z ∈ u) ∧
    (∀ Y ∈ MA, ∃ a ∈ Y, a ∈ H) ∧
    one ∈ H ∧
    (∀ x, ∃ y, !Pf y p ∧ ∃ Nx, (∀ t ∈ Nx, !domain.dfn t ⊆ Nx) ∧ y ∈ Nx ∧
      ∃ Fx, !IsFunction.dfn Fx ∧ !domain.dfn Fx = Nx ∧
        (∀ t ∈ Nx, ∀ w, (w ∈ !value.dfn Fx t ↔
          ∃ v, ∃ q ∈ H, !kpair.dfn v q ∈ t ∧ w = !value.dfn Fx v)) ∧
        x = !value.dfn Fx y) ∧
    !IsFunction.dfn F ∧ !domain.dfn F = N ∧
    (∀ σ ∈ N, ∀ z, (z ∈ !value.dfn F σ ↔
      ∃ ν, ∃ r ∈ H, !kpair.dfn ν r ∈ σ ∧ z = !value.dfn F ν)) ∧
    (∀ i ∈ ck, ∀ z, (z ∈ !value.dfn F (!value.dfn cs i) ↔ !kpair.dfn i z ∈ W)) ∧
    b ∈ !value.dfn F ct”

section

variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_orbitBoundFormula_raw (b Pc N ct : M) :
    orbitBoundFormula.Evalb ![b, Pc, N, ct] ↔
      ∃ H : M, H ⊆ Pc ∧ ∃ F : M, IsFunction F ∧ domain F = N ∧
        (∀ σ ∈ N, ∀ z, (z ∈ F ‘ σ ↔ ∃ ν : M, ∃ p ∈ H, (⟨ν, p⟩ₖ : M) ∈ σ ∧ z = F ‘ ν)) ∧
        b ∈ F ‘ ct := by
  simp [orbitBoundFormula]

/-- The bounding formula says that `b` lies in the value of `ct` at some subset of `Pc`. -/
theorem eval_orbitBoundFormula {N : M} (hN : IsSubnameClosed N) {ct : M} (hct : ct ∈ N)
    (b Pc : M) :
    orbitBoundFormula.Evalb ![b, Pc, N, ct] ↔ ∃ H : M, H ⊆ Pc ∧ b ∈ nameValue H ct := by
  rw [eval_orbitBoundFormula_raw]
  constructor
  · rintro ⟨H, hHP, F, hfun, hdom, hrec, hb⟩
    have hF : IsSubnameRecursion N (nameValueStep H) F :=
      (isSubnameRecursion_iff_values hN hfun hdom).mpr hrec
    exact ⟨H, hHP, by rwa [← value_eq_nameValue_of_subnameRecursion hN hct hF]⟩
  · rintro ⟨H, hHP, hb⟩
    obtain ⟨F, hF⟩ := subnameRecursion_exists hN (nameValueStep H) (by definability)
    exact ⟨H, hHP, F, hF.1, hF.2.1, (isSubnameRecursion_iff_values hN hF.1 hF.2.1).mp hF,
      by rwa [value_eq_nameValue_of_subnameRecursion hN hct hF]⟩

theorem eval_solovayOrbitFormula_raw (Pf : SetTheorySemisentence 2)
    (b Q Reg MA one N ct cs ck W p : M) :
    (solovayOrbitFormula Pf).Evalb ![b, Q, Reg, MA, one, N, ct, cs, ck, W, p] ↔
      b ∈ Q ∧ ∃ H : M, ∃ F : M,
        (∀ u ∈ H, u ∈ Reg) ∧
        (∀ u ∈ H, ∀ u' ∈ Reg, u ⊆ u' → u' ∈ H) ∧
        (∀ u ∈ H, ∀ u' ∈ H, u ∩ u' ∈ H) ∧
        (∀ u ∈ H, ∃ z, z ∈ u) ∧
        (∀ Y ∈ MA, ∃ a ∈ Y, a ∈ H) ∧
        one ∈ H ∧
        (∀ x : M, ∃ y : M, Pf.Evalb ![y, p] ∧ ∃ Nx : M, (∀ t ∈ Nx, domain t ⊆ Nx) ∧ y ∈ Nx ∧
          ∃ Fx : M, IsFunction Fx ∧ domain Fx = Nx ∧
            (∀ t ∈ Nx, ∀ w, (w ∈ Fx ‘ t ↔
              ∃ v : M, ∃ q ∈ H, (⟨v, q⟩ₖ : M) ∈ t ∧ w = Fx ‘ v)) ∧
            x = Fx ‘ y) ∧
        IsFunction F ∧ domain F = N ∧
        (∀ σ ∈ N, ∀ z, (z ∈ F ‘ σ ↔ ∃ ν : M, ∃ r ∈ H, (⟨ν, r⟩ₖ : M) ∈ σ ∧ z = F ‘ ν)) ∧
        (∀ i ∈ ck, ∀ z, (z ∈ F ‘ (cs ‘ i) ↔ (⟨i, z⟩ₖ : M) ∈ W)) ∧
        b ∈ F ‘ ct := by
  simp [solovayOrbitFormula]

/-- Every set of the extension is the value at `H` of a name satisfying `Pf` at `p`. When `Pf`
at `p` defines the ground model, this says that the `H`-extension is the whole universe, which is
the side condition `V[H] = V[G]` of Karagila and Schilhan, Lemma 9.3. -/
def IsFullValuation (Pf : SetTheorySemisentence 2) (p H : M) : Prop :=
  ∀ x : M, ∃ y : M, Pf.Evalb ![y, p] ∧ x = nameValue H y

/-- `H` is an antichain-generic ultrafilter on `Reg` relative to `MA`, contains the top `one`,
gives the whole universe as its valuation of the names satisfying `Pf` at `p`, and its
valuations of the support names `cs ‘ i` are the sections of `W`. -/
def IsOrbitFilter (Pf : SetTheorySemisentence 2) (Reg MA one cs ck W p H : M) : Prop :=
  (∀ u ∈ H, u ∈ Reg) ∧
  (∀ u ∈ H, ∀ u' ∈ Reg, u ⊆ u' → u' ∈ H) ∧
  (∀ u ∈ H, ∀ u' ∈ H, u ∩ u' ∈ H) ∧
  (∀ u ∈ H, ∃ z, z ∈ u) ∧
  (∀ Y ∈ MA, ∃ a ∈ Y, a ∈ H) ∧
  one ∈ H ∧
  IsFullValuation Pf p H ∧
  (∀ i ∈ ck, ∀ z, (z ∈ nameValue H (cs ‘ i) ↔ (⟨i, z⟩ₖ : M) ∈ W))

/-- The raw clause of the formula for the full valuation is the semantic one. -/
theorem isFullValuation_iff (Pf : SetTheorySemisentence 2) (p H : M) :
    (∀ x : M, ∃ y : M, Pf.Evalb ![y, p] ∧ ∃ Nx : M, (∀ t ∈ Nx, domain t ⊆ Nx) ∧ y ∈ Nx ∧
      ∃ Fx : M, IsFunction Fx ∧ domain Fx = Nx ∧
        (∀ t ∈ Nx, ∀ w, (w ∈ Fx ‘ t ↔
          ∃ v : M, ∃ q ∈ H, (⟨v, q⟩ₖ : M) ∈ t ∧ w = Fx ‘ v)) ∧
        x = Fx ‘ y) ↔ IsFullValuation Pf p H := by
  constructor
  · intro h x
    obtain ⟨y, hy, Nx, hNx, hyN, Fx, hfun, hdom, hrec, hx⟩ := h x
    have hF : IsSubnameRecursion Nx (nameValueStep H) Fx :=
      (isSubnameRecursion_iff_values hNx hfun hdom).mpr hrec
    exact ⟨y, hy, by rwa [value_eq_nameValue_of_subnameRecursion hNx hyN hF] at hx⟩
  · intro h x
    obtain ⟨y, hy, hx⟩ := h x
    obtain ⟨Fx, hFx⟩ := subnameRecursion_exists (nameClosure_closed y) (nameValueStep H)
      (by definability)
    refine ⟨y, hy, nameClosure y, nameClosure_closed y, mem_nameClosure_self y, Fx, hFx.1,
      hFx.2.1, (isSubnameRecursion_iff_values (nameClosure_closed y) hFx.1 hFx.2.1).mp hFx, ?_⟩
    rwa [value_eq_nameValue_of_subnameRecursion (nameClosure_closed y)
      (mem_nameClosure_self y) hFx]

/-- The formula says what the orbit union is meant to say, once `N` is subname-closed and holds
the name `ct` and all the support names `cs ‘ i`. -/
theorem eval_solovayOrbitFormula (Pf : SetTheorySemisentence 2) {N : M} (hN : IsSubnameClosed N)
    {ct cs ck : M} (hct : ct ∈ N) (hcs : ∀ i ∈ ck, cs ‘ i ∈ N) (b Q Reg MA one W p : M) :
    (solovayOrbitFormula Pf).Evalb ![b, Q, Reg, MA, one, N, ct, cs, ck, W, p] ↔
      b ∈ Q ∧ ∃ H : M, IsOrbitFilter Pf Reg MA one cs ck W p H ∧ b ∈ nameValue H ct := by
  rw [eval_solovayOrbitFormula_raw]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨H, F, h1, h2, h3, h4, h5, h6, h7, hfun, hdom, hrec, hsupp, hb⟩
    have hF : IsSubnameRecursion N (nameValueStep H) F :=
      (isSubnameRecursion_iff_values hN hfun hdom).mpr hrec
    refine ⟨H, ⟨h1, h2, h3, h4, h5, h6, (isFullValuation_iff Pf p H).mp h7,
      fun i hi z ↦ ?_⟩, ?_⟩
    · rw [← value_eq_nameValue_of_subnameRecursion hN (hcs i hi) hF]
      exact hsupp i hi z
    · rwa [← value_eq_nameValue_of_subnameRecursion hN hct hF]
  · rintro ⟨H, ⟨h1, h2, h3, h4, h5, h6, h7, hsupp⟩, hb⟩
    obtain ⟨F, hF⟩ := subnameRecursion_exists hN (nameValueStep H) (by definability)
    refine ⟨H, F, h1, h2, h3, h4, h5, h6, (isFullValuation_iff Pf p H).mpr h7, hF.1, hF.2.1,
      (isSubnameRecursion_iff_values hN hF.1 hF.2.1).mp hF, fun i hi z ↦ ?_, ?_⟩
    · rw [value_eq_nameValue_of_subnameRecursion hN (hcs i hi) hF]
      exact hsupp i hi z
    · rwa [value_eq_nameValue_of_subnameRecursion hN hct hF]

end

/-! ### Subsets of the check of a countable ground set -/

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable {A : ForcingContext V}

/-- A subset of `Š`, for a ground set `S` carrying a ground injection `F` into `ω`, is definable
from ground sets, reals and ordinals: the real is the image of the subset under the check of the
graph of `F`. This is `groundRealDefinable_of_subset_check_omega_prod` with the pairing code
replaced by an arbitrary ground code. -/
theorem groundRealDefinable_of_subset_check_of_code {S : V} {F : V → V}
    (hF : ℒₛₑₜ-function₁ F) (hFω : ∀ a ∈ S, F a ∈ (ω : V))
    (hFinj : ∀ a ∈ S, ∀ b ∈ S, F a = F b → a = b)
    {x : A.Model} (hx : x ⊆ A.check S) : A.IsGroundRealDefinable x := by
  set g : V := definableGraph S F hF with hg
  set r : A.Model :=
    {n ∈ A.check (ω : V) ; ∃ p ∈ x, (⟨p, n⟩ₖ : A.Model) ∈ A.check g} with hr
  have hrsub : r ⊆ A.check (ω : V) := sep_subset
  have hpairmem : ∀ a ∈ S, (⟨A.check a, A.check (F a)⟩ₖ : A.Model) ∈ A.check g := by
    intro a ha
    rw [← A.check_kpair, A.check_mem_iff]
    exact (mem_definableGraph_iff S F hF _).mpr ⟨a, ha, rfl⟩
  have hpairmem' : ∀ a ∈ S, ∀ n : V, (⟨A.check a, A.check n⟩ₖ : A.Model) ∈ A.check g →
      n = F a := by
    intro a ha n hn
    rw [← A.check_kpair, A.check_mem_iff] at hn
    obtain ⟨y, _, hy⟩ := (mem_definableGraph_iff S F hF _).mp hn
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hy
    rfl
  refine ⟨3, omegaPairDecodeFormula, ![A.check S, A.check g, r], ?_, fun b ↦ ?_⟩
  · intro i
    match i with
    | 0 => exact Or.inl ⟨S, rfl⟩
    | 1 => exact Or.inl ⟨g, rfl⟩
    | 2 => exact Or.inr (Or.inl hrsub)
  · rw [eval_omegaPairDecodeFormula]
    constructor
    · intro hb
      obtain ⟨b₀, hb₀, rfl⟩ := (A.mem_check_iff _ _).mp (hx b hb)
      refine ⟨hx _ hb, A.check (F b₀), ?_, hpairmem b₀ hb₀⟩
      exact mem_sep_iff.mpr ⟨(A.check_mem_iff _ _).mpr (hFω b₀ hb₀), _, hb, hpairmem b₀ hb₀⟩
    · rintro ⟨hb, n, hn, hbn⟩
      obtain ⟨b₀, hb₀, rfl⟩ := (A.mem_check_iff _ _).mp hb
      obtain ⟨hnω, p, hp, hpn⟩ := mem_sep_iff.mp hn
      obtain ⟨n₀, _, rfl⟩ := (A.mem_check_iff _ _).mp hnω
      obtain ⟨p₀, hp₀, rfl⟩ := (A.mem_check_iff _ _).mp (hx p hp)
      have h1 : n₀ = F b₀ := hpairmem' b₀ hb₀ n₀ hbn
      have h2 : n₀ = F p₀ := hpairmem' p₀ hp₀ n₀ hpn
      rw [hFinj b₀ hb₀ p₀ hp₀ (h1 ▸ h2 ▸ rfl)]
      exact hp

end ForcingContext

/-! ### The code of `k × ω × ω` in `ω` -/

/-- The ground code of a triple `⟨i, ⟨a, b⟩⟩` by iterated natural pairing. -/
noncomputable def orbitCode (w : V) : V :=
  naturalPairCode (kpair.π₁ w) (naturalPairCode (kpair.π₁ (kpair.π₂ w)) (kpair.π₂ (kpair.π₂ w)))

instance orbitCode_definable : ℒₛₑₜ-function₁[V] orbitCode := by
  unfold orbitCode
  definability

theorem orbitCode_kpair (i a b : V) :
    orbitCode (⟨i, (⟨a, b⟩ₖ : V)⟩ₖ : V) = naturalPairCode i (naturalPairCode a b) := by
  unfold orbitCode
  rw [kpair.π₁_kpair, kpair.π₂_kpair, kpair.π₁_kpair, kpair.π₂_kpair]

theorem orbitCode_natural {k : V} (hk : k ⊆ (ω : V)) :
    ∀ w ∈ k ×ˢ ((ω : V) ×ˢ (ω : V)), orbitCode w ∈ (ω : V) := by
  rintro w hw
  obtain ⟨i, hi, y, hy, rfl⟩ := mem_prod_iff.mp hw
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hy
  rw [orbitCode_kpair]
  exact naturalPairCode_natural (hk i hi) (naturalPairCode_natural ha hb)

theorem orbitCode_injective {k : V} (hk : k ⊆ (ω : V)) :
    ∀ w ∈ k ×ˢ ((ω : V) ×ˢ (ω : V)), ∀ w' ∈ k ×ˢ ((ω : V) ×ˢ (ω : V)),
      orbitCode w = orbitCode w' → w = w' := by
  rintro w hw w' hw' he
  obtain ⟨i, hi, y, hy, rfl⟩ := mem_prod_iff.mp hw
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hy
  obtain ⟨i', hi', y', hy', rfl⟩ := mem_prod_iff.mp hw'
  obtain ⟨a', ha', b', hb', rfl⟩ := mem_prod_iff.mp hy'
  rw [orbitCode_kpair, orbitCode_kpair] at he
  obtain ⟨rfl, hc⟩ := naturalPairCode_injective (hk i hi) (naturalPairCode_natural ha hb)
    (hk i' hi') (naturalPairCode_natural ha' hb') he
  obtain ⟨rfl, rfl⟩ := naturalPairCode_injective ha hb ha' hb' hc
  rfl

/-! ### The orbit union -/

/-- A subname-closed ground set holding the name `τ` and every value of the support sequence
`s`. -/
noncomputable def orbitClosure (s τ : V) : V := transitiveClosure (({τ} : V) ∪ range s)

theorem mem_orbitClosure_self (s τ : V) : τ ∈ orbitClosure s τ :=
  subset_transitiveClosure _ _ (mem_union_iff.mpr (Or.inl (mem_singleton_iff.mpr rfl)))

theorem mem_orbitClosure_of_mem_range {s τ z : V} (hz : z ∈ range s) : z ∈ orbitClosure s τ :=
  subset_transitiveClosure _ _ (mem_union_iff.mpr (Or.inr hz))

theorem orbitClosure_transitive (s τ : V) : IsTransitive (orbitClosure s τ) :=
  transitiveClosure_transitive _

namespace ForcingContext

variable (A : ForcingContext V)

/-- The parameter that carries the values of the support names: the `i`-th section is the value
of the `i`-th support name at the generic. -/
noncomputable def orbitSupportReal (s k : V) : A.Model :=
  sep (A.check (k ×ˢ ((ω : V) ×ˢ (ω : V))))
    (fun w ↦ ∃ i : A.Model, ∃ z : A.Model, w = (⟨i, z⟩ₖ : A.Model) ∧
      z ∈ nameValue A.boolGenericSet ((A.check s) ‘ i))
    (by definability)

theorem orbitSupportReal_subset (s k : V) :
    A.orbitSupportReal s k ⊆ A.check (k ×ˢ ((ω : V) ×ˢ (ω : V))) := sep_subset

theorem mem_orbitSupportReal_iff (s k : V) (w : A.Model) :
    w ∈ A.orbitSupportReal s k ↔ w ∈ A.check (k ×ˢ ((ω : V) ×ˢ (ω : V))) ∧
      ∃ i : A.Model, ∃ z : A.Model, w = (⟨i, z⟩ₖ : A.Model) ∧
        z ∈ nameValue A.boolGenericSet ((A.check s) ‘ i) := mem_sep_iff

/-- Every value of the name `τ` at a subset of the checked completion, gathered into one set.
The orbit union is separated out of this. -/
noncomputable def orbitBound (τ : V) : A.Model :=
  ⋃ˢ (repl (fun H ↦ nameValue H (A.check τ)) (by definability)
    (℘ (A.check (booleanConditions A.P A.R))))

theorem mem_orbitBound_iff (τ : V) (b : A.Model) :
    b ∈ A.orbitBound τ ↔
      ∃ H : A.Model, H ⊆ A.check (booleanConditions A.P A.R) ∧
        b ∈ nameValue H (A.check τ) := by
  unfold orbitBound
  rw [mem_sUnion_iff]
  constructor
  · rintro ⟨y, hy, hby⟩
    rw [repl_spec] at hy
    obtain ⟨H, hH, rfl⟩ := hy
    exact ⟨H, mem_power_iff.mp hH, hby⟩
  · rintro ⟨H, hH, hb⟩
    exact ⟨nameValue H (A.check τ), by rw [repl_spec]; exact ⟨H, mem_power_iff.mpr hH, rfl⟩, hb⟩

/-- The bounding set is definable in the extension from ground sets alone. -/
theorem groundRealDefinable_orbitBound (s τ : V) : A.IsGroundRealDefinable (A.orbitBound τ) := by
  have hN : IsSubnameClosed (A.check (orbitClosure s τ)) :=
    transitive_subnameClosed (check_transitive_of_ground (orbitClosure_transitive s τ))
  have hct : A.check τ ∈ A.check (orbitClosure s τ) :=
    (A.check_mem_iff _ _).mpr (mem_orbitClosure_self s τ)
  refine groundRealDefinable_of_definable_from_definables
    ![A.check (booleanConditions A.P A.R), A.check (orbitClosure s τ), A.check τ]
    (fun i ↦ ?_) orbitBoundFormula (fun b ↦ ?_)
  · match i with
    | 0 => exact groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
    | 1 => exact groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
    | 2 => exact groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
  · have he : (b :> ![A.check (booleanConditions A.P A.R), A.check (orbitClosure s τ),
        A.check τ]) = ![b, A.check (booleanConditions A.P A.R), A.check (orbitClosure s τ),
        A.check τ] := rfl
    rw [he, eval_orbitBoundFormula hN hct]
    exact A.mem_orbitBound_iff τ b

/-- The parameters of the orbit union: the bounding set, checks of ground sets, and the support
real. -/
noncomputable def solovayOrbitParams (s k τ : V) (p : A.Model) : Fin 10 → A.Model :=
  ![A.orbitBound τ,
    A.check (regularSets A.P A.R),
    A.check (boolMaximalAntichains A.P A.R),
    A.check A.P,
    A.check (orbitClosure s τ),
    A.check τ,
    A.check s,
    A.check k,
    A.orbitSupportReal s k,
    p]

/-- The orbit union of Karagila and Schilhan, Proposition 9.4, as a set of the extension: the
union of the values `τ^H` over the internally generic filters `H` that contain the top and give
the support names `s ‘ i` the same values as the generic does. -/
noncomputable def solovayOrbitUnion (Pf : SetTheorySemisentence 2) (s k τ : V) (p : A.Model) :
    A.Model :=
  sep (A.orbitBound τ)
    (fun b ↦ (solovayOrbitFormula Pf).Evalb (b :> A.solovayOrbitParams s k τ p))
    (evalbSection_definable _ _)

theorem mem_solovayOrbitUnion_iff (Pf : SetTheorySemisentence 2) (s k τ : V) (p b : A.Model) :
    b ∈ A.solovayOrbitUnion Pf s k τ p ↔
      (solovayOrbitFormula Pf).Evalb (b :> A.solovayOrbitParams s k τ p) := by
  unfold solovayOrbitUnion
  rw [mem_sep_iff]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  have he : (b :> A.solovayOrbitParams s k τ p) =
      ![b, A.orbitBound τ, A.check (regularSets A.P A.R),
        A.check (boolMaximalAntichains A.P A.R), A.check A.P, A.check (orbitClosure s τ),
        A.check τ, A.check s, A.check k, A.orbitSupportReal s k, p] := rfl
  rw [he, eval_solovayOrbitFormula_raw] at h
  exact h.1

/-- The orbit union is definable in the extension from ground sets, reals and ordinals. This is
the definability half of Karagila and Schilhan, Proposition 9.4: the union is read off ground
parameters and the values of the finitely many support names, which are reals. -/
theorem groundRealDefinable_solovayOrbitUnion (Pf : SetTheorySemisentence 2) (s τ : V) {k : V}
    (hk : k ⊆ (ω : V)) {p : A.Model} (hp : A.IsGroundRealDefinable p) :
    A.IsGroundRealDefinable (A.solovayOrbitUnion Pf s k τ p) := by
  refine groundRealDefinable_of_definable_from_definables (A.solovayOrbitParams s k τ p)
    (fun i ↦ ?_) (solovayOrbitFormula Pf) (fun b ↦ ?_)
  · match i with
    | 0 => exact A.groundRealDefinable_orbitBound s τ
    | 1 => exact groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
    | 2 => exact groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
    | 3 => exact groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
    | 4 => exact groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
    | 5 => exact groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
    | 6 => exact groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
    | 7 => exact groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
    | 8 =>
      exact groundRealDefinable_of_subset_check_of_code (orbitCode_definable (V := V))
        (orbitCode_natural hk) (orbitCode_injective hk) (A.orbitSupportReal_subset s k)
    | 9 => exact hp
  · exact A.mem_solovayOrbitUnion_iff Pf s k τ p b

end ForcingContext

/-! ### The easy inclusion -/

namespace ForcingContext

variable {A : ForcingContext V}

/-- The value of a Boolean name in the extension is the internal valuation of the check of the
name at the trace of the generic on the completion. -/
theorem booleanReal_eq_nameValue (A : ForcingContext V) (τ : ForcingName A.booleanContext.P) :
    A.booleanReal τ = nameValue A.boolGenericSet (A.check τ.val) := by
  have hmap : A.booleanEquiv (nameValue A.boolGenericSet (A.check τ.val)) =
      nameValue (A.booleanEquiv A.boolGenericSet) (A.booleanEquiv (A.check τ.val)) :=
    A.recoveredRealization.embedding.map_nameValue _ _
  have h : A.booleanEquiv (nameValue A.boolGenericSet (A.check τ.val)) =
      A.booleanContext.ofName τ := by
    rw [hmap, A.booleanEquiv_boolGenericSet, A.booleanEquiv_check]
    exact A.booleanContext.nameValue_genericSet_check τ
  unfold booleanReal
  rw [← h, Equiv.symm_apply_apply]

/-- The value of the check of a nice name over `K` at any filter containing the top is a set of
checked elements of `K`. -/
theorem nameValue_check_subset_check_of_nice {P one K τ : V}
    (hτ : IsNiceName P one K τ) {H : A.Model} (hone : A.check one ∈ H) :
    nameValue H (A.check τ) ⊆ A.check K := by
  intro z hz
  obtain ⟨σ, p, hp, hσp, rfl⟩ := (mem_nameValue_iff H (A.check τ) z).mp hz
  obtain ⟨w, hw, hweq⟩ := (A.mem_check_iff τ _).mp hσp
  obtain ⟨k, hk, q, hq, rfl⟩ := hτ w hw
  rw [A.check_kpair] at hweq
  obtain ⟨rfl, -⟩ := kpair_iff.mp hweq
  rw [A.nameValue_check_checkName hone k]
  exact (A.check_mem_iff _ _).mpr hk

/-- The trace of the generic on the completion is a set of Boolean conditions. -/
theorem boolGenericSet_subset_check_booleanConditions (A : ForcingContext V) :
    A.boolGenericSet ⊆ A.check (booleanConditions A.P A.R) := by
  intro d hd
  obtain ⟨hdreg, p, hp, hpd⟩ := mem_sep_iff.mp hd
  obtain ⟨d₀, hd₀, rfl⟩ := (A.mem_check_iff _ _).mp hdreg
  obtain ⟨p₀, hp₀, rfl⟩ := (A.mem_check_iff _ _).mp hpd
  exact (A.check_mem_iff _ _).mpr ((mem_booleanConditions_iff _ _ _).mpr
    ⟨(mem_regularSets_iff _ _ _).mp hd₀, p₀, hp₀⟩)

/-- The generic itself is one of the filters of the orbit union, so the value of the name is
contained in the orbit union. This is the easy half of Karagila and Schilhan, Proposition 9.4. -/
theorem booleanReal_subset_solovayOrbitUnion (A : ForcingContext V) {s k : V} [IsFunction s]
    (hsdom : domain s = k) (τ : ForcingName A.booleanContext.P)
    (hs : ∀ i ∈ k, IsNiceName (booleanConditions A.P A.R) A.P ((ω : V) ×ˢ (ω : V)) (s ‘ i))
    (Pf : SetTheorySemisentence 2) {p : A.Model}
    (hground : ∀ a : V, Pf.Evalb ![A.check a, p]) :
    A.booleanReal τ ⊆ A.solovayOrbitUnion Pf s k τ.val p := by
  have hPreg : A.P ∈ regularSets A.P A.R := (mem_regularSets_iff _ _ _).mpr (forcingRegular_top _ _)
  have hone : A.check A.P ∈ A.boolGenericSet :=
    (A.check_mem_boolGenericSet_iff A.P).mpr ⟨hPreg, A.one, A.one_mem_G, A.top.1⟩
  have hN : IsSubnameClosed (A.check (orbitClosure s τ.val)) :=
    transitive_subnameClosed (check_transitive_of_ground (orbitClosure_transitive s τ.val))
  have hct : A.check τ.val ∈ A.check (orbitClosure s τ.val) :=
    (A.check_mem_iff _ _).mpr (mem_orbitClosure_self s τ.val)
  have hvals : ∀ i₀ ∈ k, (A.check s) ‘ (A.check i₀) = A.check (s ‘ i₀) := fun i₀ hi₀ ↦
    A.check_value (by rw [hsdom]; exact hi₀)
  have hcs : ∀ i ∈ A.check k, (A.check s) ‘ i ∈ A.check (orbitClosure s τ.val) := by
    intro i hi
    obtain ⟨i₀, hi₀, rfl⟩ := (A.mem_check_iff _ _).mp hi
    rw [hvals i₀ hi₀]
    exact (A.check_mem_iff _ _).mpr (mem_orbitClosure_of_mem_range
      (mem_range_of_kpair_mem (kpair_value_mem (by rw [hsdom]; exact hi₀))))
  have hgen := A.boolGenericSet_antichainGeneric
  have hfull : IsFullValuation Pf p A.boolGenericSet := by
    intro x
    obtain ⟨τ', hτ'⟩ := A.booleanContext.ofName_surjective (A.booleanEquiv x)
    refine ⟨A.check τ'.val, hground _, ?_⟩
    rw [← A.booleanReal_eq_nameValue τ']
    unfold booleanReal
    rw [hτ', Equiv.symm_apply_apply]
  have hfilter : IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p A.boolGenericSet := by
    refine ⟨hgen.subset, hgen.upward, hgen.inter, ?_, hgen.meets, hone, hfull, ?_⟩
    · intro u hu
      obtain ⟨-, q, -, hq⟩ := mem_sep_iff.mp hu
      exact ⟨q, hq⟩
    · intro i hi z
      obtain ⟨i₀, hi₀, rfl⟩ := (A.mem_check_iff _ _).mp hi
      rw [A.mem_orbitSupportReal_iff]
      constructor
      · intro hz
        rw [hvals i₀ hi₀] at hz
        have hzK : z ∈ A.check ((ω : V) ×ˢ (ω : V)) :=
          nameValue_check_subset_check_of_nice (hs i₀ hi₀) hone z hz
        refine ⟨?_, A.check i₀, z, rfl, by rw [hvals i₀ hi₀]; exact hz⟩
        rw [show A.check (k ×ˢ ((ω : V) ×ˢ (ω : V)))
            = A.check k ×ˢ A.check ((ω : V) ×ˢ (ω : V)) from A.checkEmbedding.map_prod _ _]
        exact mem_prod_iff.mpr ⟨A.check i₀, (A.check_mem_iff _ _).mpr hi₀, z, hzK, rfl⟩
      · rintro ⟨-, i', z', he, hz'⟩
        obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
        exact hz'
  intro b hb
  rw [A.booleanReal_eq_nameValue τ] at hb
  rw [A.mem_solovayOrbitUnion_iff]
  have he : (b :> A.solovayOrbitParams s k τ.val p) =
      ![b, A.orbitBound τ.val, A.check (regularSets A.P A.R),
        A.check (boolMaximalAntichains A.P A.R), A.check A.P, A.check (orbitClosure s τ.val),
        A.check τ.val, A.check s, A.check k, A.orbitSupportReal s k, p] := rfl
  rw [he, eval_solovayOrbitFormula Pf hN hct hcs]
  exact ⟨(A.mem_orbitBound_iff τ.val b).mpr
      ⟨A.boolGenericSet, A.boolGenericSet_subset_check_booleanConditions, hb⟩,
    A.boolGenericSet, hfilter, hb⟩

end ForcingContext

/-! ### The hard inclusion -/

namespace ForcingContext

variable (A : ForcingContext V)

/-- The transfer statement of Karagila and Schilhan, Lemma 9.3, in the form the orbit union
needs: every internally generic filter that agrees with the generic on the support names is the
image of the generic under a ground automorphism lying in the forced stabilizer of the support.
The side condition `V[H] = V[G]` of the paper is kept: it is the clause `IsFullValuation Pf p H`
of `IsOrbitFilter`, which says that every set of the extension is the value at `H` of a name
satisfying `Pf` at `p`. The statement itself is carried as a hypothesis rather than proved. -/
def OrbitTransfer (Pf : SetTheorySemisentence 2) (s k : V) (p : A.Model) : Prop :=
  ∀ H : A.Model, IsOrbitFilter Pf (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check A.P) (A.check s) (A.check k)
      (A.orbitSupportReal s k) p H →
    ∃ π ∈ forcedStabilizer (booleanConditions A.P A.R) (booleanOrder A.P A.R)
        (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R)) (range s),
      H = range ((A.check π) ↾ A.boolGenericSet)

/-- The symmetry lemma for the image of the generic under an automorphism that fixes the name:
the value of the name at the image filter is its value at the generic. -/
theorem nameValue_image_eq {π τ : V}
    (hπ : IsForcingAutomorphism (booleanConditions A.P A.R) (booleanOrder A.P A.R) π)
    (hτ : IsForcingName (booleanConditions A.P A.R) τ) (hfix : nameAction π τ = τ) :
    nameValue (range ((A.check π) ↾ A.boolGenericSet)) (A.check τ) =
      nameValue A.boolGenericSet (A.check τ) := by
  have hcf : ∀ x : V, A.checkEmbedding.toFun x = A.check x := fun _ ↦ rfl
  have hπ' := A.checkEmbedding.map_forcingAutomorphism hπ
  simp only [hcf] at hπ'
  have hτ' : IsForcingName (A.check (booleanConditions A.P A.R)) (A.check τ) :=
    A.checkEmbedding.map_forcingName hτ
  have hact : nameAction (A.check π) (A.check τ) = A.check τ := by
    have h0 := A.checkEmbedding.map_nameAction π τ
    simp only [hcf] at h0
    rw [← h0, hfix]
  have h := nameValue_nameAction hπ'.1 hπ'.2.1
    A.boolGenericSet_subset_check_booleanConditions hτ'
  rwa [hact] at h

/-- The orbit union is contained in the value of the name, given the transfer statement. This is
the hard half of Karagila and Schilhan, Proposition 9.4. -/
theorem solovayOrbitUnion_subset_booleanReal (Pf : SetTheorySemisentence 2) {p : A.Model}
    {s k : V} [IsFunction s] (hsdom : domain s = k)
    (τ : ForcingName A.booleanContext.P)
    (hsym : forcedStabilizer (booleanConditions A.P A.R) (booleanOrder A.P A.R)
        (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R)) (range s) ⊆
      nameStabilizer (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R))
        τ.val)
    (htr : A.OrbitTransfer Pf s k p) :
    A.solovayOrbitUnion Pf s k τ.val p ⊆ A.booleanReal τ := by
  have hN : IsSubnameClosed (A.check (orbitClosure s τ.val)) :=
    transitive_subnameClosed (check_transitive_of_ground (orbitClosure_transitive s τ.val))
  have hct : A.check τ.val ∈ A.check (orbitClosure s τ.val) :=
    (A.check_mem_iff _ _).mpr (mem_orbitClosure_self s τ.val)
  have hcs : ∀ i ∈ A.check k, (A.check s) ‘ i ∈ A.check (orbitClosure s τ.val) := by
    intro i hi
    obtain ⟨i₀, hi₀, rfl⟩ := (A.mem_check_iff _ _).mp hi
    rw [A.check_value (f := s) (by rw [hsdom]; exact hi₀)]
    exact (A.check_mem_iff _ _).mpr (mem_orbitClosure_of_mem_range
      (mem_range_of_kpair_mem (kpair_value_mem (by rw [hsdom]; exact hi₀))))
  intro b hb
  rw [A.mem_solovayOrbitUnion_iff] at hb
  have he : (b :> A.solovayOrbitParams s k τ.val p) =
      ![b, A.orbitBound τ.val, A.check (regularSets A.P A.R),
        A.check (boolMaximalAntichains A.P A.R), A.check A.P, A.check (orbitClosure s τ.val),
        A.check τ.val, A.check s, A.check k, A.orbitSupportReal s k, p] := rfl
  rw [he, eval_solovayOrbitFormula Pf hN hct hcs] at hb
  obtain ⟨-, H, hH, hbH⟩ := hb
  obtain ⟨π, hπE, rfl⟩ := htr H hH
  obtain ⟨hπΓ, hfix⟩ := mem_sep_iff.mp (hsym π hπE)
  rw [A.nameValue_image_eq ((mem_forcingAutomorphisms_iff _ _ _).mp hπΓ) τ.property hfix] at hbH
  rw [A.booleanReal_eq_nameValue τ]
  exact hbH

/-! ### The value of a symmetric name -/

/-- The value of a hereditarily symmetric name of the Solovay system is definable in the
extension from ground sets, reals and ordinals, given the transfer statement. -/
theorem groundRealDefinable_booleanReal_of_transfer (Pf : SetTheorySemisentence 2) {p : A.Model}
    (hp : A.IsGroundRealDefinable p) (hground : ∀ a : V, Pf.Evalb ![A.check a, p])
    (htr : ∀ s k : V, A.OrbitTransfer Pf s k p) (τ : A.solovayContext.Name) :
    A.IsGroundRealDefinable (A.booleanReal ⟨τ.val, τ.property.1⟩) := by
  obtain ⟨E, hEf, hE, hEs⟩ := A.solovay_exists_support τ
  obtain ⟨s, hsfin, hsrange⟩ := exists_finiteSequence_range hEf
  obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff E s).mp hsfin
  have : IsFunction s := IsFunction.of_mem hsn
  have hsdom : domain s = n := domain_eq_of_mem_function hsn
  have hnω : n ⊆ (ω : V) := IsOrdinal.toIsTransitive.transitive n hn
  have hsval : ∀ i ∈ n, s ‘ i ∈ E := by
    intro i hi
    rw [← hsrange]
    exact mem_range_of_kpair_mem (kpair_value_mem (by rw [hsdom]; exact hi))
  have hs : ∀ i ∈ n, IsNiceName (booleanConditions A.P A.R) A.P ((ω : V) ×ˢ (ω : V)) (s ‘ i) :=
    fun i hi ↦ (hE _ (hsval i hi)).nice
  have hsym : forcedStabilizer (booleanConditions A.P A.R) (booleanOrder A.P A.R)
      (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R)) (range s) ⊆
      nameStabilizer (forcingAutomorphisms (booleanConditions A.P A.R) (booleanOrder A.P A.R))
        τ.val := by
    rw [hsrange]
    exact hEs
  set τ' : ForcingName A.booleanContext.P := ⟨τ.val, τ.property.1⟩ with hτ'
  have hsub1 : A.booleanReal τ' ⊆ A.solovayOrbitUnion Pf s n τ.val p :=
    A.booleanReal_subset_solovayOrbitUnion hsdom τ' hs Pf hground
  have hsub2 : A.solovayOrbitUnion Pf s n τ.val p ⊆ A.booleanReal τ' :=
    A.solovayOrbitUnion_subset_booleanReal Pf hsdom τ' hsym (htr s n)
  have heq : A.booleanReal τ' = A.solovayOrbitUnion Pf s n τ.val p :=
    mem_ext (fun z ↦ ⟨fun h ↦ hsub1 z h, fun h ↦ hsub2 z h⟩)
  rw [heq]
  exact A.groundRealDefinable_solovayOrbitUnion Pf s τ.val hnω hp

end ForcingContext

/-! ### The pointwise hypothesis of the Solovay corollary -/

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- The hypothesis `hpt` of `solovay_corollary_final`, from the transfer statement of Karagila
and Schilhan, Lemma 9.3, applied with the ground-model class formula. -/
theorem groundRealDefinable_solovayInclusion_of_transfer
    (htr : ∀ s k : V, (levyContext κ hG).OrbitTransfer groundFormula s k (solovayParam κ hG))
    (x : (levySolovayContext κ hG).Model) :
    (levyContext κ hG).IsGroundRealDefinable (solovaySymmetricInclusion hG x) := by
  obtain ⟨τ, rfl⟩ := (levySolovayContext κ hG).ofName_surjective x
  refine (levyContext κ hG).groundRealDefinable_booleanReal_of_transfer groundFormula ?_ ?_ htr τ
  · rw [solovayParam_eq_check]
    exact ForcingContext.groundRealDefinable_of_parameter (Or.inl ⟨_, rfl⟩)
  · intro a
    exact (eval_groundFormula _ _).mpr (levy_isGround_check hAC hU hc hω hκ hG a)

include hAC hU hc hω hκ in
/-- `cor:Solovay` with the transfer statement of Karagila and Schilhan, Lemma 9.3, as its only
open assumption. -/
theorem solovay_corollary_of_transfer
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (htr : ∀ s k : V, (levyContext κ hG).OrbitTransfer groundFormula s k (solovayParam κ hG)) :
    haveI := solovay_models_zf hAC hU hc hω hκ hG
    (SolovayHOD κ hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 ∧
    (∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := SolovayHOD κ hG) φ) ∧
    InternalDependentChoice (SolovayHOD κ hG) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → IsLebesgueMeasurable X) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → BaireProperty X) ∧
    (∀ X : SolovayHOD κ hG, X ⊆ cantorSpace (SolovayHOD κ hG) → PerfectSetProperty X) ∧
    ¬ InternalChoice (SolovayHOD κ hG) ∧
    hartogsNumber (ω : SolovayHOD κ hG) = solovayCheck hAC hU hc hω hκ hG κ ∧
    IsNonprincipalSetUltrafilter (solovayCheck hAC hU hc hω hκ hG κ)
      (solovayUltrafilter hAC hU hc hω hκ hG) ∧
    IsOrdinalComplete (solovayCheck hAC hU hc hω hκ hG κ)
      (solovayUltrafilter hAC hU hc hω hκ hG) :=
  solovay_corollary_final hAC hU hc hω hκ hG hVP
    (groundRealDefinable_solovayInclusion_of_transfer hAC hU hc hω hκ hG htr)

end

end ZFVP
