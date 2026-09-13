import ZFVP.ModelTheory.SolovayHODGroundSequences
import ZFVP.ModelTheory.SolovayHODBridge
import ZFVP.ModelTheory.LevyParameterTreeLocalized
import ZFVP.ModelTheory.LevyCollapseOmegaOne
import ZFVP.SetTheory.HODFunctionClosure
import ZFVP.SetTheory.HODCantorTransport
import ZFVP.SetTheory.HartogsRegularChoice
import ZFVP.SetTheory.Collection
import ZFVP.SetTheory.LeastOrdinalChoice
import ZFVP.SetTheory.DependentChoice

/-! The Solovay class model is closed under `ω`-sequences of its elements, so dependent choice
holds there (lem:Solovay-regularity, clause `DC`).

Let `f : ω → V[G]` be a sequence in the extension all of whose values are ordinal definable over
the Solovay parameter class. Choice holds in the extension, so a single sequence `n ↦ w_n` of
codes for the values can be chosen: `w_n` is the triple of a stage, a two-variable membership
formula code and a parameter tree defining `f(n)`. Each of the three pieces lies in a bounded
stage `V[G_ξ]`: the stage and the formula code are checks, and a parameter tree over the Solovay
class is localized. Localization is an internally definable predicate, so the least stage holding
`w_n` is a set function of `n`, an `ω`-sequence of ordinals below `κ̌`; and `κ̌` is a regular
cardinal of the extension, so that sequence is bounded by some `ζ̌ < κ̌`. All the codes therefore
lie in `V[G_ζ]`, the code sequence is definable from ground sets, reals and ordinals, and `f` is
read off it by one formula. Hence `f` is ordinal definable, and hereditarily so because its values
and its domain are.

Dependent choice in the class model then follows from dependent choice in the extension. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ### Codes for ordinal definable sets, as a single set -/

section

variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance isParameterTree_definable (Pf : SetTheorySemisentence 2) :
    ℒₛₑₜ-relation[M] (IsParameterTree Pf) := (parameterTreeFormula_defined Pf).to_definable

instance decode_definable : ℒₛₑₜ-function₃[M] decode := decodeFormula_defined.to_definable

/-- `w` codes `x` as an ordinal definable set: it is the triple of a stage, a two-variable
membership formula code and a parameter tree defining `x` over that stage. -/
def IsODCode (Pf : SetTheorySemisentence 2) (p x w : M) : Prop :=
  ∃ α φ P : M, w = ⟨α, ⟨φ, P⟩ₖ⟩ₖ ∧ IsOrdinal α ∧ IsMembershipFormulaCode ((2 : ℕ) : M) φ ∧
    IsParameterTree Pf P p ∧ P ∈ hierarchy α ∧ x = decode α φ P

theorem isOD_iff_exists_odCode (Pf : SetTheorySemisentence 2) (p x : M) :
    IsOD Pf x p ↔ ∃ w : M, IsODCode Pf p x w := by
  constructor
  · rintro ⟨α, φ, P, h1, h2, h3, h4, h5⟩
    exact ⟨⟨α, ⟨φ, P⟩ₖ⟩ₖ, α, φ, P, rfl, h1, h2, h3, h4, h5⟩
  · rintro ⟨w, α, φ, P, -, h1, h2, h3, h4, h5⟩
    exact ⟨α, φ, P, h1, h2, h3, h4, h5⟩

/-- The set a code stands for, read off the three components of the code. -/
theorem odCode_eq_decode {Pf : SetTheorySemisentence 2} {p x w : M} (h : IsODCode Pf p x w) :
    x = decode (kpair.π₁ w) (kpair.π₁ (kpair.π₂ w)) (kpair.π₂ (kpair.π₂ w)) := by
  obtain ⟨α, φ, P, rfl, -, -, -, -, hx⟩ := h
  rw [kpair.π₁_kpair, kpair.π₂_kpair, kpair.π₁_kpair, kpair.π₂_kpair]
  exact hx

/-- The codes inside a fixed set for the `n`-th value of a sequence. -/
noncomputable def odCodeFamily (Pf : SetTheorySemisentence 2) (p W f n : M) : M :=
  {w ∈ W ; IsODCode Pf p (f ‘ n) w}

theorem mem_odCodeFamily_iff (Pf : SetTheorySemisentence 2) (p W f n w : M) :
    w ∈ odCodeFamily Pf p W f n ↔ w ∈ W ∧ IsODCode Pf p (f ‘ n) w := mem_sep_iff

theorem odCodeFamily_definable (Pf : SetTheorySemisentence 2) (p W f : M) :
    ℒₛₑₜ-function₁[M] (odCodeFamily Pf p W f) := by
  have h : ℒₛₑₜ-relation[M] (fun y n : M ↦ ∀ w, w ∈ y ↔ (w ∈ W ∧ IsODCode Pf p (f ‘ n) w)) := by
    unfold IsODCode
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = odCodeFamily Pf p W f (v 1) ↔ _
  rw [mem_ext_iff]
  exact forall_congr' (fun z ↦ iff_congr Iff.rfl (mem_odCodeFamily_iff Pf p W f (v 1) z))

/-- `z` is the pair of `n` with the set decoded from the `n`-th entry of the code sequence `c`. -/
def odSequenceFormula : SetTheorySemisentence 2 :=
  f“z c. ∃ n ∈ !isω, z = !kpair.dfn n
    (!decodeFormula (!kpair.π₁.dfn (!value.dfn c n))
      (!kpair.π₁.dfn (!kpair.π₂.dfn (!value.dfn c n)))
      (!kpair.π₂.dfn (!kpair.π₂.dfn (!value.dfn c n))))”

theorem eval_odSequenceFormula (z c : M) :
    odSequenceFormula.Evalb ![z, c] ↔
      ∃ n ∈ (ω : M), z = ⟨n, decode (kpair.π₁ (c ‘ n)) (kpair.π₁ (kpair.π₂ (c ‘ n)))
        (kpair.π₂ (kpair.π₂ (c ‘ n)))⟩ₖ := by
  simp [odSequenceFormula]

end

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
  (Pf : SetTheorySemisentence 2) {p : (levyContext κ hG).Model}
  (hPf_loc : ∀ y : (levyContext κ hG).Model, Pf.Evalb ![y, p] → IsLocalized hG y)

include hAC hU hc hω hκ in
/-- Every member of the Solovay parameter class is localized. Use this to get `hPf_loc` below
from the stronger class hypothesis used in `LevyParameterTreeLocalized`. -/
theorem solovayParameter_localized
    (hPf_class : ∀ y : (levyContext κ hG).Model, Pf.Evalb ![y, p] →
      (levyContext κ hG).IsSolovayParameter y)
    (y : (levyContext κ hG).Model) (hy : Pf.Evalb ![y, p]) : IsLocalized hG y :=
  isLocalized_parameter hAC hU hc hω hκ hG (hPf_class y hy)

include hAC hU hc hω hκ hPf_loc in
/-- A code built from localized parameters lies in a bounded stage: the stage and the formula
code are checks, and the parameter tree is localized. -/
theorem isLocalized_odCode {x w : (levyContext κ hG).Model} (h : IsODCode Pf p x w) :
    IsLocalized hG w := by
  obtain ⟨α, φ, P, rfl, hα, hcode, hP, -, -⟩ := h
  haveI : IsOrdinal α := hα
  obtain ⟨φ₀, rfl⟩ := (levyContext κ hG).check_membershipFormulaCode hcode
  exact isLocalized_kpair hG (isLocalized_parameter hAC hU hc hω hκ hG (Or.inr (Or.inr hα)))
    (isLocalized_kpair hG (isLocalized_check hG hω φ₀)
      (isLocalized_parameterTree hAC hU hc hω hκ hG Pf p
        (isAllowed_localized hG Pf p hω hPf_loc) hP))

include hAC hU hc hω hκ in
/-- `κ̌` is a regular cardinal of the Levy extension: it is the Hartogs number of `ω` there, and
the extension satisfies Choice. -/
theorem levy_check_kappa_regular : IsRegularCardinal ((levyContext κ hG).check κ) := by
  have h := hartogsNumber_regular ((levyContext κ hG).internalChoice_of_ground hAC)
    (A := (ω : (levyContext κ hG).Model)) (CardLE.refl _)
  rwa [levy_check_hartogs hAC hU hc hω hκ hG] at h

include hω in
theorem levy_omega_mem_check_kappa :
    (ω : (levyContext κ hG).Model) ∈ (levyContext κ hG).check κ := by
  rw [← ForcingContext.check_omega_eq]
  exact ((levyContext κ hG).check_mem_iff (ω : V) κ).mpr hω

include hAC hU hc hω hκ hPf_loc in
/-- An `ω`-sequence of the Levy extension all of whose values are ordinal definable over the
Solovay parameter class is definable from ground sets, reals and ordinals. -/
theorem levy_od_sequence_groundRealDefinable {f A : (levyContext κ hG).Model}
    (hf : f ∈ A ^ (ω : (levyContext κ hG).Model))
    (hval : ∀ n ∈ (ω : (levyContext κ hG).Model), IsOD Pf (f ‘ n) p) :
    (levyContext κ hG).IsGroundRealDefinable f := by
  let B := levyContext κ hG
  haveI : IsFunction f := IsFunction.of_mem hf
  have hd : domain f = (ω : B.Model) := domain_eq_of_mem_function hf
  -- one set holding a code for every value
  obtain ⟨W, hW⟩ := collection (ω : B.Model) (fun n w ↦ IsODCode Pf p (f ‘ n) w)
    (by unfold IsODCode; definability)
    (fun n hn ↦ (isOD_iff_exists_odCode Pf p (f ‘ n)).mp (hval n hn))
  -- and a choice of one code for each value
  obtain ⟨Cd, hCdfun, hCddom, hCdval⟩ :=
    choice_for_definable_family (B.internalChoice_of_ground hAC) (ω : B.Model)
      (odCodeFamily Pf p W f) (odCodeFamily_definable Pf p W f)
      (fun n hn ↦ by
        obtain ⟨w, hwW, hw⟩ := hW n hn
        exact ⟨⟨w, (mem_odCodeFamily_iff Pf p W f n w).mpr ⟨hwW, hw⟩⟩⟩)
  haveI : IsFunction Cd := hCdfun
  have hCdcode : ∀ n ∈ (ω : B.Model), IsODCode Pf p (f ‘ n) (Cd ‘ n) :=
    fun n hn ↦ ((mem_odCodeFamily_iff Pf p W f n _).mp (hCdval n hn)).2
  -- the least stage holding the `n`-th code
  let r : B.Model := levyInternalParameter hG
  have hRl : ℒₛₑₜ-relation[B.Model]
      (fun n ξ : B.Model ↦ ξ ∈ B.check κ ∧ InLevySubmodelInternal ξ (Cd ‘ n) r) := by
    definability
  let b : B.Model → B.Model := leastOrdinalOrZero _ hRl
  have hbspec : ∀ n ∈ (ω : B.Model), b n ∈ B.check κ ∧ InLevySubmodelInternal (b n) (Cd ‘ n) r := by
    intro n hn
    have hloc : IsLocalized hG (Cd ‘ n) :=
      isLocalized_odCode hAC hU hc hω hκ hG Pf hPf_loc (hCdcode n hn)
    obtain ⟨ξ, hξ, hmem⟩ := (isLocalized_iff_internal hAC hU hc hω hκ hG (Cd ‘ n)).mp hloc
    rw [levyInternalParameter_fst] at hξ
    haveI : IsOrdinal ξ := IsOrdinal.of_mem hξ
    exact (leastOrdinalOrZero_spec _ hRl n ⟨ξ, inferInstance, hξ, hmem⟩).2.1
  have hbdef : ℒₛₑₜ-function₁[B.Model] b := leastOrdinalOrZero_definable _ hRl
  let bg : B.Model := definableGraph (ω : B.Model) b hbdef
  have hbg : bg ∈ B.check κ ^ (ω : B.Model) :=
    definableGraph_mem_function_of_mapsTo _ _ b hbdef (fun n hn ↦ (hbspec n hn).1)
  obtain ⟨ξ', hξ'κ, hξ'⟩ := regularCardinal_maps_bounded
    (levy_check_kappa_regular hAC hU hc hω hκ hG) (levy_omega_mem_check_kappa hω hG) hbg
  obtain ⟨ζ, hζ, rfl⟩ := (B.mem_check_iff κ ξ').mp hξ'κ
  haveI : IsOrdinal ζ := IsOrdinal.of_mem hζ
  have hζsub : ζ ⊆ κ := IsOrdinal.toIsTransitive.transitive ζ hζ
  -- all the codes lie in the single stage `V[G_ζ]`
  have hall : ∀ n ∈ (ω : B.Model), InLevySubmodel ζ hζsub hG (Cd ‘ n) := by
    intro n hn
    have hb := hξ' n hn
    rw [value_definableGraph (ω : B.Model) b hbdef hn] at hb
    obtain ⟨ξ₀, hξ₀, hbeq⟩ := (B.mem_check_iff ζ (b n)).mp hb
    haveI : IsOrdinal ξ₀ := IsOrdinal.of_mem (hζsub ξ₀ hξ₀)
    have hξ₀sub : ξ₀ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ₀ (hζsub ξ₀ hξ₀)
    have hmem : InLevySubmodelInternal (B.check ξ₀) (Cd ‘ n) r := hbeq ▸ (hbspec n hn).2
    have h1 : InLevySubmodel ξ₀ hξ₀sub hG (Cd ‘ n) :=
      (inLevySubmodel_iff_internal hAC hU hc hω hκ hG hξ₀sub (Cd ‘ n)).mpr hmem
    exact inLevySubmodel_mono hG hξ₀sub hζsub
      (IsOrdinal.toIsTransitive.transitive ξ₀ hξ₀) h1
  have hCdf : Cd ∈ range Cd ^ (ω : B.Model) := function_mem_of_isFunction' hCddom rfl
  have hCddefinable : B.IsGroundRealDefinable Cd :=
    levy_localized_sequence_groundRealDefinable hAC hU hc hω hκ hG hζ hCdf hall
  -- the sequence is read off its code sequence
  refine ForcingContext.groundRealDefinable_of_definable_from hCddefinable odSequenceFormula
    (fun z ↦ ?_)
  rw [eval_odSequenceFormula, mem_omega_function_iff hf z]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, by rw [← odCode_eq_decode (hCdcode n hn)]⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, by rw [← odCode_eq_decode (hCdcode n hn)]⟩

variable (hPf_check : ∀ a : V, Pf.Evalb ![(levyContext κ hG).check a, p])
  (hPf_real : ∀ c : (levyContext κ hG).Model,
    c ⊆ (levyContext κ hG).check (ω : V) → Pf.Evalb ![c, p])

include hAC hU hc hω hκ hPf_loc hPf_check hPf_real in
/-- The Solovay class model is closed under `ω`-sequences of its elements. -/
theorem levy_hod_sequence_isHOD {f A : (levyContext κ hG).Model}
    (hf : f ∈ A ^ (ω : (levyContext κ hG).Model))
    (hval : ∀ n ∈ (ω : (levyContext κ hG).Model), IsHOD Pf (f ‘ n) p) :
    IsHOD Pf f p := by
  haveI : IsFunction f := IsFunction.of_mem hf
  have hd : domain f = (ω : (levyContext κ hG).Model) := domain_eq_of_mem_function hf
  have hOD : IsOD Pf f p :=
    ForcingContext.isOD_of_groundRealDefinable (levyContext κ hG) Pf hPf_check hPf_real
      (levy_od_sequence_groundRealDefinable hAC hU hc hω hκ hG Pf hPf_loc hf
        (fun n hn ↦ (hval n hn).od Pf))
  refine isHOD_of_function Pf p hOD ?_ ?_
  · rw [hd]
    exact isHOD_of_ordinal Pf (ω : (levyContext κ hG).Model) p
  · rw [hd]
    exact hval

include hAC hU hc hω hκ hPf_loc hPf_check hPf_real in
/-- Dependent choice passes from the Levy extension to the Solovay class model. -/
theorem hod_internalDependentChoice [Nonempty (HODDom Pf p)]
    [(HODDom Pf p)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hDC : InternalDependentChoice (levyContext κ hG).Model) :
    InternalDependentChoice (HODDom Pf p) :=
  hod_dependentChoice Pf p hDC (fun f A hf hvals ↦
    levy_hod_sequence_isHOD hAC hU hc hω hκ hG Pf hPf_loc hPf_check hPf_real hf hvals)

include hAC hU hc hω hκ hPf_loc hPf_check hPf_real in
/-- Dependent choice holds in the Solovay class model: Choice in the ground gives Choice, hence
dependent choice, in the Levy extension. -/
theorem hod_internalDependentChoice_of_ground [Nonempty (HODDom Pf p)]
    [(HODDom Pf p)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : InternalDependentChoice (HODDom Pf p) :=
  hod_internalDependentChoice hAC hU hc hω hκ hG Pf hPf_loc hPf_check hPf_real
    (dependentChoice_of_internalChoice ((levyContext κ hG).internalChoice_of_ground hAC))

end

end ZFVP
