import ZFVP.ModelTheory.DefinableStageDichotomy
import ZFVP.ModelTheory.ElementaryStageSatisfaction
import ZFVP.SetTheory.UniformLowTruth
import ZFVP.Syntax.UniformAssignments
import ZFVP.SetTheory.UniformRecursion
import ZFVP.SetTheory.CnAbsoluteness

/-! Case I of Enayat's Theorem 4.4 ("Models of set theory: extensions and dead ends") for
conservative end extensions: the Tarski criterion, and the contradiction it yields.

Let `j : V → W` be a conservative end extension of models of ZF, `δ ∈ θ` ordinals of `W`, and
`δ₀` the least ordinal that is definable in `(V_θ, ∈)` from `δ` and one old parameter and is
not old itself. Enayat's claim is that the image of `V` passes the Tarski test in `V_{δ₀}`;
`ZFVP.MembershipEndExtension.false_of_elementary_stage` then gives a contradiction, since the
pullback of the satisfaction relation of the stage would be a definable full satisfaction class
for `V`.

The proof of the Tarski test needs the least ordinal `ξ` whose stage holds a witness for a given
coded formula to be definable in `(V_θ, ∈)`. The property defining `ξ` mentions
`MembershipSatisfies` over `V_{δ₀}`, which is not bounded, so `V_θ` computes it correctly only
for suitable `θ`. Here `θ` is therefore chosen by reflection: `ReflectsCaseOne θ` says that
`V_θ` computes the three fixed formulas of `caseOneCodes` correctly, and
`exists_reflectsCaseOne` produces such a `θ` above any prescribed ordinal. The coded formula and
the assignment enter those formulas only as parameters, so one `θ` serves all of them. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Satisfaction of a coded formula in a rank stage, with the stage read off the second
variable and the arity, the code and the assignment read off the third. -/
def stageWitnessSatFormula : SetTheorySemisentence 3 :=
  f“y p q. !membershipSatisfiesFormula (!hierarchyFormula p)
    (!succ.dfn (!kpair.π₁.dfn (!kpair.π₂.dfn q)))
    (!kpair.π₁.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn q)))
    (!assignmentPrependFormula (!kpair.π₁.dfn (!kpair.π₂.dfn q))
      (!kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn q))) y)”

/-- The same, or its negation. -/
def polarSatFormula : Bool → SetTheorySemisentence 3
  | true => stageWitnessSatFormula
  | false => f“y p q. ¬!stageWitnessSatFormula y p q”

/-- The first variable is the least ordinal whose stage holds a witness. -/
def leastPolarWitnessFormula (pos : Bool) : SetTheorySemisentence 3 :=
  f“x p q. !IsOrdinal.dfn x ∧ (∃ y ∈ !hierarchyFormula x, !(polarSatFormula pos) y p q) ∧
    ∀ z ∈ x, ∀ y ∈ !hierarchyFormula z, ¬!(polarSatFormula pos) y p q”

/-- The first variable is the first component of the third. -/
def kpairFirstFormula : SetTheorySemisentence 3 := f“x p q. x = !kpair.π₁.dfn q”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The stage `hierarchy p` satisfies the arity `succ n` code `φ` at the assignment `b`
extended by `y`. -/
def stageSat (p n φ b y : V) : Prop :=
  MembershipSatisfies (hierarchy p) (succ n) φ (assignmentPrepend n b y)

/-- `stageSat` with the arity, the code and the assignment read off `q`, which is expected to
be `⟨u, ⟨n, ⟨φ, b⟩ₖ⟩ₖ⟩ₖ`. The first component is not used by the formula; it carries the
parameter that the least element of Enayat's `O'` is defined from. -/
def stageWitnessSat (y p q : V) : Prop :=
  stageSat p (kpair.π₁ (kpair.π₂ q)) (kpair.π₁ (kpair.π₂ (kpair.π₂ q)))
    (kpair.π₂ (kpair.π₂ (kpair.π₂ q))) y

/-- `stageSat` for `pos = true`, its negation for `pos = false`. -/
def polarStage (pos : Bool) (p n φ b y : V) : Prop :=
  if pos then stageSat p n φ b y else ¬ stageSat p n φ b y

/-- `stageWitnessSat` for `pos = true`, its negation for `pos = false`. -/
def polarSat (pos : Bool) (y p q : V) : Prop :=
  if pos then stageWitnessSat y p q else ¬ stageWitnessSat y p q

theorem polarStage_true (p n φ b y : V) :
    polarStage true p n φ b y ↔ stageSat p n φ b y := by simp [polarStage]

theorem polarStage_false (p n φ b y : V) :
    polarStage false p n φ b y ↔ ¬ stageSat p n φ b y := by simp [polarStage]

theorem polarSat_kpair (pos : Bool) (p u n φ b y : V) :
    polarSat pos y p ⟨u, ⟨n, ⟨φ, b⟩ₖ⟩ₖ⟩ₖ ↔ polarStage pos p n φ b y := by
  cases pos <;> simp [polarSat, polarStage, stageWitnessSat]

/-- `x` is the least ordinal whose stage holds a witness for `polarSat pos`. -/
def IsLeastPolarWitness (pos : Bool) (x p q : V) : Prop :=
  IsOrdinal x ∧ (∃ y ∈ hierarchy x, polarSat pos y p q) ∧
    ∀ z ∈ x, ∀ y ∈ hierarchy z, ¬ polarSat pos y p q

instance stageWitnessSatFormula_defined :
    ℒₛₑₜ-relation₃[V] stageWitnessSat via stageWitnessSatFormula :=
  ⟨fun v ↦ by simp [stageWitnessSatFormula, stageWitnessSat, stageSat]⟩

instance polarSatFormula_defined (pos : Bool) :
    ℒₛₑₜ-relation₃[V] (polarSat pos) via polarSatFormula pos := by
  cases pos
  · exact ⟨fun v ↦ by simp [polarSatFormula, polarSat]⟩
  · exact ⟨fun v ↦ by simp [polarSatFormula, polarSat]⟩

instance leastPolarWitnessFormula_defined (pos : Bool) :
    ℒₛₑₜ-relation₃[V] (IsLeastPolarWitness pos) via leastPolarWitnessFormula pos :=
  ⟨fun v ↦ by simp [leastPolarWitnessFormula, IsLeastPolarWitness]⟩

instance kpairFirstFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun x _ q ↦ x = kpair.π₁ q) via kpairFirstFormula :=
  ⟨fun v ↦ by simp [kpairFirstFormula]⟩

instance stageWitnessSat_definable : ℒₛₑₜ-relation₃[V] stageWitnessSat :=
  stageWitnessSatFormula_defined.to_definable

instance polarSat_definable (pos : Bool) : ℒₛₑₜ-relation₃[V] (polarSat pos) :=
  (polarSatFormula_defined pos).to_definable

theorem polarSat_stage_definable (pos : Bool) (p q : V) :
    ℒₛₑₜ-predicate[V] (fun β ↦ ∃ y ∈ hierarchy β, polarSat pos y p q) := by
  cases pos
  · have he : (fun β : V ↦ ∃ y ∈ hierarchy β, polarSat false y p q)
        = fun β : V ↦ ∃ y ∈ hierarchy β, ¬ stageWitnessSat y p q := by
      funext β
      simp [polarSat]
    rw [he]
    definability
  · have he : (fun β : V ↦ ∃ y ∈ hierarchy β, polarSat true y p q)
        = fun β : V ↦ ∃ y ∈ hierarchy β, stageWitnessSat y p q := by
      funext β
      simp [polarSat]
    rw [he]
    definability

/-! ### The least stage holding a witness -/

/-- There is at most one least witness stage. -/
theorem IsLeastPolarWitness.unique {pos : Bool} {p q x x' : V}
    (h : IsLeastPolarWitness pos x p q) (h' : IsLeastPolarWitness pos x' p q) : x = x' := by
  have hx : IsOrdinal x := h.1
  have hx' : IsOrdinal x' := h'.1
  rcases IsOrdinal.mem_trichotomy x x' with hlt | heq | hgt
  · obtain ⟨y, hy, hpy⟩ := h.2.1
    exact absurd hpy (h'.2.2 x hlt y hy)
  · exact heq
  · obtain ⟨y, hy, hpy⟩ := h'.2.1
    exact absurd hpy (h.2.2 x' hgt y hy)

/-- The least witness stage is at most any other witness stage. -/
theorem IsLeastPolarWitness.le {pos : Bool} {p q x ζ y : V} [IsOrdinal ζ]
    (h : IsLeastPolarWitness pos x p q) (hy : y ∈ hierarchy ζ) (hpy : polarSat pos y p q) :
    x ∈ ζ ∨ x = ζ := by
  have hx : IsOrdinal x := h.1
  rcases IsOrdinal.mem_trichotomy x ζ with hlt | heq | hgt
  · exact Or.inl hlt
  · exact Or.inr heq
  · exact absurd hpy (h.2.2 ζ hgt y hy)

/-- The least witness stage exists as soon as there is a witness. -/
theorem exists_isLeastPolarWitness (pos : Bool) (p q y : V) (hy : polarSat pos y p q) :
    ∃ x : V, IsLeastPolarWitness pos x p q := by
  have hmem : y ∈ hierarchy (succ (rank y)) := by
    rw [hierarchy_succ, mem_power_iff]
    exact subset_hierarchy_rank y
  have hex : ∃ β : V, IsOrdinal β ∧ ∃ y' ∈ hierarchy β, polarSat pos y' p q :=
    ⟨succ (rank y), inferInstance, y, hmem, hy⟩
  obtain ⟨x, hx, -⟩ := leastOrdinal_existsUnique
    (fun β ↦ ∃ y ∈ hierarchy β, polarSat pos y p q) (polarSat_stage_definable pos p q) hex
  have hxord : IsOrdinal x := hx.1
  refine ⟨x, hx.1, hx.2.1, fun z hz w hw hpw ↦ ?_⟩
  have hzord : IsOrdinal z := IsOrdinal.of_mem hz
  have hsub : x ⊆ z := hx.2.2 z hzord ⟨w, hw, hpw⟩
  exact mem_irrefl z (hsub z hz)

/-- A limit ordinal is closed under successor. -/
theorem succ_mem_of_isLimitOrdinal {lam ζ : V} (hlim : IsLimitOrdinal lam) (hζ : ζ ∈ lam) :
    succ ζ ∈ lam := by
  have hlamord : IsOrdinal lam := hlim.1
  have hζord : IsOrdinal ζ := IsOrdinal.of_mem hζ
  rcases IsOrdinal.mem_trichotomy (succ ζ) lam with h | h | h
  · exact h
  · exact absurd ⟨ζ, h.symm⟩ hlim.2.2
  · rcases mem_succ_iff.mp h with rfl | h'
    · exact absurd hζ (mem_irrefl lam)
    · exact absurd (IsOrdinal.toIsTransitive.mem_trans h' hζ) (mem_irrefl lam)

/-! ### Changing the second parameter -/

/-- Definability in a stage chains through a definable second parameter. This is the mirror of
`isStageDefinable_trans`, which chains through the first one. The witnessing code is
`∃ v (χ[v, p, q] ∧ ρ[x, p, v])`. -/
theorem isStageDefinable_trans_param {θ p q u x : V} (hp : p ∈ hierarchy θ)
    (hq : q ∈ hierarchy θ) (hu : IsStageDefinable θ p q u) (hx : IsStageDefinable θ p u x) :
    IsStageDefinable θ p q x := by
  obtain ⟨χ, hχc, hχ⟩ := hu
  obtain ⟨ρ, hρc, hρ⟩ := hx
  have huA : u ∈ hierarchy θ := hχ.1
  have hxA : x ∈ hierarchy θ := hρ.1
  have hA : IsNonempty (hierarchy θ) := ⟨⟨u, huA⟩⟩
  have h3 : ((3 : ℕ) : V) ∈ (ω : V) := ofNat_mem_ω 3
  have h4 : ((4 : ℕ) : V) ∈ (ω : V) := ofNat_mem_ω 4
  set fχ : Fin 3 → Fin 4 := ![⟨0, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩] with hfχ
  set fρ : Fin 3 → Fin 4 := ![⟨1, by omega⟩, ⟨2, by omega⟩, ⟨0, by omega⟩] with hfρ
  set rχ : V := standardTuple (fun k ↦ (((fχ k).val : ℕ) : V)) with hrχdef
  set rρ : V := standardTuple (fun k ↦ (((fρ k).val : ℕ) : V)) with hrρdef
  have hrχ : rχ ∈ ((4 : ℕ) : V) ^ ((3 : ℕ) : V) := index_tuple_mem fχ
  have hrρ : rρ ∈ ((4 : ℕ) : V) ^ ((3 : ℕ) : V) := index_tuple_mem fρ
  set χ' : V := renameMembershipFormula ((3 : ℕ) : V) ((4 : ℕ) : V) rχ χ with hχ'def
  set ρ' : V := renameMembershipFormula ((3 : ℕ) : V) ((4 : ℕ) : V) rρ ρ with hρ'def
  have hχ'mem : χ' ∈ formulaSet (membershipLanguageCode : V) ∅ ((4 : ℕ) : V) :=
    renameMembershipFormula_mem h3 h4 hrχ hχc.valid
  have hρ'mem : ρ' ∈ formulaSet (membershipLanguageCode : V) ∅ ((4 : ℕ) : V) :=
    renameMembershipFormula_mem h3 h4 hrρ hρc.valid
  have hand : andCode χ' ρ' ∈ formulaSet (membershipLanguageCode : V) ∅ ((4 : ℕ) : V) :=
    (formulaSet_binary membershipLanguageCode_valid h4 hχ'mem hρ'mem).1
  have hσ : existsCode (andCode χ' ρ') ∈ formulaSet (membershipLanguageCode : V) ∅ ((3 : ℕ) : V) :=
    (formulaSet_quantifiers membershipLanguageCode_valid h3 hand).2
  refine ⟨existsCode (andCode χ' ρ'), (mem_formulaSet_iff _ _ _ _).mp hσ, hxA, fun z hz ↦ ?_⟩
  have hb : standardTuple ![z, p, q] ∈ hierarchy θ ^ ((3 : ℕ) : V) :=
    standardTuple_mem_function _ (fun i ↦
      Fin.cases hz (fun i ↦ Fin.cases hp (fun i ↦ Fin.cases hq (fun i ↦ i.elim0) i) i) i)
  rw [membershipSatisfies_exists h3 hand hb]
  have key : ∀ w ∈ hierarchy θ,
      (MembershipSatisfies (hierarchy θ) ((4 : ℕ) : V) (andCode χ' ρ')
        (assignmentPrepend ((3 : ℕ) : V) (standardTuple ![z, p, q]) w) ↔
          (w = u ∧ MembershipSatisfies (hierarchy θ) ((3 : ℕ) : V) ρ
            (standardTuple ![z, p, w]))) := by
    intro w hw
    have hcons : assignmentPrepend ((3 : ℕ) : V) (standardTuple ![z, p, q]) w =
        standardTuple ![w, z, p, q] := (standardTuple_prepend w ![z, p, q]).symm
    have hc : standardTuple ![w, z, p, q] ∈ hierarchy θ ^ ((4 : ℕ) : V) :=
      standardTuple_mem_function _ (fun i ↦
        Fin.cases hw (fun i ↦ Fin.cases hz (fun i ↦ Fin.cases hp
          (fun i ↦ Fin.cases hq (fun i ↦ i.elim0) i) i) i) i)
    rw [hcons, membershipSatisfies_and h4 hχ'mem hρ'mem hc,
      membershipSatisfies_rename hA h3 h4 hrχ hχc.valid hc,
      membershipSatisfies_rename hA h3 h4 hrρ hρc.valid hc]
    rw [compose_index_tuple ![w, z, p, q] fχ ![w, p, q]
        (fun k ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
          (fun k ↦ k.elim0) k) k) k),
      compose_index_tuple ![w, z, p, q] fρ ![z, p, w]
        (fun k ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
          (fun k ↦ k.elim0) k) k) k)]
    exact and_congr_left' (hχ.2 w hw)
  constructor
  · rintro ⟨w, hw, hsat⟩
    obtain ⟨rfl, hρsat⟩ := (key w hw).mp hsat
    exact (hρ.2 z hz).mp hρsat
  · intro hzx
    exact ⟨u, huA, (key u huA).mpr ⟨rfl, (hρ.2 z hz).mpr hzx⟩⟩

/-! ### Choosing the stage by reflection -/

/-- The three-variable formulas that Case I needs `(hierarchy θ, ∈)` to compute correctly. -/
def caseOneCodes : List (SetTheorySemisentence 3) :=
  [kpairFirstFormula, leastPolarWitnessFormula true, leastPolarWitnessFormula false]

/-- `(hierarchy θ, ∈)` computes the formulas of `caseOneCodes` correctly, in the coded sense
that internal satisfaction of the encoded formula agrees with the real one. -/
def ReflectsCaseOne (θ : V) : Prop :=
  ∀ ψ ∈ caseOneCodes, ∀ b : Fin 3 → SetDomain (hierarchy θ),
    MembershipSatisfies (hierarchy θ) ((3 : ℕ) : V) (encodeMembershipFormula ψ)
      (standardTuple (fun i ↦ (b i).val)) ↔ ψ.Evalb (fun i ↦ (b i).val)

/-- Such a stage exists above any prescribed ordinal: the list of formulas is fixed, and the
coded formula and the assignment of Case I enter it only as parameters. -/
theorem exists_reflectsCaseOne (δ : V) [IsOrdinal δ] :
    ∃ θ : V, IsOrdinal θ ∧ δ ∈ θ ∧ ReflectsCaseOne θ := by
  obtain ⟨θ, hθ, hδ, -, hΦ⟩ := finite_coded_reflection_containing
    (caseOneCodes.map (fun ψ ↦ (⟨3, ψ⟩ : FormulaWithArity))) δ
  have : IsOrdinal θ := hθ
  refine ⟨θ, hθ, ordinal_mem_hierarchy_iff.mp hδ, fun ψ hψ b ↦ ?_⟩
  exact hΦ ⟨3, ψ⟩ (List.mem_map_of_mem hψ) b

/-- A reflected formula that pins down `x` uniquely inside the stage defines `x` there. -/
theorem isStageDefinable_of_reflect {θ p q x : V} (hθ : ReflectsCaseOne θ)
    {ψ : SetTheorySemisentence 3} (hψ : ψ ∈ caseOneCodes)
    (hx : x ∈ hierarchy θ) (hp : p ∈ hierarchy θ) (hq : q ∈ hierarchy θ)
    (hchar : ∀ z ∈ hierarchy θ, ψ.Evalb ![z, p, q] ↔ z = x) :
    IsStageDefinable θ p q x := by
  refine ⟨encodeMembershipFormula ψ,
    (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem ψ), hx, fun z hz ↦ ?_⟩
  have hval : (fun i ↦ ((![⟨z, hz⟩, ⟨p, hp⟩, ⟨q, hq⟩] :
      Fin 3 → SetDomain (hierarchy θ)) i).val) = ![z, p, q] := by
    funext i
    exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ i.elim0) i) i) i
  have h := hθ ψ hψ ![⟨z, hz⟩, ⟨p, hp⟩, ⟨q, hq⟩]
  rw [hval] at h
  rw [h]
  exact hchar z hz

/-! ### Case I with the parameter quantified existentially

Enayat's class `O` is the union over old parameters `m` of the ordinals `ξ ≤ δ` that are
definable in `(V_θ, ∈)` from `δ` and `m`. `ZFVP.MembershipEndExtension.stageDefinableCore`
takes the intersection over `m` instead. The intersection is what the argument below cannot
use: the ordinal it produces is definable from `δ` and one specific old parameter, the one
that codes the formula and the assignment, and there is no reason for it to be definable from
`δ` and an arbitrary old parameter. So the union is taken here. -/

namespace MembershipEndExtension

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Enayat's `O`: the ordinals `ξ ≤ δ` definable in `(V_θ, ∈)` from `δ` and some one old
parameter. -/
def stageDefinableParamCore (j : MembershipEndExtension V W) (δ θ : W) : W → Prop :=
  fun ξ ↦ ξ ∈ succ δ ∧ ∃ m : V, IsStageDefinable θ δ (j m) ξ

/-- Enayat's `O'`: the part of `O` outside the image of the smaller model. -/
def stageDefinableParamNew (j : MembershipEndExtension V W) (δ θ : W) : W → Prop :=
  fun ξ ↦ stageDefinableParamCore j δ θ ξ ∧ ∀ α : V, j α ≠ ξ

/-- `δ₀` is the least element of `O'`. This is the hypothesis of Enayat's Case I. -/
def IsLeastStageDefinableParamNew (j : MembershipEndExtension V W) (δ θ δ₀ : W) : Prop :=
  IsOrdinal δ₀ ∧ stageDefinableParamNew j δ θ δ₀ ∧ ∀ ξ ∈ δ₀, ¬ stageDefinableParamNew j δ θ ξ

/-- Definability from every old parameter is definability from some one of them. -/
theorem stageDefinableCore.param {j : MembershipEndExtension V W} {δ θ ξ : W}
    (h : stageDefinableCore j δ θ ξ) : stageDefinableParamCore j δ θ ξ :=
  ⟨h.1, ∅, h.2 ∅⟩

theorem stageDefinableNew.param {j : MembershipEndExtension V W} {δ θ ξ : W}
    (h : stageDefinableNew j δ θ ξ) : stageDefinableParamNew j δ θ ξ :=
  ⟨h.1.param, h.2⟩

/-- If `δ` is a new ordinal then `δ` belongs to `O'`, so `O'` is not empty. -/
theorem stageDefinableParamNew_self {j : MembershipEndExtension V W} (h : j.IsConservative)
    {δ θ : W} [IsOrdinal δ] [IsOrdinal θ] (hδθ : δ ∈ θ) (hnew : ∀ α : V, j α ≠ δ) :
    stageDefinableParamNew j δ θ δ :=
  (stageDefinableNew_self h hδθ hnew).param

/-- The image of the smaller model is contained in the stage `V_{δ₀}`. -/
theorem map_mem_hierarchy_of_leastParam {j : MembershipEndExtension V W} (h : j.IsConservative)
    {δ θ δ₀ : W} (hleast : IsLeastStageDefinableParamNew j δ θ δ₀) (x : V) :
    j x ∈ hierarchy δ₀ :=
  have : IsOrdinal δ₀ := hleast.1
  map_mem_hierarchy_of_new h hleast.2.1.2 x

/-- `δ₀ ≤ δ`, so the stage `V_{δ₀}` sits inside `V_θ`. -/
theorem subset_of_leastParam {j : MembershipEndExtension V W} {δ θ δ₀ : W} [IsOrdinal δ]
    (hleast : IsLeastStageDefinableParamNew j δ θ δ₀) : δ₀ ⊆ δ := by
  rcases mem_succ_iff.mp hleast.2.1.1.1 with rfl | hlt
  · exact fun x hx ↦ hx
  · exact IsOrdinal.toIsTransitive.transitive δ₀ hlt

/-- Enayat's "`δ₀` is a limit ordinal", for the class `O` with the parameter quantified
existentially. If `δ₀` were `succ γ` then `γ = ⋃ δ₀` would be definable in the stage from `δ₀`,
hence from `δ` and the same old parameter that defines `δ₀`; and `γ` would be new. -/
theorem isLimitOrdinal_of_leastParam {j : MembershipEndExtension V W} {δ θ δ₀ : W}
    [IsOrdinal δ] [IsOrdinal θ] (hδθ : δ ∈ θ) (hmem : ∀ m : V, j m ∈ hierarchy θ)
    (hleast : IsLeastStageDefinableParamNew j δ θ δ₀) : IsLimitOrdinal δ₀ := by
  have hδ₀ord : IsOrdinal δ₀ := hleast.1
  have hδmem : δ ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hδθ
  have hδ₀θ : δ₀ ∈ θ := by
    rcases mem_succ_iff.mp hleast.2.1.1.1 with rfl | hlt
    · exact hδθ
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hδθ
  have hδ₀mem : δ₀ ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hδ₀θ
  obtain ⟨m₀, hm₀⟩ := hleast.2.1.1.2
  rcases ordinal_cases δ₀ with h0 | ⟨γ, hγ, hsucc⟩ | hlim
  · exact absurd (h0 ▸ j.map_empty) (hleast.2.1.2 ∅)
  · exfalso
    have hγord : IsOrdinal γ := hγ
    have hγtr : IsTransitive γ := IsOrdinal.toIsTransitive
    have hγmem : γ ∈ δ₀ := by rw [hsucc]; exact mem_succ_self γ
    have hunion : (⋃ˢ δ₀ : W) = γ := by
      rw [hsucc]; exact sUnion_succ_of_transitive (n := γ)
    refine hleast.2.2 γ hγmem ⟨⟨?_, m₀, ?_⟩, fun α hα ↦ ?_⟩
    · exact IsOrdinal.toIsTransitive.mem_trans hγmem hleast.2.1.1.1
    · have hdef : IsStageDefinable θ δ₀ (j m₀) γ := by
        rw [← hunion]; exact isStageDefinable_sUnion hδ₀mem (hmem m₀)
      exact isStageDefinable_trans hδmem (hmem m₀) hm₀ hdef
    · refine hleast.2.1.2 (succ α) ?_
      rw [j.map_succ, hα, ← hsucc]
  · exact hlim

/-- The heart of Case I. Given an old code and an old assignment, if the stage `V_{δ₀}` holds a
witness for the code, or for its negation, then it holds an old one. The least ordinal `ξ` whose
stage holds a witness is definable in `(V_θ, ∈)` from `δ₀` and the old parameter that packs the
code, the assignment and the parameter defining `δ₀`; chaining, it is definable from `δ` and that
parameter, so it lies in `O`; it is below `δ₀`, so by minimality it is old, `ξ = j α`; and then a
witness lies in `hierarchy (j α) = j (hierarchy α)`, so it is old too. -/
theorem exists_old_polar_witness {j : MembershipEndExtension V W} (hc : j.IsConservative)
    {δ θ δ₀ : W} [IsOrdinal δ] [IsOrdinal θ] (hδθ : δ ∈ θ) (hrefl : ReflectsCaseOne θ)
    (hleast : IsLeastStageDefinableParamNew j δ θ δ₀) (pos : Bool) (n φ b : V) {x : W}
    (hx : x ∈ hierarchy δ₀) (hsat : polarStage pos δ₀ (j n) (j φ) (j b) x) :
    ∃ y : V, polarStage pos δ₀ (j n) (j φ) (j b) (j y) := by
  have hδ₀ord : IsOrdinal δ₀ := hleast.1
  have hnew : ∀ α : V, j α ≠ δ₀ := hleast.2.1.2
  obtain ⟨m₀, hm₀⟩ := hleast.2.1.1.2
  -- containments
  have hδ₀δ : δ₀ ⊆ δ := subset_of_leastParam hleast
  have hδmem : δ ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hδθ
  have hδθsub : δ ⊆ θ := IsOrdinal.toIsTransitive.transitive δ hδθ
  have hδ₀θ : δ₀ ∈ θ := by
    rcases mem_succ_iff.mp hleast.2.1.1.1 with rfl | hlt
    · exact hδθ
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hδθ
  have hδ₀mem : δ₀ ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hδ₀θ
  have hδ₀sub : δ₀ ⊆ θ := IsOrdinal.toIsTransitive.transitive δ₀ hδ₀θ
  have hmemδ₀ : ∀ m : V, j m ∈ hierarchy δ₀ := fun m ↦ map_mem_hierarchy_of_new hc hnew m
  have hmemθ : ∀ m : V, j m ∈ hierarchy θ := fun m ↦ hierarchy_mono hδ₀sub _ (hmemδ₀ m)
  -- the single old parameter
  set M : V := ⟨m₀, ⟨n, ⟨φ, b⟩ₖ⟩ₖ⟩ₖ with hMdef
  set Q : W := j M with hQdef
  have hQ : Q = ⟨j m₀, ⟨j n, ⟨j φ, j b⟩ₖ⟩ₖ⟩ₖ := by
    rw [hQdef, hMdef, j.map_kpair, j.map_kpair, j.map_kpair]
  have hpolar : ∀ y : W, polarSat pos y δ₀ Q ↔ polarStage pos δ₀ (j n) (j φ) (j b) y := by
    intro y
    rw [hQ]
    exact polarSat_kpair pos δ₀ (j m₀) (j n) (j φ) (j b) y
  have hQmem : Q ∈ hierarchy θ := hmemθ M
  -- the least stage holding a witness
  obtain ⟨ξ, hξ⟩ := exists_isLeastPolarWitness pos δ₀ Q x ((hpolar x).mpr hsat)
  have hξord : IsOrdinal ξ := hξ.1
  -- it is below `δ₀`
  have hlim : IsLimitOrdinal δ₀ := isLimitOrdinal_of_leastParam hδθ hmemθ hleast
  have hrankx : rank x ∈ δ₀ := (mem_hierarchy_iff_rank_mem x δ₀).mp hx
  have hsuccmem : succ (rank x) ∈ δ₀ := succ_mem_of_isLimitOrdinal hlim hrankx
  have hxstage : x ∈ hierarchy (succ (rank x)) := by
    rw [hierarchy_succ, mem_power_iff]
    exact subset_hierarchy_rank x
  have hξδ₀ : ξ ∈ δ₀ := by
    rcases hξ.le hxstage ((hpolar x).mpr hsat) with hlt | heq
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hsuccmem
    · exact heq ▸ hsuccmem
  have hξmem : ξ ∈ hierarchy θ :=
    ordinal_mem_hierarchy_iff.mpr (IsOrdinal.toIsTransitive.mem_trans hξδ₀ hδ₀θ)
  -- `ξ` is definable in the stage from `δ₀` and `Q`
  have hξdef : IsStageDefinable θ δ₀ Q ξ := by
    refine isStageDefinable_of_reflect hrefl (ψ := leastPolarWitnessFormula pos) ?_
      hξmem hδ₀mem hQmem (fun z hz ↦ ?_)
    · cases pos <;> simp [caseOneCodes]
    · have he : (leastPolarWitnessFormula pos).Evalb ![z, δ₀, Q] ↔
          IsLeastPolarWitness pos z δ₀ Q :=
        (leastPolarWitnessFormula_defined (V := W) pos).iff ![z, δ₀, Q]
      rw [he]
      exact ⟨fun h ↦ h.unique hξ, fun h ↦ h ▸ hξ⟩
  -- `δ₀` is definable in the stage from `δ` and `Q`
  have hπ : IsStageDefinable θ δ Q (j m₀) := by
    refine isStageDefinable_of_reflect hrefl (ψ := kpairFirstFormula) (by simp [caseOneCodes])
      (hmemθ m₀) hδmem hQmem (fun z hz ↦ ?_)
    have he : kpairFirstFormula.Evalb ![z, δ, Q] ↔ z = kpair.π₁ Q :=
      (kpairFirstFormula_defined (V := W)).iff ![z, δ, Q]
    rw [he, hQ]
    simp
  have hδ₀def : IsStageDefinable θ δ Q δ₀ := isStageDefinable_trans_param hδmem hQmem hπ hm₀
  -- so `ξ` lies in `O`
  have hcore : stageDefinableParamCore j δ θ ξ :=
    ⟨mem_succ_iff.mpr (Or.inr (hδ₀δ ξ hξδ₀)), M,
      isStageDefinable_trans hδmem hQmem hδ₀def hξdef⟩
  -- and is old, by minimality of `δ₀`
  have hold : ∃ α : V, j α = ξ := by
    by_contra hno
    exact hleast.2.2 ξ hξδ₀ ⟨hcore, fun α hα ↦ hno ⟨α, hα⟩⟩
  obtain ⟨α, hα⟩ := hold
  have hαord : IsOrdinal α := (j.ordinal_iff α).mp (hα ▸ hξord)
  obtain ⟨y, hy, hpy⟩ := hξ.2.1
  have hyj : y ∈ j (hierarchy α) := by
    rw [hc.isPowersetPreserving.map_hierarchy α, hα]
    exact hy
  obtain ⟨y₀, -, rfl⟩ := (j.mem_map_iff (hierarchy α) y).mp hyj
  exact ⟨y₀, (hpolar (j y₀)).mp hpy⟩

/-- Enayat's Case I, second half: the image of the smaller model passes the Tarski test in the
stage `V_{δ₀}`. This is exactly the `helem` hypothesis of
`stageSatisfaction_isFullSatisfactionClass`. -/
theorem elementary_of_least {j : MembershipEndExtension V W} (hc : j.IsConservative)
    {δ θ δ₀ : W} [IsOrdinal δ] [IsOrdinal θ] (hδθ : δ ∈ θ) (hrefl : ReflectsCaseOne θ)
    (hleast : IsLeastStageDefinableParamNew j δ θ δ₀) :
    ∀ n φ b : V, IsMembershipFormulaCode (succ n) φ → IsFunction b → domain b = n →
      ((∀ y : V, MembershipSatisfies (hierarchy δ₀) (succ (j n)) (j φ)
            (assignmentPrepend (j n) (j b) (j y))) →
          ∀ x : W, x ∈ hierarchy δ₀ →
            MembershipSatisfies (hierarchy δ₀) (succ (j n)) (j φ)
              (assignmentPrepend (j n) (j b) x)) ∧
      ((∃ x : W, x ∈ hierarchy δ₀ ∧
            MembershipSatisfies (hierarchy δ₀) (succ (j n)) (j φ)
              (assignmentPrepend (j n) (j b) x)) →
          ∃ y : V, MembershipSatisfies (hierarchy δ₀) (succ (j n)) (j φ)
            (assignmentPrepend (j n) (j b) (j y))) := by
  intro n φ b _ _ _
  constructor
  · intro hall x hx
    by_contra hxs
    obtain ⟨y, hy⟩ := exists_old_polar_witness hc hδθ hrefl hleast false n φ b hx
      ((polarStage_false δ₀ (j n) (j φ) (j b) x).mpr hxs)
    exact (polarStage_false δ₀ (j n) (j φ) (j b) (j y)).mp hy (hall y)
  · rintro ⟨x, hx, hsat⟩
    obtain ⟨y, hy⟩ := exists_old_polar_witness hc hδθ hrefl hleast true n φ b hx
      ((polarStage_true δ₀ (j n) (j φ) (j b) x).mpr hsat)
    exact ⟨y, (polarStage_true δ₀ (j n) (j φ) (j b) (j y)).mp hy⟩

/-- Enayat's Theorem 4.4(b), Case I, in the conservative case: a conservative end extension of a
model of ZF has no least new stage-definable ordinal, once the stage `V_θ` is chosen by
reflection. -/
theorem false_of_least_stage {j : MembershipEndExtension V W} (hc : j.IsConservative)
    {δ θ δ₀ : W} [IsOrdinal δ] [IsOrdinal θ] (hδθ : δ ∈ θ) (hrefl : ReflectsCaseOne θ)
    (hleast : IsLeastStageDefinableParamNew j δ θ δ₀) : False :=
  false_of_elementary_stage hc δ₀ (map_mem_hierarchy_of_leastParam hc hleast)
    (elementary_of_least hc hδθ hrefl hleast)

/-- The reflecting stage exists, so Case I is impossible outright: above every ordinal of the
larger model there is a stage `V_θ` for which Enayat's `O'` has no least element. -/
theorem exists_stage_without_least {j : MembershipEndExtension V W} (hc : j.IsConservative)
    (δ : W) [IsOrdinal δ] :
    ∃ θ : W, IsOrdinal θ ∧ δ ∈ θ ∧ ∀ δ₀ : W, ¬ IsLeastStageDefinableParamNew j δ θ δ₀ := by
  obtain ⟨θ, hθ, hδθ, hrefl⟩ := exists_reflectsCaseOne δ
  have : IsOrdinal θ := hθ
  exact ⟨θ, hθ, hδθ, fun δ₀ hleast ↦ false_of_least_stage hc hδθ hrefl hleast⟩

end MembershipEndExtension

end ZFVP
