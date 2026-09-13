import ZFVP.ModelTheory.ConservativeRankExtension
import ZFVP.ModelTheory.DirectedElementaryUnion
import ZFVP.ModelTheory.CodedSequentSemantics
import ZFVP.Syntax.MembershipRenaming
import ZFVP.SetTheory.RankBounds

/-! Definability inside a rank stage and auxiliary intersections over old parameters.

`IsStageDefinable θ p q x` says that `x` is the unique element of the stage `hierarchy θ`
satisfying some internally coded three-variable formula there, the other two variables being
interpreted as `p` and `q`. This is an internal notion: it is a definable relation of the four
arguments, so Separation collects the stage-definable ordinals below a bound.

For an end extension `j : MembershipEndExtension V W`, `stageDefinableCore` collects the
ordinals `ξ ≤ δ` that are stage-definable from `δ` and `j m` for every old parameter `m`.
Enayat's class `O` uses some old parameter. That union and the actual proof of his
Theorem 4.4 are defined in `ElementaryStageCaseOne` as `stageDefinableParamCore`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Definability inside a rank stage -/

/-- `x` is defined over the stage `hierarchy θ` by the three-variable code `φ` with the two
parameters `p` and `q`: `x` lies in the stage and is the only element of the stage that satisfies
`φ` there when the second and third variables are read as `p` and `q`. -/
def DefinesInStage (θ p q φ x : V) : Prop :=
  x ∈ hierarchy θ ∧ ∀ z ∈ hierarchy θ,
    (MembershipSatisfies (hierarchy θ) ((3 : ℕ) : V) φ (standardTuple ![z, p, q]) ↔ z = x)

/-- `x` is definable in the structure `(hierarchy θ, ∈)` from the parameters `p` and `q`. -/
def IsStageDefinable (θ p q x : V) : Prop :=
  ∃ φ : V, IsMembershipFormulaCode ((3 : ℕ) : V) φ ∧ DefinesInStage θ p q φ x

theorem standardTuple_three (z p q : V) :
    standardTuple ![z, p, q] =
      assignmentPrepend ((2 : ℕ) : V)
        (assignmentPrepend ((1 : ℕ) : V) (assignmentPrepend ((0 : ℕ) : V) ∅ q) p) z := by
  simp [standardTuple]

instance definesInStage_definable : ℒₛₑₜ-relation₅[V] DefinesInStage := by
  unfold DefinesInStage
  simp only [standardTuple_three]
  definability

instance isStageDefinable_definable : ℒₛₑₜ-relation₄[V] IsStageDefinable := by
  unfold IsStageDefinable
  definability

/-- A code defines at most one element of the stage. -/
theorem DefinesInStage.unique {θ p q φ x y : V} (hx : DefinesInStage θ p q φ x)
    (hy : DefinesInStage θ p q φ y) : x = y :=
  ((hx.2 y hy.1).mp ((hy.2 y hy.1).mpr rfl)).symm

/-- A stage-definable element lies in the stage. -/
theorem IsStageDefinable.mem_hierarchy {θ p q x : V} (h : IsStageDefinable θ p q x) :
    x ∈ hierarchy θ := by
  obtain ⟨_, _, hd⟩ := h
  exact hd.1

/-- The stage-definable elements of a set form a set. -/
theorem exists_stageDefinable_sep (θ p q a : V) :
    ∃ S : V, ∀ ξ, ξ ∈ S ↔ ξ ∈ a ∧ IsStageDefinable θ p q ξ :=
  ⟨sep a (fun ξ ↦ IsStageDefinable θ p q ξ) (by definability), fun _ ↦ mem_sep_iff⟩

/-! ### Non-vacuity: a parameter is definable from itself -/

/-- The three-variable formula saying that the first variable equals the second. -/
def firstEqualsSecond : SetTheorySemisentence 3 := f“x p q. x = p”

theorem definesInStage_firstEqualsSecond {θ p q : V} (hp : p ∈ hierarchy θ)
    (hq : q ∈ hierarchy θ) :
    DefinesInStage θ p q (encodeMembershipFormula firstEqualsSecond) p := by
  have hA : IsNonempty (hierarchy θ) := ⟨⟨p, hp⟩⟩
  refine ⟨hp, fun z hz ↦ ?_⟩
  have hval : (fun i ↦ ((![⟨z, hz⟩, ⟨p, hp⟩, ⟨q, hq⟩] :
      Fin 3 → SetDomain (hierarchy θ)) i).val) = ![z, p, q] := by
    funext i
    exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ i.elim0) i) i) i
  have h := membershipSatisfies_encode (A := hierarchy θ) hA firstEqualsSecond
    ![⟨z, hz⟩, ⟨p, hp⟩, ⟨q, hq⟩]
  rw [hval] at h
  rw [h]
  simp only [firstEqualsSecond]
  constructor
  · intro hzp
    replace hzp : ∀ x : SetDomain (hierarchy θ), x = ⟨z, hz⟩ →
        ∀ y : SetDomain (hierarchy θ), y = ⟨p, hp⟩ → x = y := by simpa using hzp
    exact congrArg Subtype.val (hzp _ rfl _ rfl)
  · intro hzp
    have hall : ∀ x : SetDomain (hierarchy θ), x = ⟨z, hz⟩ →
        ∀ y : SetDomain (hierarchy θ), y = ⟨p, hp⟩ → x = y := by
      rintro _ rfl _ rfl
      exact Subtype.ext hzp
    simpa using hall

/-- An element of the stage is definable in it from itself. -/
theorem isStageDefinable_self {θ p q : V} (hp : p ∈ hierarchy θ) (hq : q ∈ hierarchy θ) :
    IsStageDefinable θ p q p :=
  ⟨encodeMembershipFormula firstEqualsSecond,
    (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem firstEqualsSecond),
    definesInStage_firstEqualsSecond hp hq⟩

/-- The three-variable formula saying that the first variable is the union of the second. -/
def firstIsUnionOfSecond : SetTheorySemisentence 3 :=
  f“x p q. (∀ z ∈ x, ∃ w ∈ p, z ∈ w) ∧ (∀ w ∈ p, ∀ z ∈ w, z ∈ x)”

theorem definesInStage_sUnion {θ p q : V} [IsOrdinal θ] (hp : p ∈ hierarchy θ)
    (hq : q ∈ hierarchy θ) :
    DefinesInStage θ p q (encodeMembershipFormula firstIsUnionOfSecond) (⋃ˢ p) := by
  have hA : IsNonempty (hierarchy θ) := ⟨⟨p, hp⟩⟩
  have htr : IsTransitive (hierarchy θ) := hierarchy_transitive θ
  have hup : (⋃ˢ p : V) ∈ hierarchy θ := by
    obtain ⟨β, hβ, hpβ⟩ := (mem_hierarchy_iff_of_ordinal θ p).mp hp
    have : IsOrdinal β := IsOrdinal.of_mem hβ
    refine (mem_hierarchy_iff_of_ordinal θ _).mpr ⟨β, hβ, fun z hz ↦ ?_⟩
    obtain ⟨w, hw, hzw⟩ := mem_sUnion_iff.mp hz
    exact (hierarchy_transitive β).transitive w (hpβ w hw) z hzw
  refine ⟨hup, fun z hz ↦ ?_⟩
  have hval : (fun i ↦ ((![⟨z, hz⟩, ⟨p, hp⟩, ⟨q, hq⟩] :
      Fin 3 → SetDomain (hierarchy θ)) i).val) = ![z, p, q] := by
    funext i
    exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ i.elim0) i) i) i
  have h := membershipSatisfies_encode (A := hierarchy θ) hA firstIsUnionOfSecond
    ![⟨z, hz⟩, ⟨p, hp⟩, ⟨q, hq⟩]
  rw [hval] at h
  rw [h]
  simp only [firstIsUnionOfSecond]
  constructor
  · intro hsat
    obtain ⟨h1, h2⟩ : (∀ x : SetDomain (hierarchy θ), x = ⟨z, hz⟩ → ∀ y ∈ x,
          ∀ x' : SetDomain (hierarchy θ), x' = ⟨p, hp⟩ → ∃ w ∈ x', y ∈ w) ∧
        (∀ x : SetDomain (hierarchy θ), x = ⟨p, hp⟩ → ∀ w ∈ x, ∀ y ∈ w,
          ∀ x' : SetDomain (hierarchy θ), x' = ⟨z, hz⟩ → y ∈ x') := by simpa using hsat
    apply mem_ext
    intro y
    rw [mem_sUnion_iff]
    constructor
    · intro hy
      obtain ⟨w, hw, hyw⟩ := h1 _ rfl ⟨y, htr.transitive z hz y hy⟩ hy _ rfl
      exact ⟨w.val, hw, hyw⟩
    · rintro ⟨w, hw, hyw⟩
      have hwθ : w ∈ hierarchy θ := htr.transitive p hp w hw
      exact h2 _ rfl ⟨w, hwθ⟩ hw ⟨y, htr.transitive w hwθ y hyw⟩ hyw _ rfl
  · rintro rfl
    have hall : (∀ x : SetDomain (hierarchy θ), x = ⟨⋃ˢ p, hz⟩ → ∀ y ∈ x,
          ∀ x' : SetDomain (hierarchy θ), x' = ⟨p, hp⟩ → ∃ w ∈ x', y ∈ w) ∧
        (∀ x : SetDomain (hierarchy θ), x = ⟨p, hp⟩ → ∀ w ∈ x, ∀ y ∈ w,
          ∀ x' : SetDomain (hierarchy θ), x' = ⟨⋃ˢ p, hz⟩ → y ∈ x') := by
      constructor
      · rintro _ rfl y hy _ rfl
        obtain ⟨w, hw, hyw⟩ := mem_sUnion_iff.mp hy
        exact ⟨⟨w, htr.transitive p hp w hw⟩, hw, hyw⟩
      · rintro _ rfl w hw y hy _ rfl
        exact mem_sUnion_iff.mpr ⟨w.val, hw, hy⟩
    simpa using hall

/-- The union of a parameter is definable in the stage from that parameter. -/
theorem isStageDefinable_sUnion {θ p q : V} [IsOrdinal θ] (hp : p ∈ hierarchy θ)
    (hq : q ∈ hierarchy θ) : IsStageDefinable θ p q (⋃ˢ p) :=
  ⟨encodeMembershipFormula firstIsUnionOfSecond,
    (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem firstIsUnionOfSecond),
    definesInStage_sUnion hp hq⟩

/-! ### Chaining two definitions

Enayat's Case I needs: if `u` is definable in the stage from `p, q` and `x` is definable in the
stage from `u, q`, then `x` is definable in the stage from `p, q`. The witnessing code is
`∃ v (χ[v, p, q] ∧ ρ[x, v, q])`, built with the internal existential quantifier, the internal
conjunction and the internal renaming of bound variables. -/

/-- Composing an internal renaming with a tuple reads off the renamed entries. -/
theorem compose_index_tuple (v : Fin 4 → V) (f : Fin 3 → Fin 4) (g : Fin 3 → V)
    (hg : ∀ k, g k = v (f k)) :
    compose (standardTuple (fun k ↦ (((f k).val : ℕ) : V))) (standardTuple v) = standardTuple g := by
  rw [compose_standardTuple _ _ (fun k ↦ by
    rw [domain_standardTuple]; exact natCast_mem_of_lt (f k).isLt)]
  congr 1
  funext k
  rw [value_standardTuple v (f k), hg k]

/-- Prepending to an assignment is prepending to the tuple. -/
theorem standardTuple_prepend {n : ℕ} (x : V) (b : Fin n → V) :
    standardTuple (x :> b) = assignmentPrepend ((n : ℕ) : V) (standardTuple b) x := by
  simp [standardTuple]

/-- The code of a renaming of three variables into four is an internal function `3 → 4`. -/
theorem index_tuple_mem (f : Fin 3 → Fin 4) :
    standardTuple (fun k ↦ (((f k).val : ℕ) : V)) ∈ ((4 : ℕ) : V) ^ ((3 : ℕ) : V) :=
  standardTuple_mem_function _ (fun k ↦ natCast_mem_of_lt (f k).isLt)

/-- Definability in a stage chains through a definable parameter. -/
theorem isStageDefinable_trans {θ p q u x : V} (hp : p ∈ hierarchy θ) (hq : q ∈ hierarchy θ)
    (hu : IsStageDefinable θ p q u) (hx : IsStageDefinable θ u q x) :
    IsStageDefinable θ p q x := by
  obtain ⟨χ, hχc, hχ⟩ := hu
  obtain ⟨ρ, hρc, hρ⟩ := hx
  have huA : u ∈ hierarchy θ := hχ.1
  have hxA : x ∈ hierarchy θ := hρ.1
  have hA : IsNonempty (hierarchy θ) := ⟨⟨u, huA⟩⟩
  have h3 : ((3 : ℕ) : V) ∈ (ω : V) := ofNat_mem_ω 3
  have h4 : ((4 : ℕ) : V) ∈ (ω : V) := ofNat_mem_ω 4
  -- the two renamings, sending the three variables of `χ` and `ρ` into a four-variable context
  -- whose variables are, in order, the bound witness `v`, then `x`, `p`, `q`
  set fχ : Fin 3 → Fin 4 := ![⟨0, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩] with hfχ
  set fρ : Fin 3 → Fin 4 := ![⟨1, by omega⟩, ⟨0, by omega⟩, ⟨3, by omega⟩] with hfρ
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
            (standardTuple ![z, w, q]))) := by
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
      compose_index_tuple ![w, z, p, q] fρ ![z, w, q]
        (fun k ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
          (fun k ↦ k.elim0) k) k) k)]
    exact and_congr_left' (hχ.2 w hw)
  constructor
  · rintro ⟨w, hw, hsat⟩
    obtain ⟨rfl, hρsat⟩ := (key w hw).mp hsat
    exact (hρ.2 z hz).mp hρsat
  · intro hzx
    exact ⟨u, huA, (key u huA).mpr ⟨rfl, (hρ.2 z hz).mpr hzx⟩⟩

/-! ### Intersection over old parameters -/

namespace MembershipEndExtension

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The auxiliary intersection: ordinals `ξ ≤ δ` definable in `(V_θ, ∈)` from `δ`
together with each single old parameter. The actual Enayat argument uses the union
`stageDefinableParamCore` in `ElementaryStageCaseOne`. -/
def stageDefinableCore (j : MembershipEndExtension V W) (δ θ : W) : W → Prop :=
  fun ξ ↦ ξ ∈ succ δ ∧ ∀ m : V, IsStageDefinable θ δ (j m) ξ

/-- The part of the auxiliary intersection outside the image of the smaller model. -/
def stageDefinableNew (j : MembershipEndExtension V W) (δ θ : W) : W → Prop :=
  fun ξ ↦ stageDefinableCore j δ θ ξ ∧ ∀ α : V, j α ≠ ξ

theorem stageDefinableNew.core {j : MembershipEndExtension V W} {δ θ ξ : W}
    (h : stageDefinableNew j δ θ ξ) : stageDefinableCore j δ θ ξ := h.1

/-- Every old set sits inside the stage of a new ordinal: a conservative end extension is a rank
extension, so the rank of an old set is below the rank of a new ordinal, which is that ordinal. -/
theorem map_mem_hierarchy_of_new {j : MembershipEndExtension V W} (h : j.IsConservative)
    {δ : W} [IsOrdinal δ] (hnew : ∀ α : V, j α ≠ δ) (x : V) : j x ∈ hierarchy δ := by
  rw [mem_hierarchy_iff_rank_mem]
  simpa only [rank_of_ordinal] using h.isRankExtension x δ hnew

/-- `δ` belongs to the auxiliary intersection when every old set lies in `V_θ`. -/
theorem stageDefinableCore_self (j : MembershipEndExtension V W) {δ θ : W} [IsOrdinal δ]
    [IsOrdinal θ] (hδθ : δ ∈ θ) (hmem : ∀ m : V, j m ∈ hierarchy θ) :
    stageDefinableCore j δ θ δ := by
  have hδ : δ ∈ hierarchy θ := by
    rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]
    exact hδθ
  exact ⟨mem_succ_self δ, fun m ↦ isStageDefinable_self hδ (hmem m)⟩

/-- A new ordinal `δ` belongs to `stageDefinableNew`, which is therefore nonempty. -/
theorem stageDefinableNew_self {j : MembershipEndExtension V W} (h : j.IsConservative)
    {δ θ : W} [IsOrdinal δ] [IsOrdinal θ] (hδθ : δ ∈ θ) (hnew : ∀ α : V, j α ≠ δ) :
    stageDefinableNew j δ θ δ :=
  ⟨stageDefinableCore_self j hδθ (fun m ↦ hierarchy_mono
    (IsOrdinal.toIsTransitive.transitive δ hδθ) _ (map_mem_hierarchy_of_new h hnew m)), hnew⟩

/-! ### A least new element of the auxiliary intersection -/

/-- `δ₀` is the least new element of the auxiliary intersection. -/
def IsLeastStageDefinableNew (j : MembershipEndExtension V W) (δ θ δ₀ : W) : Prop :=
  IsOrdinal δ₀ ∧ stageDefinableNew j δ θ δ₀ ∧ ∀ ξ ∈ δ₀, ¬ stageDefinableNew j δ θ ξ

/-- The image of the smaller model is contained in `V_{δ₀}`. The least element of
`stageDefinableNew` is a new ordinal, and a conservative end extension is a
rank extension, so the rank of every old set is below it. -/
theorem map_mem_hierarchy_of_least {j : MembershipEndExtension V W} (h : j.IsConservative)
    {δ θ δ₀ : W} (hleast : IsLeastStageDefinableNew j δ θ δ₀) (x : V) : j x ∈ hierarchy δ₀ :=
  have : IsOrdinal δ₀ := hleast.1
  map_mem_hierarchy_of_new h hleast.2.1.2 x

/-- The least new element of the auxiliary intersection is a limit ordinal.
If `δ₀` were `succ γ` then `γ = ⋃ δ₀` would be definable
in the stage from `δ₀`, hence, chaining, from `δ` and each old parameter; and `γ` would be new,
since `j (succ α) = succ (j α)`. So `γ` would be a member of `δ₀` in `stageDefinableNew`. -/
theorem isLimitOrdinal_of_least {j : MembershipEndExtension V W} {δ θ δ₀ : W}
    [IsOrdinal δ] [IsOrdinal θ] (hδθ : δ ∈ θ) (hmem : ∀ m : V, j m ∈ hierarchy θ)
    (hleast : IsLeastStageDefinableNew j δ θ δ₀) : IsLimitOrdinal δ₀ := by
  haveI hδ₀ord : IsOrdinal δ₀ := hleast.1
  have hδmem : δ ∈ hierarchy θ := by
    rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]; exact hδθ
  have hδ₀θ : δ₀ ∈ θ := by
    rcases mem_succ_iff.mp hleast.2.1.1.1 with rfl | hlt
    · exact hδθ
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hδθ
  have hδ₀mem : δ₀ ∈ hierarchy θ := by
    rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]; exact hδ₀θ
  rcases ordinal_cases δ₀ with h0 | ⟨γ, hγ, hsucc⟩ | hlim
  · exact absurd (h0 ▸ j.map_empty) (hleast.2.1.2 ∅)
  · exfalso
    haveI : IsOrdinal γ := hγ
    haveI : IsTransitive γ := IsOrdinal.toIsTransitive
    have hγmem : γ ∈ δ₀ := by rw [hsucc]; exact mem_succ_self γ
    have hunion : (⋃ˢ δ₀ : W) = γ := by
      rw [hsucc]; exact sUnion_succ_of_transitive (n := γ)
    refine hleast.2.2 γ hγmem ⟨⟨?_, fun m ↦ ?_⟩, fun α hα ↦ ?_⟩
    · exact IsOrdinal.toIsTransitive.mem_trans hγmem hleast.2.1.1.1
    · have hdef : IsStageDefinable θ δ₀ (j m) γ := by
        rw [← hunion]; exact isStageDefinable_sUnion hδ₀mem (hmem m)
      exact isStageDefinable_trans hδmem (hmem m) (hleast.2.1.1.2 m) hdef
    · refine hleast.2.1.2 (succ α) ?_
      rw [j.map_succ, hα, ← hsucc]
  · exact hlim

/-! ### Where the two cases are finished

The second half of Case I, the Tarski criterion, is proved in
`ZFVP.ModelTheory.ElementaryStageCaseOne`, and Case II, Enayat's reflection argument, in
`ZFVP.ModelTheory.NoConservativeEndExtension`. Together they give Enayat's Theorem 5.1,
`ZFVP.no_conservative_proper_end_extension`.

Case I uses the union over old parameters. Its argument produces an ordinal definable in
`(V_θ, ∈)` from `δ` and the single old parameter that codes the formula and the assignment, and
there is no reason for that ordinal to be definable from `δ` and an arbitrary old parameter. So
`ElementaryStageCaseOne` replaces the intersection over old parameters in `stageDefinableCore` by
the union, `stageDefinableParamCore`; `stageDefinableNew.param` sends the class defined here into
that one. The results proved above about the least element of `stageDefinableNew`, the containment
`j x ∈ V_{δ₀}` and the limit-ordinal property of `δ₀`, are reproved there for the union form.

Why `θ` cannot stay arbitrary is already visible here. Case I needs the least ordinal `ξ` whose
stage holds a failing witness to be definable in `(V_θ, ∈)`, and the property defining `ξ`
mentions `MembershipSatisfies` over the stage `V_{δ₀}`. `MembershipSatisfies` is not a bounded
predicate, so `V_θ` does not compute it correctly for an arbitrary `θ` above `δ`. The fix is to
choose `θ` by reflection rather than take it arbitrary. `ReflectsCaseOne θ` says that `V_θ` is
correct for the fixed finite list of formulas that spell out "`x` is the least ordinal with a
failing witness in `V_x`", and `exists_reflectsCaseOne` produces such a `θ` above any prescribed
ordinal. The coded formula and the assignment enter those formulas only as parameters, so one `θ`
serves all of them. -/

end MembershipEndExtension
end ZFVP
