import ZFVP.ModelTheory.SchmerlInfinitaryTreeSentence
import ZFVP.SetTheory.UniformRecursion

/-! A fixed countable language and an actual infinitary sentence for the class
tree. Its reduct theorem yields rather classlessness in every ZF model satisfying
the sentence. The sentence contains no constants naming a particular forced model.
-/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory Set Order
open ZFVP.Infinitary (Formula)

universe u

def classNodeFormula : SetTheorySemisentence 1 :=
  f“p. ∃ s α, !IsOrdinal.dfn α ∧ s ⊆ !hierarchyFormula α ∧ p = !kpair.dfn s α”

def classOrderFormula : SetTheorySemisentence 2 :=
  f“p q. !kpair.π₂.dfn p ⊆ !kpair.π₂.dfn q ∧
    !kpair.π₁.dfn p = !inter.dfn (!kpair.π₁.dfn q) (!hierarchyFormula (!kpair.π₂.dfn p))”

def classRankFormula : SetTheorySemisentence 2 :=
  f“p α. p = !kpair.dfn (!kpair.π₁.dfn p) α”

def ordinalNodeFormula : SetTheorySemisentence 1 := f“α. !IsOrdinal.dfn α”

def ordinalOrderFormula : SetTheorySemisentence 2 := “α β. α ⊆ β”

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_classNodeFormula (p : V) :
    classNodeFormula.Evalb ![p] ↔ p ∈ Set.range (ClassTreeNode.code (V := V)) := by
  have he : classNodeFormula.Evalb ![p] ↔
      ∃ s α : V, IsOrdinal α ∧ s ⊆ hierarchy α ∧ p = ⟨s, α⟩ₖ := by
    simp [classNodeFormula]
  rw [he]
  constructor
  · rintro ⟨s, α, hα, hs, hp⟩
    exact ⟨⟨⟨α, hα⟩, s, hs⟩, hp.symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t.slice, t.level.val, t.level.ordinal, t.subset, rfl⟩

theorem eval_classOrderFormula (a b : ClassTreeNode V) :
    classOrderFormula.Evalb ![a.code, b.code] ↔ a ≤ b := by
  simp [classOrderFormula, ClassTreeNode.code, ClassTreeNode.le_def, SetTheory.Ordinal.le_def]

theorem eval_classRankFormula (t : ClassTreeNode V) (a : V) :
    classRankFormula.Evalb ![t.code, a] ↔ a = t.level.val := by
  simp [classRankFormula, ClassTreeNode.code, kpair_iff, eq_comm]

def ordinalCodeEmbedding : SetTheory.Ordinal V ↪ V where
  toFun := SetTheory.Ordinal.val
  inj' := by
    intro a b h
    cases a
    cases b
    cases h
    rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_ordinalNodeFormula (a : V) :
    ordinalNodeFormula.Evalb ![a] ↔ a ∈ Set.range (ordinalCodeEmbedding (V := V)) := by
  have he : ordinalNodeFormula.Evalb ![a] ↔ IsOrdinal a := by simp [ordinalNodeFormula]
  rw [he]
  exact ⟨fun h ↦ ⟨⟨a, h⟩, rfl⟩, fun ⟨b, he⟩ ↦ he ▸ b.ordinal⟩

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_ordinalOrderFormula (a b : SetTheory.Ordinal V) :
    ordinalOrderFormula.Evalb ![a.val, b.val] ↔ a ≤ b := by
  simp [ordinalOrderFormula, SetTheory.Ordinal.le_def]

/-- One selected-rank predicate and one color-graph relation. -/
inductive ClassExtraRelation : ℕ → Type where
  | selected : ClassExtraRelation 1
  | color : ClassExtraRelation 2

instance {n : ℕ} : Subsingleton (ClassExtraRelation n) where
  allEq a b := by cases a <;> cases b <;> rfl

noncomputable instance {n : ℕ} : Encodable (ClassExtraRelation n) :=
  Encodable.ofInj (fun _ ↦ ()) (fun _ _ _ ↦ Subsingleton.elim _ _)

def classExtraLanguage : Language := ⟨fun _ ↦ Empty, ClassExtraRelation⟩

noncomputable instance : classExtraLanguage.Encodable :=
  ⟨fun _ ↦ inferInstanceAs (Encodable Empty),
    fun n ↦ inferInstanceAs (Encodable (ClassExtraRelation n))⟩

def classLanguage : Language := Language.add ℒₛₑₜ classExtraLanguage

noncomputable instance : classLanguage.Encodable :=
  ⟨fun n ↦ inferInstanceAs (Encodable ((Language.Func ℒₛₑₜ n) ⊕ Empty)),
    fun n ↦ inferInstanceAs (Encodable ((Language.Rel ℒₛₑₜ n) ⊕ ClassExtraRelation n))⟩

def classLanguageEmbedding : ℒₛₑₜ →ᵥ classLanguage :=
  Language.Hom.add₁ ℒₛₑₜ classExtraLanguage

/-- An expansion of the original set structure by the chosen ranks and colors. -/
@[instance_reducible] def classExpansion (D : V → Prop) (f : V → V) : Structure classLanguage V where
  func := fun {_} F a ↦ match F with
    | Sum.inl F => Structure.func F a
    | Sum.inr F => Empty.elim F
  rel := fun {_} R a ↦ match R with
    | Sum.inl R => Structure.rel R a
    | Sum.inr R => match R with
      | .selected => D (a 0)
      | .color => a 0 = f (a 1)

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem classExpansion_reduct (D : V → Prop) (f : V → V) :
    (classExpansion D f).lMap classLanguageEmbedding =
      (inferInstance : Structure ℒₛₑₜ V) := rfl

def classOriginal {n : ℕ} (φ : SetTheorySemisentence n) : Formula classLanguage n :=
  .fo (φ.lMap classLanguageEmbedding)

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_classOriginal (D : V → Prop) (f : V → V) {n : ℕ}
    (φ : SetTheorySemisentence n) (b : Fin n → V) :
    @Formula.Eval classLanguage V (classExpansion D f) n (classOriginal φ) b ↔ φ.Evalb b :=
  Semiformula.eval_lMap

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_classOriginal_of_reduct (s : Structure classLanguage V)
    (hs : s.lMap classLanguageEmbedding = (inferInstance : Structure ℒₛₑₜ V))
    {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → V) :
    @Formula.Eval classLanguage V s n (classOriginal φ) b ↔ φ.Evalb b := by
  change (φ.lMap classLanguageEmbedding).Evalb (s := s) b ↔ φ.Evalb b
  calc
    _ ↔ φ.Evalb (s := s.lMap classLanguageEmbedding) b := Semiformula.eval_lMap
    _ ↔ φ.Evalb b := by rw [hs]

def classSelected : Formula classLanguage 1 :=
  .fo (.rel (Sum.inr ClassExtraRelation.selected) (fun i ↦ .bvar i))

def classColor : Formula classLanguage 2 :=
  .fo (.rel (Sum.inr ClassExtraRelation.color) (fun i ↦ .bvar i))

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_classSelected (D : V → Prop) (f : V → V) (a : V) :
    @Formula.Eval classLanguage V (classExpansion D f) 1 classSelected ![a] ↔ D a := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_classColor (D : V → Prop) (f : V → V) (c x : V) :
    @Formula.Eval classLanguage V (classExpansion D f) 2 classColor ![c, x] ↔ c = f x := Iff.rfl

/-- Totality and uniqueness ensure that any model's color relation is a graph. -/
def classColorTotal : Formula classLanguage 0 :=
  .all (.exs (.and classColor (.all (.imp (classColor.rename ![0, 2])
    ((classOriginal (“x y. x = y” : SetTheorySemisentence 2)).rename ![0, 1])))))

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_classColorTotal (s : Structure classLanguage V)
    (hs : s.lMap classLanguageEmbedding = (inferInstance : Structure ℒₛₑₜ V)) :
    @Formula.Eval classLanguage V s 0 classColorTotal ![] ↔
      ∀ x : V, ∃ c : V, @Formula.Eval classLanguage V s 2 classColor ![c, x] ∧
        ∀ d : V, @Formula.Eval classLanguage V s 2 classColor ![d, x] → d = c := by
  let : Structure classLanguage V := s
  have he (x y : V) :
      (classOriginal (“x y. x = y” : SetTheorySemisentence 2)).Eval ![x, y] ↔ x = y := by
    rw [eval_classOriginal_of_reduct s hs]
    simp
  simp [classColorTotal, Formula.eval_all, Formula.eval_exs, Formula.eval_and,
    Formula.eval_imp, Formula.eval_rename, he]

/-- The fixed class-tree sentence in the countable expanded language. -/
noncomputable def classTreeSentence : Formula classLanguage 0 :=
  .and classColorTotal (treeDefinitionSentence classLanguageEmbedding
    (classOriginal classNodeFormula) (classOriginal ordinalNodeFormula) classSelected
    (classOriginal classOrderFormula) (classOriginal ordinalOrderFormula)
    (classOriginal classRankFormula) classColor)

/-- Every ZF reduct of a standard model of this fixed sentence is rather
classless. The cofinality and coloring facts are consequences of satisfaction. -/
theorem ratherClassless_of_classTreeSentence (D : V → Prop) (f : V → V)
    (h : @Formula.Eval classLanguage V (classExpansion D f) 0 classTreeSentence ![]) :
    ∀ X : V → Prop, IsAmenableClass V X → ℒₛₑₜ-predicate[V] X := by
  let : Structure classLanguage V := classExpansion D f
  have htree := (Formula.eval_and _ _ _).mp h |>.2
  apply ratherClassless_iff_classTree_branches_definable.mpr
  have hb := branches_definable_of_treeDefinitionSentence classLanguageEmbedding
    (ClassTreeNode.rankedTree (V := V)) ClassTreeNode.codeEmbedding ordinalCodeEmbedding
    (fun t ↦ f t.code) (classOriginal classNodeFormula) (classOriginal ordinalNodeFormula)
    classSelected (classOriginal classOrderFormula) (classOriginal ordinalOrderFormula)
    (classOriginal classRankFormula) classColor
    (fun x ↦ (eval_classOriginal D f classNodeFormula ![x]).trans (eval_classNodeFormula x))
    (fun x ↦ (eval_classOriginal D f ordinalNodeFormula ![x]).trans (eval_ordinalNodeFormula x))
    (fun a b ↦ (eval_classOriginal D f classOrderFormula ![a.code, b.code]).trans
      (eval_classOrderFormula a b))
    (fun a b ↦ (eval_classOriginal D f ordinalOrderFormula ![a.val, b.val]).trans
      (eval_ordinalOrderFormula a b))
    (fun t a ↦ (eval_classOriginal D f classRankFormula ![t.code, a]).trans
      (eval_classRankFormula t a))
    (fun t c ↦ eval_classColor D f c t.code) htree
  exact hb

/-- The arbitrary-model reduct theorem: the sentence itself supplies its color
function, so no interpretation hypothesis for an added symbol remains. -/
theorem ratherClassless_of_classTreeSentence_model (s : Structure classLanguage V)
    (hs : s.lMap classLanguageEmbedding = (inferInstance : Structure ℒₛₑₜ V))
    (h : @Formula.Eval classLanguage V s 0 classTreeSentence ![]) :
    ∀ X : V → Prop, IsAmenableClass V X → ℒₛₑₜ-predicate[V] X := by
  classical
  let : Structure classLanguage V := s
  obtain ⟨htotal, htree⟩ := (Formula.eval_and _ _ _).mp h
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice ((eval_classColorTotal s hs).mp htotal)
  have hF (x c : V) : classColor.Eval ![c, x] ↔ c = f x := by
    exact ⟨fun hc ↦ (hf x).2 c hc, fun he ↦ he ▸ (hf x).1⟩
  apply ratherClassless_iff_classTree_branches_definable.mpr
  have hb := branches_definable_of_treeDefinitionSentence classLanguageEmbedding
    (ClassTreeNode.rankedTree (V := V)) ClassTreeNode.codeEmbedding ordinalCodeEmbedding
    (fun t ↦ f t.code) (classOriginal classNodeFormula) (classOriginal ordinalNodeFormula)
    classSelected (classOriginal classOrderFormula) (classOriginal ordinalOrderFormula)
    (classOriginal classRankFormula) classColor
    (fun x ↦ (eval_classOriginal_of_reduct s hs classNodeFormula ![x]).trans (eval_classNodeFormula x))
    (fun x ↦ (eval_classOriginal_of_reduct s hs ordinalNodeFormula ![x]).trans (eval_ordinalNodeFormula x))
    (fun a b ↦ (eval_classOriginal_of_reduct s hs classOrderFormula ![a.code, b.code]).trans
      (eval_classOrderFormula a b))
    (fun a b ↦ (eval_classOriginal_of_reduct s hs ordinalOrderFormula ![a.val, b.val]).trans
      (eval_ordinalOrderFormula a b))
    (fun t a ↦ (eval_classOriginal_of_reduct s hs classRankFormula ![t.code, a]).trans
      (eval_classRankFormula t a))
    (fun t c ↦ hF t.code c) htree
  dsimp only at hb
  rw [hs] at hb
  exact hb

end ZFVP.Schmerl
