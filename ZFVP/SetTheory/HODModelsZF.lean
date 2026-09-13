import ZFVP.SetTheory.OrdinalDefinabilityClosure
import ZFVP.SetTheory.ClassModelsZF

/-! The class of hereditarily ordinal definable sets relative to a parameter class is a transitive
model of ZF: it contains the ordinals and is closed under the ZF operations by the closure of
ordinal definability. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def pairFormula : SetTheorySemisentence 4 := f“w q₁ q₂ P. w = q₁ ∨ w = q₂”

def unionFormula : SetTheorySemisentence 4 := f“w q₁ q₂ P. ∃ u ∈ q₁, w ∈ u”

def powerFormula (Pf : SetTheorySemisentence 2) : SetTheorySemisentence 4 :=
  f“y q₁ q₂ P. !(hodFormula Pf) y P ∧ ∀ z ∈ y, z ∈ q₁”

/-- The guard `#0 ∈ &(some 0)` of a bound variable. -/
def memGuard (n : ℕ) : SetTheorySemiformula (Option ℕ) (n + 1) :=
  Rew.embSubsts ![Semiterm.bvar 0, Semiterm.fvar (some 0)] ▹ (“y x. y ∈ x” : SetTheorySemisentence 2)

/-- The class-relativized separation formula `#0 ∈ &(some 0) ∧ ψ^H`, with the free variables of
`ψ^H` shifted by one. -/
def sepClassFormula (H : SetTheorySemisentence 2) (ψ : SetTheorySemiformula ℕ 1) :
    SetTheorySemiformula (Option ℕ) 1 :=
  memGuard 0 ⋏ (Rew.rewriteMap (Option.map Nat.succ) ▹ relativizeClass H ψ)

/-- The class-relativized replacement image formula `H(#0, &none) ∧ ∃ z ∈ &(some 0), ψ^H(z, #0)`. -/
def replClassFormula (H : SetTheorySemisentence 2) (ψ : SetTheorySemiformula ℕ 2) :
    SetTheorySemiformula (Option ℕ) 1 :=
  classGuard H 0 ⋏ Semiformula.exs (memGuard 1 ⋏ (Rew.rewriteMap (Option.map Nat.succ) ▹ relativizeClass H ψ))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The parameter assignment with the class parameter at `none`, a set at `some 0` and a sequence
of sets at the remaining places. -/
def classParams (p x : V) (e : ℕ → V) : Option ℕ → V :=
  fun o ↦ o.elim p (fun j ↦ Nat.rec x (fun j' _ ↦ e j') j)

theorem classParams_shift (p x : V) (e : ℕ → V) :
    (fun o ↦ classParams p x e (Option.map Nat.succ o)) = fun o ↦ o.elim p e := by
  funext o
  cases o <;> rfl

theorem eval_pairFormula (w q₁ q₂ P : V) : pairFormula.Evalb ![w, q₁, q₂, P] ↔ w = q₁ ∨ w = q₂ := by
  simp [pairFormula]

theorem eval_unionFormula (w q₁ q₂ P : V) : unionFormula.Evalb ![w, q₁, q₂, P] ↔ ∃ u ∈ q₁, w ∈ u := by
  simp [unionFormula]

theorem eval_powerFormula (Pf : SetTheorySemisentence 2) (y q₁ q₂ P : V) :
    (powerFormula Pf).Evalb ![y, q₁, q₂, P] ↔ IsHOD Pf y P ∧ ∀ z ∈ y, z ∈ q₁ := by
  simp [powerFormula]

theorem eval_memGuard {n : ℕ} (x : V) (b : Fin n → V) (F : Option ℕ → V) :
    (memGuard n).Eval (x :> b) F ↔ x ∈ F (some 0) := by
  unfold memGuard
  rw [Semiformula.eval_embSubsts]
  have hv : (Semiterm.val (L := ℒₛₑₜ) (M := V) (x :> b) F ∘
      (![Semiterm.bvar 0, Semiterm.fvar (some 0)] : Fin 2 → SetTheorySemiterm (Option ℕ) (n + 1))) =
      ![x, F (some 0)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
  rw [hv]
  simp

theorem eval_classGuard' {ξ : Type*} {n : ℕ} (H : SetTheorySemisentence 2) (x : V) (b : Fin n → V)
    (F : Option ξ → V) : (classGuard H n).Eval (x :> b) F ↔ H.Evalb ![x, F none] := by
  unfold classGuard
  rw [Semiformula.eval_embSubsts]
  have hv : (Semiterm.val (L := ℒₛₑₜ) (M := V) (x :> b) F ∘
      (![Semiterm.bvar 0, Semiterm.fvar none] : Fin 2 → SetTheorySemiterm (Option ξ) (n + 1))) =
      ![x, F none] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
  rw [hv]

theorem eval_sepClassFormula (H : SetTheorySemisentence 2) (ψ : SetTheorySemiformula ℕ 1)
    (F : Option ℕ → V) (y : V) :
    (sepClassFormula H ψ).Eval ![y] F ↔
      y ∈ F (some 0) ∧ (relativizeClass H ψ).Eval ![y] (fun o ↦ F (Option.map Nat.succ o)) := by
  show (memGuard 0).Eval (y :> ![]) F ∧
    (Rew.rewriteMap (Option.map Nat.succ) ▹ relativizeClass H ψ).Eval ![y] F ↔ _
  rw [eval_memGuard, Semiformula.eval_rewriteMap]

theorem eval_replClassFormula (H : SetTheorySemisentence 2) (ψ : SetTheorySemiformula ℕ 2)
    (F : Option ℕ → V) (y : V) :
    (replClassFormula H ψ).Eval ![y] F ↔
      H.Evalb ![y, F none] ∧ ∃ z, z ∈ F (some 0) ∧
        (relativizeClass H ψ).Eval ![z, y] (fun o ↦ F (Option.map Nat.succ o)) := by
  show (classGuard H 0).Eval (y :> ![]) F ∧
    (∃ z : V, (memGuard 1).Eval (z :> ![y]) F ∧
      (Rew.rewriteMap (Option.map Nat.succ) ▹ relativizeClass H ψ).Eval ![z, y] F) ↔ _
  rw [eval_classGuard']
  apply and_congr_right
  intro _
  apply exists_congr
  intro z
  rw [eval_memGuard, Semiformula.eval_rewriteMap]

/-- The transitive closure of a set lies in the set together with the closures of its elements. -/
theorem transitiveClosure_subset_union (b : V) :
    transitiveClosure b ⊆ b ∪ ⋃ˢ (repl transitiveClosure transitiveClosure_definable b) := by
  apply transitiveClosure_minimal
  · exact fun y hy ↦ mem_union_iff.mpr (Or.inl hy)
  · refine ⟨fun w hw z hz ↦ ?_⟩
    rcases mem_union_iff.mp hw with hw | hw
    · exact mem_union_iff.mpr (Or.inr (mem_sUnion_iff.mpr ⟨transitiveClosure w,
        (repl_spec _).mpr ⟨w, hw, rfl⟩, subset_transitiveClosure w z hz⟩))
    · obtain ⟨C, hC, hwC⟩ := mem_sUnion_iff.mp hw
      obtain ⟨y, -, rfl⟩ := (repl_spec _).mp hC
      exact mem_union_iff.mpr (Or.inr (mem_sUnion_iff.mpr
        ⟨transitiveClosure y, hC, (transitiveClosure_transitive y).mem_trans hz hwC⟩))

section

variable (Pf : SetTheorySemisentence 2)

theorem hodClass_iff (p x : V) : classOf (hodFormula Pf) p x ↔ IsHOD Pf x p :=
  (hodFormula_defined Pf).iff ![x, p]

/-- An ordinal definable set of hereditarily ordinal definable sets is hereditarily ordinal
definable. -/
theorem isHOD_of_od {b p : V} (hb : IsOD Pf b p) (hmem : ∀ y ∈ b, IsHOD Pf y p) : IsHOD Pf b p := by
  refine ⟨hb, fun z hz ↦ ?_⟩
  rcases mem_union_iff.mp (transitiveClosure_subset_union b z hz) with hz | hz
  · exact (hmem z hz).1
  · obtain ⟨C, hC, hzC⟩ := mem_sUnion_iff.mp hz
    obtain ⟨y, hy, rfl⟩ := (repl_spec _).mp hC
    exact (hmem y hy).2 z hzC

theorem isHOD_of_ordinal (α p : V) [IsOrdinal α] : IsHOD Pf α p := by
  refine ⟨isOD_of_allowed Pf (Or.inl inferInstance), fun z hz ↦ ?_⟩
  have hsub : transitiveClosure α ⊆ α := transitiveClosure_minimal α α (fun x hx ↦ hx) inferInstance
  exact isOD_of_allowed Pf (Or.inl (IsOrdinal.of_mem (hsub z hz)))

theorem isHOD_of_hereditarily_allowed {x p : V} (hx : IsAllowed Pf x p)
    (h : ∀ y ∈ transitiveClosure x, IsAllowed Pf y p) : IsHOD Pf x p :=
  ⟨isOD_of_allowed Pf hx, fun y hy ↦ isOD_of_allowed Pf (h y hy)⟩

theorem hod_nonempty (p : V) : Nonempty (ClassDomain (classOf (hodFormula Pf) p)) :=
  ⟨⟨ω, (hodClass_iff Pf p _).mpr (isHOD_of_ordinal Pf ω p)⟩⟩

theorem sepPredicate_definable (H : SetTheorySemisentence 2) (a : V) (ψ : SetTheorySemiformula ℕ 1)
    (e : ℕ → ClassDomain (classOf H a)) :
    ℒₛₑₜ-predicate (fun y : V ↦ (relativizeClass H ψ).Eval ![y] (fun i ↦ i.elim a (fun j ↦ (e j).val))) := by
  apply Language.Definable.of_iff (relativizedClassEvaluation_definable H a ψ e)
  intro v
  have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  change (relativizeClass H ψ).Eval ![v 0] _ ↔ (relativizeClass H ψ).Eval v _
  rw [hv]

theorem classParams_od {p x : V} (hp : IsOD Pf p p) (hx : IsOD Pf x p) (e : ℕ → V)
    (he : ∀ j, IsOD Pf (e j) p) : ∀ o, IsOD Pf (classParams p x e o) p := by
  intro o
  cases o with
  | none => exact hp
  | some j =>
    cases j with
    | zero => exact hx
    | succ j' => exact he j'

/-- Relativized separation inside the hereditarily ordinal definable sets. -/
theorem hod_sep {p x : V} (hp : IsAllowed Pf p p) (hx : IsHOD Pf x p) (ψ : SetTheorySemiformula ℕ 1)
    (e : ℕ → ClassDomain (classOf (hodFormula Pf) p)) :
    IsHOD Pf (sep x (fun y ↦ (relativizeClass (hodFormula Pf) ψ).Eval ![y]
      (fun i ↦ i.elim p (fun j ↦ (e j).val))) (sepPredicate_definable (hodFormula Pf) p ψ e)) p := by
  refine isHOD_of_od Pf ?_ (fun y hy ↦ hx.mem Pf (mem_sep_iff.mp hy).1)
  refine isOD_of_classParameters Pf (sepClassFormula (hodFormula Pf) ψ)
    (classParams p x (fun j ↦ (e j).val))
    (classParams_od Pf (isOD_of_allowed Pf hp) (IsHOD.od Pf hx) _ (fun j ↦ IsHOD.od Pf ((hodClass_iff Pf p _).mp (e j).property)))
    ?_
  intro y
  rw [mem_sep_iff, eval_sepClassFormula, classParams_shift]
  exact Iff.rfl

/-- Relativized replacement images inside the hereditarily ordinal definable sets. -/
theorem hod_repl {p x b : V} (hp : IsAllowed Pf p p) (hx : IsHOD Pf x p) (ψ : SetTheorySemiformula ℕ 2)
    (e : ℕ → ClassDomain (classOf (hodFormula Pf) p))
    (hb : ∀ y, y ∈ b ↔ ∃ z ∈ x, IsHOD Pf y p ∧ (relativizeClass (hodFormula Pf) ψ).Eval ![z, y]
      (fun i ↦ i.elim p (fun j ↦ (e j).val))) : IsHOD Pf b p := by
  refine isHOD_of_od Pf ?_ (fun y hy ↦ by obtain ⟨z, -, hy', -⟩ := (hb y).mp hy; exact hy')
  refine isOD_of_classParameters Pf (replClassFormula (hodFormula Pf) ψ)
    (classParams p x (fun j ↦ (e j).val))
    (classParams_od Pf (isOD_of_allowed Pf hp) (IsHOD.od Pf hx) _ (fun j ↦ IsHOD.od Pf ((hodClass_iff Pf p _).mp (e j).property)))
    ?_
  intro y
  rw [hb y, eval_replClassFormula, classParams_shift, (hodFormula_defined Pf).iff]
  change (∃ z ∈ x, IsHOD Pf y p ∧ _) ↔ IsHOD Pf y p ∧ ∃ z, z ∈ x ∧ _
  constructor
  · rintro ⟨z, hz, hy, hzy⟩
    exact ⟨hy, z, hz, hzy⟩
  · rintro ⟨hy, z, hz, hzy⟩
    exact ⟨z, hz, hy, hzy⟩

/-- The hereditarily ordinal definable sets form a model of ZF. -/
theorem hod_models_zf (p : V) (hp : IsAllowed Pf p p)
    [Nonempty (ClassDomain (classOf (hodFormula Pf) p))] :
    (ClassDomain (classOf (hodFormula Pf) p))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  have hiff : ∀ x, classOf (hodFormula Pf) p x ↔ IsHOD Pf x p := hodClass_iff Pf p
  have hptree : IsParameterTree Pf p p := isParameterTree_of_allowed Pf hp
  refine classDomain_models_zf (hodFormula Pf) p ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx y hy
    exact (hiff y).mpr (((hiff x).mp hx).mem Pf hy)
  · exact (hiff ω).mpr (isHOD_of_ordinal Pf ω p)
  · intro x y hx hy
    rw [hiff] at hx hy ⊢
    refine isHOD_of_od Pf ?_ ?_
    · refine isOD_of_two Pf pairFormula hx.1 hy.1 hptree ?_
      intro w
      rw [eval_pairFormula, mem_insert, mem_singleton_iff]
    · intro w hw
      rcases mem_insert.mp hw with rfl | hw
      · exact hx
      · rw [mem_singleton_iff.mp hw]
        exact hy
  · intro x hx
    rw [hiff] at hx ⊢
    refine isHOD_of_od Pf ?_ ?_
    · refine isOD_of_two Pf unionFormula hx.1 hx.1 hptree ?_
      intro w
      rw [eval_unionFormula, mem_sUnion_iff]
    · intro w hw
      obtain ⟨u, hu, hwu⟩ := mem_sUnion_iff.mp hw
      exact (hx.mem Pf hu).mem Pf hwu
  · intro x hx
    rw [hiff] at hx
    refine ⟨sep (℘ x) (fun y ↦ IsHOD Pf y p) (isHOD_definable Pf p), ?_, ?_⟩
    · rw [hiff]
      refine isHOD_of_od Pf ?_ (fun y hy ↦ (mem_sep_iff.mp hy).2)
      refine isOD_of_two Pf (powerFormula Pf) hx.1 hx.1 hptree ?_
      intro y
      rw [eval_powerFormula, mem_sep_iff, mem_power_iff, and_comm]
      exact Iff.rfl
    · intro y
      rw [mem_sep_iff, mem_power_iff, hiff, and_comm]
  · intro ψ e x hx
    rw [hiff] at hx
    exact ⟨_, (hiff _).mpr (hod_sep Pf hp hx ψ e), fun y ↦ mem_sep_iff⟩
  · intro ψ e x hx hfun
    rw [hiff] at hx
    let R' : V → V → Prop := fun z y ↦ IsHOD Pf y p ∧
      (relativizeClass (hodFormula Pf) ψ).Eval ![z, y] (fun i ↦ i.elim p (fun j ↦ (e j).val))
    have hR' : ℒₛₑₜ-relation R' := by
      have h1 : Language.Definable ℒₛₑₜ (fun v : Fin 2 → V ↦ IsHOD Pf (v 1) p) :=
        Language.Definable.retraction (isHOD_definable Pf p) ![1]
      have h2 := relativizedClassEvaluation_definable (hodFormula Pf) p ψ e
      refine Language.Definable.of_iff (Language.Definable.and h1 h2) ?_
      intro v
      have hv : ![v 0, v 1] = v := by
        funext i
        exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
      show IsHOD Pf (v 1) p ∧ (relativizeClass (hodFormula Pf) ψ).Eval ![v 0, v 1] _ ↔
        IsHOD Pf (v 1) p ∧ (relativizeClass (hodFormula Pf) ψ).Eval v _
      rw [hv]
    have hex : ∀ z ∈ x, ∃! y, R' z y := by
      intro z hz
      obtain ⟨w, hw, huw⟩ := hfun z ((hiff z).mpr (hx.mem Pf hz))
      exact ⟨w, ⟨(hiff w).mp hw.1, hw.2⟩, fun y hy ↦ huw y ⟨(hiff y).mpr hy.1, hy.2⟩⟩
    obtain ⟨b, hb⟩ := replacement_rel_exists_of_mem_existsUnique x R' hex hR'
    refine ⟨b, (hiff b).mpr (hod_repl Pf hp hx ψ e hb), fun y ↦ ?_⟩
    rw [hb y, hiff]
    constructor
    · rintro ⟨z, hz, hy, hzy⟩
      exact ⟨hy, z, hz, hzy⟩
    · rintro ⟨hy, z, hz, hzy⟩
      exact ⟨z, hz, hy, hzy⟩

end

end ZFVP
