import ZFVP.SetTheory.HODModelsZF
import ZFVP.SetTheory.CantorSpace
import ZFVP.SetTheory.PerfectSetCore
import ZFVP.SetTheory.InverseFunction
import ZFVP.SetTheory.SplittingScheme

/-! Reals-coded objects are hereditarily ordinal definable when the reals are allowed
parameters: pairs of HOD sets, reals, finite binary sequences and sets of them, sequences of
finite sequences, sequences of sets of finite sequences and sequences of reals. The codings use an
allowed injection of the finite binary sequences into `ω` and an allowed pairing of `ω × ω` into
`ω` (in the application both lie in the ground model). -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def seqCodeFormula : SetTheorySemisentence 4 :=
  f“y c k P. ∃ s ∈ !binarySequencesFormula, !value.dfn c s = k ∧ y ∈ s”

def subsetCodeFormula : SetTheorySemisentence 4 :=
  f“y c r P. y ∈ !binarySequencesFormula ∧ !value.dfn r (!value.dfn c y) = !succ.dfn (!isEmpty)”

def funCodeFormula : SetTheorySemisentence 4 :=
  f“q r z P. ∃ n ∈ !isω, ∃ s ∈ !binarySequencesFormula, q = !kpair.dfn n s ∧
    !value.dfn r (!value.dfn (!kpair.π₂.dfn P) (!kpair.dfn n (!value.dfn (!kpair.π₁.dfn P) s))) =
      !succ.dfn (!isEmpty)”

def powFunCodeFormula : SetTheorySemisentence 4 :=
  f“q r z P. ∃ n ∈ !isω, ∃ T ∈ !power.dfn (!binarySequencesFormula), q = !kpair.dfn n T ∧
    ∀ s ∈ !binarySequencesFormula, (s ∈ T ↔
      !value.dfn r (!value.dfn (!kpair.π₂.dfn P) (!kpair.dfn n (!value.dfn (!kpair.π₁.dfn P) s))) =
        !succ.dfn (!isEmpty))”

def realSeqCodeFormula : SetTheorySemisentence 4 :=
  f“q r z P. ∃ n ∈ !isω, ∃ x ∈ !cantorSpaceFormula, q = !kpair.dfn n x ∧
    ∀ m ∈ !isω, (!value.dfn x m = !succ.dfn (!isEmpty) ↔
      !value.dfn r (!value.dfn P (!kpair.dfn n m)) = !succ.dfn (!isEmpty))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_seqCodeFormula (y c k P : V) :
    seqCodeFormula.Evalb ![y, c, k, P] ↔ ∃ s ∈ binarySequences V, c ‘ s = k ∧ y ∈ s := by
  simp [seqCodeFormula]

theorem eval_subsetCodeFormula (y c r P : V) :
    subsetCodeFormula.Evalb ![y, c, r, P] ↔ y ∈ binarySequences V ∧ r ‘ (c ‘ y) = succ ∅ := by
  simp [subsetCodeFormula]

theorem eval_funCodeFormula (q r z P : V) :
    funCodeFormula.Evalb ![q, r, z, P] ↔ ∃ n ∈ (ω : V), ∃ s ∈ binarySequences V, q = ⟨n, s⟩ₖ ∧
      r ‘ ((kpair.π₂ P) ‘ ⟨n, (kpair.π₁ P) ‘ s⟩ₖ) = succ ∅ := by
  simp [funCodeFormula]

theorem eval_powFunCodeFormula (q r z P : V) :
    powFunCodeFormula.Evalb ![q, r, z, P] ↔ ∃ n ∈ (ω : V), ∃ T ∈ ℘ (binarySequences V), q = ⟨n, T⟩ₖ ∧
      ∀ s ∈ binarySequences V, (s ∈ T ↔ r ‘ ((kpair.π₂ P) ‘ ⟨n, (kpair.π₁ P) ‘ s⟩ₖ) = succ ∅) := by
  simp [powFunCodeFormula]

theorem eval_realSeqCodeFormula (q r z P : V) :
    realSeqCodeFormula.Evalb ![q, r, z, P] ↔ ∃ n ∈ (ω : V), ∃ x ∈ cantorSpace V, q = ⟨n, x⟩ₖ ∧
      ∀ m ∈ (ω : V), (x ‘ m = succ ∅ ↔ r ‘ (P ‘ ⟨n, m⟩ₖ) = succ ∅) := by
  simp [realSeqCodeFormula]

/-- The characteristic function of a set of naturals. -/
noncomputable def charFun (S : V) : V :=
  (S ×ˢ ({succ ∅} : V)) ∪ (((ω : V) \ S) ×ˢ ({∅} : V))

theorem mem_charFun_iff (S q : V) :
    q ∈ charFun S ↔ (∃ k ∈ S, q = ⟨k, succ ∅⟩ₖ) ∨ (∃ k ∈ (ω : V), k ∉ S ∧ q = ⟨k, ∅⟩ₖ) := by
  unfold charFun
  rw [mem_union_iff]
  constructor
  · rintro (hq | hq)
    · obtain ⟨k, hk, i, hi, rfl⟩ := mem_prod_iff.mp hq
      rw [mem_singleton_iff] at hi
      exact Or.inl ⟨k, hk, by rw [hi]⟩
    · obtain ⟨k, hk, i, hi, rfl⟩ := mem_prod_iff.mp hq
      rw [mem_singleton_iff] at hi
      obtain ⟨hk, hkS⟩ := mem_sdiff_iff.mp hk
      exact Or.inr ⟨k, hk, hkS, by rw [hi]⟩
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, hkS, rfl⟩)
    · exact Or.inl (kpair_mem_iff.mpr ⟨hk, mem_singleton_iff.mpr rfl⟩)
    · exact Or.inr (kpair_mem_iff.mpr ⟨mem_sdiff_iff.mpr ⟨hk, hkS⟩, mem_singleton_iff.mpr rfl⟩)

theorem succ_empty_ne_empty' : (succ ∅ : V) ≠ ∅ :=
  fun h ↦ not_mem_empty (h ▸ mem_succ_self (∅ : V))

theorem charFun_mem_cantorSpace {S : V} (hS : S ⊆ (ω : V)) : charFun S ∈ cantorSpace V := by
  rw [mem_cantorSpace_iff, mem_function_iff]
  constructor
  · intro q hq
    rcases (mem_charFun_iff S q).mp hq with ⟨k, hk, rfl⟩ | ⟨k, hk, -, rfl⟩
    · exact kpair_mem_iff.mpr ⟨hS k hk, (mem_two_iff _).mpr (Or.inr rfl)⟩
    · exact kpair_mem_iff.mpr ⟨hk, (mem_two_iff _).mpr (Or.inl rfl)⟩
  · intro k hk
    by_cases hkS : k ∈ S
    · refine ⟨succ ∅, (mem_charFun_iff S _).mpr (Or.inl ⟨k, hkS, rfl⟩), fun y hy ↦ ?_⟩
      rcases (mem_charFun_iff S _).mp hy with ⟨k', -, he⟩ | ⟨k', -, hk'S, he⟩
      · exact (kpair_inj he).2
      · exact (hk'S ((kpair_inj he).1 ▸ hkS)).elim
    · refine ⟨∅, (mem_charFun_iff S _).mpr (Or.inr ⟨k, hk, hkS, rfl⟩), fun y hy ↦ ?_⟩
      rcases (mem_charFun_iff S _).mp hy with ⟨k', hk', he⟩ | ⟨k', -, -, he⟩
      · exact (hkS ((kpair_inj he).1 ▸ hk')).elim
      · exact (kpair_inj he).2

theorem charFun_value {S k : V} (hS : S ⊆ (ω : V)) (hk : k ∈ (ω : V)) :
    (charFun S) ‘ k = succ ∅ ↔ k ∈ S := by
  have : IsFunction (charFun S) := IsFunction.of_mem ((mem_cantorSpace_iff _).mp (charFun_mem_cantorSpace hS))
  constructor
  · intro h
    by_contra hkS
    have h0 : (charFun S) ‘ k = ∅ :=
      value_eq_of_kpair_mem ((mem_charFun_iff S _).mpr (Or.inr ⟨k, hk, hkS, rfl⟩))
    exact succ_empty_ne_empty' (h.symm.trans h0)
  · intro hkS
    exact value_eq_of_kpair_mem ((mem_charFun_iff S _).mpr (Or.inl ⟨k, hkS, rfl⟩))

/-- Two reals with the same values are equal. -/
theorem cantorSpace_ext {x y : V} (hx : x ∈ cantorSpace V) (hy : y ∈ cantorSpace V)
    (h : ∀ m ∈ (ω : V), x ‘ m = y ‘ m) : x = y := by
  have hxf : IsFunction x := IsFunction.of_mem ((mem_cantorSpace_iff x).mp hx)
  have hyf : IsFunction y := IsFunction.of_mem ((mem_cantorSpace_iff y).mp hy)
  have hxd : domain x = (ω : V) := domain_eq_of_mem_function ((mem_cantorSpace_iff x).mp hx)
  have hyd : domain y = (ω : V) := domain_eq_of_mem_function ((mem_cantorSpace_iff y).mp hy)
  apply mem_ext
  intro q
  constructor
  · intro hq
    obtain ⟨m, hm, i, -, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp ((mem_cantorSpace_iff x).mp hx)).1 q hq)
    have hi : i = x ‘ m := (value_eq_of_kpair_mem hq).symm
    rw [hi, h m hm]
    exact kpair_value_mem (by rw [hyd]; exact hm)
  · intro hq
    obtain ⟨m, hm, i, -, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp ((mem_cantorSpace_iff y).mp hy)).1 q hq)
    have hi : i = y ‘ m := (value_eq_of_kpair_mem hq).symm
    rw [hi, ← h m hm]
    exact kpair_value_mem (by rw [hxd]; exact hm)

theorem two_value_eq {x y m : V} (hx : x ∈ cantorSpace V) (hy : y ∈ cantorSpace V) (hm : m ∈ (ω : V))
    (h : x ‘ m = succ ∅ ↔ y ‘ m = succ ∅) : x ‘ m = y ‘ m := by
  have h1 := (mem_two_iff _).mp (function_value_mem ((mem_cantorSpace_iff x).mp hx) hm)
  have h2 := (mem_two_iff _).mp (function_value_mem ((mem_cantorSpace_iff y).mp hy) hm)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · rw [h1, h2]
  · exact (succ_empty_ne_empty' ((h.mpr h2).symm.trans h1)).elim
  · exact (succ_empty_ne_empty' ((h.mp h1).symm.trans h2)).elim
  · rw [h1, h2]

section

variable (Pf : SetTheorySemisentence 2) (p : V)

theorem isHOD_kpair {x y : V} (hx : IsHOD Pf x p) (hy : IsHOD Pf y p) : IsHOD Pf ⟨x, y⟩ₖ p := by
  have hp0 : IsParameterTree Pf ∅ p := isParameterTree_of_allowed Pf (isAllowed_empty Pf p)
  have hsx : IsHOD Pf ({x} : V) p := by
    refine isHOD_of_od Pf ?_ (fun w hw ↦ by rw [mem_singleton_iff.mp hw]; exact hx)
    refine isOD_of_two Pf pairFormula (IsHOD.od Pf hx) (IsHOD.od Pf hx) hp0 ?_
    intro w
    rw [eval_pairFormula, mem_singleton_iff, or_self]
  have hpx : IsHOD Pf ({x, y} : V) p := by
    refine isHOD_of_od Pf ?_ (fun w hw ↦ ?_)
    · refine isOD_of_two Pf pairFormula (IsHOD.od Pf hx) (IsHOD.od Pf hy) hp0 ?_
      intro w
      rw [eval_pairFormula, mem_insert, mem_singleton_iff]
    · rcases mem_insert.mp hw with rfl | hw
      · exact hx
      · rw [mem_singleton_iff.mp hw]
        exact hy
  refine isHOD_of_od Pf ?_ (fun w hw ↦ ?_)
  · refine isOD_of_two Pf pairFormula (IsHOD.od Pf hsx) (IsHOD.od Pf hpx) hp0 ?_
    intro w
    rw [eval_pairFormula]
    show w ∈ ({{x}, {x, y}} : V) ↔ _
    rw [mem_insert, mem_singleton_iff]
  · change w ∈ ({{x}, {x, y}} : V) at hw
    rcases mem_insert.mp hw with rfl | hw
    · exact hsx
    · rw [mem_singleton_iff.mp hw]
      exact hpx

theorem isHOD_natural {n : V} (hn : n ∈ (ω : V)) : IsHOD Pf n p :=
  have : IsOrdinal n := IsOrdinal.of_mem hn
  isHOD_of_ordinal Pf n p

theorem two_mem_omega : ((2 : ℕ) : V) ∈ (ω : V) := ω_succ_closed (ω_succ_closed empty_mem_ω)

theorem isHOD_natural_pair {n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ ((2 : ℕ) : V)) :
    IsHOD Pf ⟨n, i⟩ₖ p :=
  isHOD_kpair Pf p (isHOD_natural Pf p hn)
    (isHOD_natural Pf p (IsTransitive.ω.mem_trans hi two_mem_omega))

variable (hreal : ∀ x ∈ cantorSpace V, IsAllowed Pf x p)

include hreal in
theorem isHOD_of_real {x : V} (hx : x ∈ cantorSpace V) : IsHOD Pf x p := by
  refine isHOD_of_od Pf (isOD_of_allowed Pf (hreal x hx)) (fun q hq ↦ ?_)
  obtain ⟨n, hn, i, hi, rfl⟩ :=
    mem_prod_iff.mp ((mem_function_iff.mp ((mem_cantorSpace_iff x).mp hx)).1 q hq)
  exact isHOD_natural_pair Pf p hn hi

variable (c e : V) (hc : c ∈ (ω : V) ^ binarySequences V) (hcinj : Injective c)
  (hcall : IsAllowed Pf c p)
  (he : e ∈ (ω : V) ^ ((ω : V) ×ˢ (ω : V))) (heinj : Injective e) (heall : IsAllowed Pf e p)

theorem isHOD_of_natural_function {s n : V} (hn : n ∈ (ω : V)) (hs : s ∈ ((2 : ℕ) : V) ^ n)
    (hod : IsOD Pf s p) : IsHOD Pf s p := by
  refine isHOD_of_od Pf hod (fun q hq ↦ ?_)
  obtain ⟨i, hi, b, hb, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hs).1 q hq)
  exact isHOD_natural_pair Pf p (IsTransitive.ω.mem_trans hi hn) hb

include hc hcinj hcall in
theorem isHOD_of_mem_binarySequences {s : V} (hs : s ∈ binarySequences V) : IsHOD Pf s p := by
  obtain ⟨n, hn, hsn⟩ := (mem_binarySequences_iff s).mp hs
  refine isHOD_of_natural_function Pf p hn hsn ?_
  have hk : IsAllowed Pf (c ‘ s) p := Or.inl (IsOrdinal.of_mem (function_value_mem hc hs))
  refine isOD_of_two Pf seqCodeFormula (isOD_of_allowed Pf hcall) (isOD_of_allowed Pf hk)
    (isParameterTree_of_allowed Pf (isAllowed_empty Pf p)) ?_
  intro y
  rw [eval_seqCodeFormula]
  constructor
  · intro hy
    exact ⟨s, hs, rfl, hy⟩
  · rintro ⟨s', hs', heq, hy⟩
    rw [injective_value_eq hc hcinj hs' hs heq] at hy
    exact hy

include hc in
theorem image_subset_omega {T : V} (hT : T ⊆ binarySequences V) : image c T ⊆ (ω : V) := by
  intro k hk
  obtain ⟨s, hs, hsk⟩ := (mem_image_iff' _ _ _).mp hk
  have : IsFunction c := IsFunction.of_mem hc
  rw [← value_eq_of_kpair_mem hsk]
  exact function_value_mem hc (hT s hs)

include hc hcinj hcall hreal in
theorem isHOD_of_subset_binarySequences {T : V} (hT : T ⊆ binarySequences V) : IsHOD Pf T p := by
  refine isHOD_of_od Pf ?_ (fun s hs ↦ isHOD_of_mem_binarySequences Pf p c hc hcinj hcall (hT s hs))
  have : IsFunction c := IsFunction.of_mem hc
  have hS : image c T ⊆ (ω : V) := image_subset_omega c hc hT
  have hr : IsAllowed Pf (charFun (image c T)) p := hreal _ (charFun_mem_cantorSpace hS)
  refine isOD_of_two Pf subsetCodeFormula (isOD_of_allowed Pf hcall) (isOD_of_allowed Pf hr)
    (isParameterTree_of_allowed Pf (isAllowed_empty Pf p)) ?_
  intro s
  rw [eval_subsetCodeFormula]
  constructor
  · intro hsT
    refine ⟨hT s hsT, ?_⟩
    rw [charFun_value hS (function_value_mem hc (hT s hsT))]
    exact (mem_image_iff' _ _ _).mpr ⟨s, hsT, kpair_value_mem (by rw [domain_eq_of_mem_function hc]; exact hT s hsT)⟩
  · rintro ⟨hsB, hval⟩
    rw [charFun_value hS (function_value_mem hc hsB)] at hval
    obtain ⟨s', hs', hs'k⟩ := (mem_image_iff' _ _ _).mp hval
    have heq : c ‘ s' = c ‘ s := value_eq_of_kpair_mem hs'k
    rw [injective_value_eq hc hcinj (hT s' hs') hsB heq] at hs'
    exact hs'

def FunCodePred (c e f k : V) : Prop := ∃ n ∈ (ω : V), k = e ‘ ⟨n, c ‘ (f ‘ n)⟩ₖ

instance funCodePred_definable (c e f : V) : ℒₛₑₜ-predicate (FunCodePred c e f) := by
  unfold FunCodePred
  definability

include hc hcinj hcall he heinj heall hreal in
theorem isHOD_of_mem_function_binarySequences {f : V} (hf : f ∈ binarySequences V ^ (ω : V)) :
    IsHOD Pf f p := by
  have hff : IsFunction f := IsFunction.of_mem hf
  have hfd : domain f = (ω : V) := domain_eq_of_mem_function hf
  have hef : IsFunction e := IsFunction.of_mem he
  let S : V := sep (ω : V) (FunCodePred c e f) (funCodePred_definable c e f)
  have hS : S ⊆ (ω : V) := sep_subset
  have hcode : ∀ n ∈ (ω : V), ∀ s ∈ binarySequences V, e ‘ ⟨n, c ‘ s⟩ₖ ∈ (ω : V) := fun n hn s hs ↦
    function_value_mem he (kpair_mem_iff.mpr ⟨hn, function_value_mem hc hs⟩)
  have hr : IsAllowed Pf (charFun S) p := hreal _ (charFun_mem_cantorSpace hS)
  refine isHOD_of_od Pf ?_ (fun q hq ↦ ?_)
  · refine isOD_of_two Pf funCodeFormula (isOD_of_allowed Pf hr) (isOD_empty Pf p)
      (isParameterTree_kpair Pf (isParameterTree_of_allowed Pf hcall) (isParameterTree_of_allowed Pf heall)) ?_
    intro q
    rw [eval_funCodeFormula, kpair.π₁_kpair, kpair.π₂_kpair]
    constructor
    · intro hq
      obtain ⟨n, hn, s, hs, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hf).1 q hq)
      have hsv : s = f ‘ n := (value_eq_of_kpair_mem hq).symm
      refine ⟨n, hn, s, hs, rfl, ?_⟩
      rw [charFun_value hS (hcode n hn s hs)]
      exact mem_sep_iff.mpr ⟨hcode n hn s hs, n, hn, by rw [hsv]⟩
    · rintro ⟨n, hn, s, hs, rfl, hval⟩
      rw [charFun_value hS (hcode n hn s hs)] at hval
      obtain ⟨-, n', hn', heq⟩ := mem_sep_iff.mp hval
      have hpair : ⟨n, c ‘ s⟩ₖ = ⟨n', c ‘ (f ‘ n')⟩ₖ :=
        injective_value_eq he heinj (kpair_mem_iff.mpr ⟨hn, function_value_mem hc hs⟩)
          (kpair_mem_iff.mpr ⟨hn', function_value_mem hc (function_value_mem hf hn')⟩) heq
      obtain ⟨hnn, hcs⟩ := kpair_inj hpair
      subst hnn
      rw [injective_value_eq hc hcinj hs (function_value_mem hf hn) hcs]
      exact kpair_value_mem (by rw [hfd]; exact hn)
  · obtain ⟨n, hn, s, hs, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hf).1 q hq)
    exact isHOD_kpair Pf p (isHOD_natural Pf p hn) (isHOD_of_mem_binarySequences Pf p c hc hcinj hcall hs)

def PowFunCodePred (c e g k : V) : Prop := ∃ n ∈ (ω : V), ∃ s ∈ g ‘ n, k = e ‘ ⟨n, c ‘ s⟩ₖ

instance powFunCodePred_definable (c e g : V) : ℒₛₑₜ-predicate (PowFunCodePred c e g) := by
  unfold PowFunCodePred
  definability

include hc hcinj hcall he heinj heall hreal in
theorem isHOD_of_mem_function_power_binarySequences {g : V}
    (hg : g ∈ (℘ (binarySequences V)) ^ (ω : V)) : IsHOD Pf g p := by
  have hgf : IsFunction g := IsFunction.of_mem hg
  have hgd : domain g = (ω : V) := domain_eq_of_mem_function hg
  have hgsub : ∀ n ∈ (ω : V), g ‘ n ⊆ binarySequences V := fun n hn ↦
    mem_power_iff.mp (function_value_mem hg hn)
  let S : V := sep (ω : V) (PowFunCodePred c e g) (powFunCodePred_definable c e g)
  have hS : S ⊆ (ω : V) := sep_subset
  have hcode : ∀ n ∈ (ω : V), ∀ s ∈ binarySequences V, e ‘ ⟨n, c ‘ s⟩ₖ ∈ (ω : V) := fun n hn s hs ↦
    function_value_mem he (kpair_mem_iff.mpr ⟨hn, function_value_mem hc hs⟩)
  have hr : IsAllowed Pf (charFun S) p := hreal _ (charFun_mem_cantorSpace hS)
  have hmem : ∀ n ∈ (ω : V), ∀ s ∈ binarySequences V,
      (s ∈ g ‘ n ↔ (charFun S) ‘ (e ‘ ⟨n, c ‘ s⟩ₖ) = succ ∅) := by
    intro n hn s hs
    rw [charFun_value hS (hcode n hn s hs)]
    constructor
    · intro hsg
      exact mem_sep_iff.mpr ⟨hcode n hn s hs, n, hn, s, hsg, rfl⟩
    · intro hval
      obtain ⟨-, n', hn', s', hs', heq⟩ := mem_sep_iff.mp hval
      have hpair : ⟨n, c ‘ s⟩ₖ = ⟨n', c ‘ s'⟩ₖ :=
        injective_value_eq he heinj (kpair_mem_iff.mpr ⟨hn, function_value_mem hc hs⟩)
          (kpair_mem_iff.mpr ⟨hn', function_value_mem hc (hgsub n' hn' s' hs')⟩) heq
      obtain ⟨hnn, hcs⟩ := kpair_inj hpair
      subst hnn
      rw [injective_value_eq hc hcinj hs (hgsub n hn s' hs') hcs]
      exact hs'
  refine isHOD_of_od Pf ?_ (fun q hq ↦ ?_)
  · refine isOD_of_two Pf powFunCodeFormula (isOD_of_allowed Pf hr) (isOD_empty Pf p)
      (isParameterTree_kpair Pf (isParameterTree_of_allowed Pf hcall) (isParameterTree_of_allowed Pf heall)) ?_
    intro q
    rw [eval_powFunCodeFormula, kpair.π₁_kpair, kpair.π₂_kpair]
    constructor
    · intro hq
      obtain ⟨n, hn, T, hT, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hg).1 q hq)
      have hTv : T = g ‘ n := (value_eq_of_kpair_mem hq).symm
      refine ⟨n, hn, T, hT, rfl, fun s hs ↦ ?_⟩
      rw [hTv]
      exact hmem n hn s hs
    · rintro ⟨n, hn, T, hT, rfl, hTs⟩
      have hTv : T = g ‘ n := by
        apply mem_ext
        intro s
        constructor
        · intro hsT
          have hsB := mem_power_iff.mp hT s hsT
          exact (hmem n hn s hsB).mpr ((hTs s hsB).mp hsT)
        · intro hsg
          have hsB := hgsub n hn s hsg
          exact (hTs s hsB).mpr ((hmem n hn s hsB).mp hsg)
      rw [hTv]
      exact kpair_value_mem (by rw [hgd]; exact hn)
  · obtain ⟨n, hn, T, hT, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hg).1 q hq)
    exact isHOD_kpair Pf p (isHOD_natural Pf p hn)
      (isHOD_of_subset_binarySequences Pf p hreal c hc hcinj hcall (mem_power_iff.mp hT))

def RealSeqCodePred (e E k : V) : Prop := ∃ n ∈ (ω : V), ∃ m ∈ (ω : V), k = e ‘ ⟨n, m⟩ₖ ∧ (E ‘ n) ‘ m = succ ∅

instance realSeqCodePred_definable (e E : V) : ℒₛₑₜ-predicate (RealSeqCodePred e E) := by
  unfold RealSeqCodePred
  definability

include he heinj heall hreal in
theorem isHOD_of_mem_function_cantorSpace {E : V} (hE : E ∈ (cantorSpace V) ^ (ω : V)) :
    IsHOD Pf E p := by
  have hEf : IsFunction E := IsFunction.of_mem hE
  have hEd : domain E = (ω : V) := domain_eq_of_mem_function hE
  let S : V := sep (ω : V) (RealSeqCodePred e E) (realSeqCodePred_definable e E)
  have hS : S ⊆ (ω : V) := sep_subset
  have hcode : ∀ n ∈ (ω : V), ∀ m ∈ (ω : V), e ‘ ⟨n, m⟩ₖ ∈ (ω : V) := fun n hn m hm ↦
    function_value_mem he (kpair_mem_iff.mpr ⟨hn, hm⟩)
  have hr : IsAllowed Pf (charFun S) p := hreal _ (charFun_mem_cantorSpace hS)
  have hmem : ∀ n ∈ (ω : V), ∀ m ∈ (ω : V),
      ((E ‘ n) ‘ m = succ ∅ ↔ (charFun S) ‘ (e ‘ ⟨n, m⟩ₖ) = succ ∅) := by
    intro n hn m hm
    rw [charFun_value hS (hcode n hn m hm)]
    constructor
    · intro hv
      exact mem_sep_iff.mpr ⟨hcode n hn m hm, n, hn, m, hm, rfl, hv⟩
    · intro hval
      obtain ⟨-, n', hn', m', hm', heq, hv⟩ := mem_sep_iff.mp hval
      have hpair : ⟨n, m⟩ₖ = ⟨n', m'⟩ₖ :=
        injective_value_eq he heinj (kpair_mem_iff.mpr ⟨hn, hm⟩) (kpair_mem_iff.mpr ⟨hn', hm'⟩) heq
      obtain ⟨hnn, hmm⟩ := kpair_inj hpair
      subst hnn
      subst hmm
      exact hv
  refine isHOD_of_od Pf ?_ (fun q hq ↦ ?_)
  · refine isOD_of_two Pf realSeqCodeFormula (isOD_of_allowed Pf hr) (isOD_empty Pf p)
      (isParameterTree_of_allowed Pf heall) ?_
    intro q
    rw [eval_realSeqCodeFormula]
    constructor
    · intro hq
      obtain ⟨n, hn, x, hx, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hE).1 q hq)
      have hxv : x = E ‘ n := (value_eq_of_kpair_mem hq).symm
      refine ⟨n, hn, x, hx, rfl, fun m hm ↦ ?_⟩
      rw [hxv]
      exact hmem n hn m hm
    · rintro ⟨n, hn, x, hx, rfl, hxm⟩
      have hxv : x = E ‘ n := by
        apply cantorSpace_ext hx (function_value_mem hE hn)
        intro m hm
        exact two_value_eq hx (function_value_mem hE hn) hm ((hxm m hm).trans (hmem n hn m hm).symm)
      rw [hxv]
      exact kpair_value_mem (by rw [hEd]; exact hn)
  · obtain ⟨n, hn, x, hx, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hE).1 q hq)
    exact isHOD_kpair Pf p (isHOD_natural Pf p hn) (isHOD_of_real Pf p hreal hx)

end

end ZFVP
