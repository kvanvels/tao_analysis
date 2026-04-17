import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Analysis.Section_6_4
/-!
# Analysis I, Section 9.1: Subsets of the real line

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of Mathlib intervals.
- Adherent points, limit points, isolated points.
- Closed sets and closure.
- The Heine-Borel theorem for the real line.

-/

variable (I : Type*)

/- Definition 9.1.1 (Intervals) -/
#check Set.Icc_def
#check Set.Ico_def
#check Set.Ioc_def
#check Set.Ioo_def
#check Set.Ici_def
#check Set.Ioi_def
#check Set.Iic_def
#check Set.Iio_def

#check EReal.image_coe_Icc
#check EReal.image_coe_Ico
#check EReal.image_coe_Ioc
#check EReal.image_coe_Ioo
#check EReal.image_coe_Ici
#check EReal.image_coe_Ioi
#check EReal.image_coe_Iic
#check EReal.image_coe_Iio

/-- Example 9.1.4 -/
example {a b: EReal} (h: a > b) : Set.Icc a b = ∅ := by
  apply Set.subset_empty_iff.1
  intro x ⟨hx0,hx1⟩
  apply False.elim
  have h1 := by calc
   x ≤ b := by sorry
   _ < a := by sorry
   _ ≤ x := by sorry
  have h2 := lt_irrefl x
  exact h2 h1  


example {a b: EReal} (h: a ≥ b) : Set.Ico a b = ∅ := by
  apply Set.subset_empty_iff.1
  intro x ⟨hx0,hx1⟩
  apply False.elim
  apply (lt_irrefl x)
  have h1 := by calc
    x < b := by sorry
    _ ≤ a := by sorry
    _ ≤ x := by sorry
  exact h1
  
  

example {a b: EReal} (h: a ≥ b) : Set.Ioc a b = ∅ := by
  apply Set.subset_empty_iff.1
  intro x ⟨hx0,hx1⟩
  apply lt_irrefl x
  have h1 := by calc
    x ≤ b := hx1
    _ ≤ a := h
    _ < x := hx0
  exact h1

example {a b: EReal} (h: a ≥ b) : Set.Ioo a b = ∅ := by
  apply Set.subset_empty_iff.1
  intro x ⟨hx0,hx1⟩
  apply lt_irrefl x  
  have h1 := by calc
    x < b := hx1
    _ ≤ a := h
    _ < x := hx0
  exact h1

  


example {a b: EReal} (h: a = b) : Set.Icc a b = {a} := by
  apply subset_antisymm
  intro x ⟨hxa,hxb⟩
  simp only [Set.mem_singleton_iff]
  apply le_antisymm _ hxa
  rwa [h]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  apply And.intro
  rw [hx]
  rw [←h,hx]
  

/-- Definition 9.1.5.  Note that a slightly different `Real.adherent` was defined in Chapter 6.4 -/
abbrev Real.adherent' (ε:ℝ) (x:ℝ) (X: Set ℝ) := ∃ y ∈ X, |x - y| ≤ ε

/-- Example 9.1.7 -/
example : (0.5:ℝ).adherent' 1.1 (.Ioo 0 1) := by
  use 0.95
  apply And.intro
  norm_num
  norm_num

example : ¬ (0.1:ℝ).adherent' 1.1 (.Ioo 0 1) := by
  push_neg
  intro y ⟨hy0,hy1⟩
  unfold abs
  rw [lt_max_iff]
  apply Or.inl
  linarith  
  

example : (0.5:ℝ).adherent' 1.1 {1,2,3} := by sorry
  


namespace Chapter9

/-- Definition 9.1.-/
abbrev AdherentPt (x:ℝ) (X:Set ℝ) := ∀ ε > (0:ℝ), ε.adherent' x X

example : AdherentPt 1 (.Ioo 0 1) := by
  intro ε εpos
  rcases (em (ε<1)) with (εsmall|εbig)
  use 1- ε/2
  apply And.intro
  apply And.intro
  linarith
  linarith
  rw [abs_le]
  apply And.intro
  linarith
  linarith
  push_neg at εbig
  use 1/2
  apply And.intro
  apply And.intro
  linarith
  linarith
  linarith  
  


example : ¬ AdherentPt 2 (.Ioo 0 1) := by
  unfold AdherentPt
  push_neg
  use 1/2
  apply And.intro (by norm_num)
  intro y ⟨hy0,hy1⟩
  unfold abs
  apply lt_max_iff.2
  apply Or.inl
  linarith
  
  

/-- Definition 9.1.10 (Closure).  Here we identify this definition with the Mathilb version. -/
theorem closure_def (X:Set ℝ) : closure X = { x | AdherentPt x X } := by
  ext; simp [Real.mem_closure_iff, AdherentPt, Real.adherent']
  constructor <;> intro h ε hε
  all_goals choose y hy hxy using h _ (half_pos hε); exact ⟨ _, hy, by rw [abs_sub_comm]; linarith ⟩

theorem closure_def' (X:Set ℝ) (x :ℝ) : x ∈ closure X ↔ AdherentPt x X := by
  simp [closure_def]

/-- identification of {name}`AdherentPt` with Mathlib's {name}`ClusterPt` -/
theorem AdherentPt_def (x:ℝ) (X:Set ℝ) : AdherentPt x X = ClusterPt x (.principal X) := by
  rw [←closure_def', mem_closure_iff_clusterPt]

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem subset_closure (X:Set ℝ): X ⊆ closure X := by
  intro x hX
  unfold closure
  intro U ⟨hU,hU1⟩
  exact hU1 hX


/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_union (X Y:Set ℝ): closure (X ∪ Y) = closure X ∪ closure Y := by
  apply subset_antisymm
  rw [←Set.compl_subset_compl,Set.compl_union]
  
  intro x ⟨(hx0:¬(x ∈  closure X)),(hx1: ¬(x ∈ closure Y)) ⟩
  show (¬ (x ∈ closure (X ∪ Y)))
  rw [closure_def'] at hx0 hx1 ⊢
  
  unfold AdherentPt at hx0 hx1 ⊢ 
  push_neg at hx0 hx1 ⊢ 
  rcases hx0 with ⟨ε0,ε0pos,hε0⟩
  rcases hx1 with ⟨ε1,ε1pos,hε1⟩
  use min ε0 ε1
  apply And.intro (by sorry)
  rintro y hy
  rw [min_lt_iff]
  rcases hy with (hy|hy)
  specialize hε0 y hy
  apply Or.inl hε0
  specialize hε1 y hy
  apply Or.inr hε1
  

  intro x hx
  wlog h0 : x ∈ closure X generalizing X Y with H
  rcases hx with (hx|hx)
  apply False.elim
  exact h0 hx
  specialize H Y X (Or.inl hx) hx
  rwa [Set.union_comm]
  rw [closure_def'] at ⊢ h0
  intro ε εpos
  clear hx
  specialize h0 ε εpos
  rcases h0 with ⟨θ,hθ0,hθ1⟩
  use θ 
  apply And.intro
  apply Or.inl hθ0
  exact hθ1
  
  
   
  
  
theorem closure_inter_helper (X Y : Set ℝ) : closure (X ∩ Y) ⊆ closure X := by
  intro x h0
  rw [closure_def'] at ⊢ h0
  intro ε εpos
  specialize h0 ε εpos
  rcases h0 with ⟨θ,hθ0,hθ1⟩
  use θ
  apply And.intro hθ0.1 hθ1
  
  

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_inter (X Y:Set ℝ): closure (X ∩ Y) ⊆ closure X ∩ closure Y := by
  rw [Set.subset_inter_iff]
  apply And.intro (closure_inter_helper X Y) 
  rw [Set.inter_comm]
  apply closure_inter_helper Y X
  

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_subset {X Y:Set ℝ} (h: X ⊆ Y): closure X ⊆ closure Y := by
  intro x hx
  rw [closure_def'] at ⊢ hx
  intro ε εpos
  specialize hx ε εpos
  rcases hx with ⟨θ,hθ⟩
  use θ
  apply And.intro (h hθ.1) hθ.2

theorem closure_is_closed (X : Set ℝ) : IsClosed (closure X) := by sorry

theorem isClosed_TFAE (U : Set ℝ): List.TFAE [IsClosed U, closure U ⊆ U, closure U = U] := by
  tfae_have 1 → 2 := by
    intro h0 x hx
    specialize hx U
    apply hx
    apply And.intro h0 (subset_refl U)
  tfae_have 2 → 3 := by
    intro h0
    apply le_antisymm h0 (subset_closure U)
  tfae_have 3 → 1 := by
    intro h0
    rw [←h0]
    apply isClosed_closure
  tfae_finish

theorem closure_closure (U : Set ℝ) : closure (closure U) = closure U := by
  have h1 := (isClosed_TFAE (closure U)).out 2 0
  rw [h1]
  apply isClosed_closure
  
  
  

/-- Exercise 9.1.6 -/
theorem closure_of_subset_closure {X Y:Set ℝ} (h: X ⊆ Y) (h' : Y ⊆ closure X): closure Y = closure X := by
   apply subset_antisymm
   have h0 := closure_subset h'
   rwa [closure_closure] at h0
   exact closure_subset h
   

/-- Lemma 9.1.12 -/
theorem closure_of_Ioo {a b:ℝ} (h:a < b) : closure (.Ioo a b) = .Icc a b := by
  -- This proof is written to follow the structure of the original text.
  ext x; simp [closure_def, AdherentPt, Real.adherent']
  constructor
  . intro h; contrapose! h
    obtain h' | h' := le_or_gt a x
    . specialize h h'
      use x-b, by linarith
      intro y ⟨ _, _ ⟩; observe : x-y ≤ |x-y|; linarith
    use a-x, by linarith
    intro y ⟨ _, _ ⟩; observe : -(x-y) ≤ |x-y|; linarith
  intro ⟨ h1, h2 ⟩
  by_cases ha : x = a
  . sorry  
  by_cases hb : x = b
  . sorry
  intro ε _; use x, (by exact ⟨lt_of_le_of_ne h1 (Ne.symm ha), lt_of_le_of_ne h2 hb⟩); simp; order

theorem closure_of_Ioc {a b:ℝ} (h:a < b) : closure (.Ioc a b) = .Icc a b := by
  sorry

theorem closure_of_Ico {a b:ℝ} (h:a < b) : closure (.Ico a b) = .Icc a b := by
  sorry

theorem closure_of_Icc {a b:ℝ} (h:a ≤ b) : closure (.Icc a b) = .Icc a b := by
  sorry

theorem closure_of_Ioi {a:ℝ} : closure (.Ioi a) = .Ici a := by
  sorry

theorem closure_of_Ici {a:ℝ} : closure (.Ici a) = .Ici a := by
  sorry

theorem closure_of_Iio {a:ℝ} : closure (.Iio a) = .Iic a := by
  sorry

theorem closure_of_Iic {a:ℝ} : closure (.Iic a) = .Iic a := by
  sorry

theorem closure_of_R : closure (.univ: Set ℝ) = .univ := by sorry

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_N :
  closure ((fun n:ℕ ↦ (n:ℝ)) '' .univ) = ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by
    sorry

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_Z :
  closure ((fun n:ℤ ↦ (n:ℝ)) '' .univ) = ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by
    sorry

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_Q :
  closure ((fun n:ℚ ↦ (n:ℝ)) '' .univ) = .univ := by
    sorry

/-- Lemma 9.1.14 / Exercise 9.1.4-/
theorem limit_of_AdherentPt (X: Set ℝ) (x:ℝ) :
  AdherentPt x X ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ X) ∧ Filter.atTop.Tendsto a (nhds x) := by
    sorry

theorem AdherentPt.of_mem {X: Set ℝ} {x: ℝ} (h: x ∈ X) : AdherentPt x X := by
  rw [limit_of_AdherentPt]; use fun _ ↦ x; simp [h]

/-- Definition 9.1.15.  Here we use the Mathlib definition. -/
theorem isClosed_def (X:Set ℝ): IsClosed X ↔ closure X = X :=
  closure_eq_iff_isClosed.symm

theorem isClosed_def' (X:Set ℝ): IsClosed X ↔ ∀ x, AdherentPt x X → x ∈ X := by
  simp [isClosed_def, subset_antisymm_iff, subset_closure]; simp [closure_def]; rfl

/-- Examples 9.1.16 -/
theorem Icc_closed {a b:ℝ} : IsClosed (.Icc a b) := by sorry

/-- Examples 9.1.16 -/
theorem Ici_closed (a:ℝ) : IsClosed (.Ici a) := by sorry

/-- Examples 9.1.16 -/
theorem Iic_closed (a:ℝ) : IsClosed (.Iic a) := by sorry

/-- Examples 9.1.16 -/
theorem R_closed : IsClosed (.univ : Set ℝ) := by sorry

/-- Examples 9.1.16 -/
theorem Ico_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (.Ico a b) := by sorry

/-- Examples 9.1.16 -/
theorem Ioc_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (.Ioc a b) := by sorry

/-- Examples 9.1.16 -/
theorem Ioo_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (.Ioo a b) := by sorry

/-- Examples 9.1.16 -/
theorem Ioi_not_closed (a:ℝ) : ¬ IsClosed (.Ioi a) := by sorry

/-- Examples 9.1.16 -/
theorem Iio_not_closed (a:ℝ) : ¬ IsClosed (.Iio a) := by sorry

/-- Examples 9.1.16 -/
theorem N_closed : IsClosed ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by sorry

/-- Examples 9.1.16 -/
theorem Z_closed : IsClosed ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by sorry

/-- Examples 9.1.16 -/
theorem Q_not_closed : ¬ IsClosed ((fun n:ℚ ↦ (n:ℝ)) '' .univ) := by sorry

/-- Corollary 9.1.17 -/
theorem isClosed_iff_limits_mem (X: Set ℝ) :
  IsClosed X ↔ ∀ (a:ℕ → ℝ) (L:ℝ), (∀ n, a n ∈ X) → Filter.atTop.Tendsto a (nhds L) → L ∈ X := by
  rw [isClosed_def']
  constructor
  . intro h _ L _ _; apply h L; rw [limit_of_AdherentPt]; solve_by_elim
  intro _ _ hx; rw [limit_of_AdherentPt] at hx; grind

/-- Definition 9.1.18 (Limit points) -/
abbrev LimitPt (x:ℝ) (X: Set ℝ) := AdherentPt x (X \ {x})

/-- Identification with Mathlib's {name}`AccPt`-/
theorem LimitPt.iff_AccPt (x:ℝ) (X: Set ℝ) : LimitPt x X ↔ AccPt x (.principal X) := by
  rw [accPt_principal_iff_clusterPt,←AdherentPt_def]

/-- Definition 9.1.18 (Isolated points) -/
abbrev IsolatedPt (x:ℝ) (X: Set ℝ) := x ∈ X ∧ ∃ ε>0, ∀ y ∈ X \ {x}, |x-y| > ε

/-- Example 9.1.19 -/
example : AdherentPt 3 ((.Ioo 1 2) ∪ {3}) := by sorry

example : ¬ LimitPt 3 ((.Ioo 1 2) ∪ {3}) := by sorry

example : IsolatedPt 3 ((.Ioo 1 2) ∪ {3}) := by sorry

/-- Remark 9.1.20 -/
theorem LimitPt.iff_limit (x:ℝ) (X: Set ℝ) :
  LimitPt x X ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ X \ {x}) ∧ Filter.atTop.Tendsto a (nhds x) := by
  simp [limit_of_AdherentPt]

/-- Lemma 9.1.21 -/
theorem mem_Icc_isLimit {a b x:ℝ} (h: a < b) (hx: x ∈ Set.Icc a b) : LimitPt x (.Icc a b) := by
  -- This proof is written to follow the structure of the original text, with some slight simplifications.
  simp at hx
  rw [LimitPt.iff_limit]
  obtain hxb | hxb := le_iff_lt_or_eq.1 hx.2
  . use (fun n:ℕ ↦ (x + 1/(n+(b-x)⁻¹)))
    constructor
    . intro n; simp
      have : b - x > 0 := by linarith
      have : (b - x)⁻¹ > 0 := by positivity
      have : n + (b - x)⁻¹ > 0 := by linarith
      have : (n+(b - x)⁻¹)⁻¹ > 0 := by positivity
      have : (b-x)⁻¹ ≤ n + (b - x)⁻¹ := by linarith
      have : (n + (b - x)⁻¹)⁻¹ ≤ b-x := by rwa [inv_le_comm₀ ?_ ?_] <;> positivity
      grind
    convert (Filter.Tendsto.const_add x (a := 0) ?_) using 1; · simp
    convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/(k+(b-x)⁻¹)) ?_ tendsto_natCast_atTop_atTop
    convert tendsto_mul_add_inv_atTop_nhds_zero 1 (b - x)⁻¹ (by norm_num) using 2 with n; simp
  sorry

theorem mem_Ico_isLimit {a b x:ℝ} (hx: x ∈ Set.Ico a b) : LimitPt x (.Ico a b) := by
  sorry

theorem mem_Ioc_isLimit {a b x:ℝ} (hx: x ∈ Set.Ioc a b) : LimitPt x (.Ioc a b) := by
  sorry

theorem mem_Ioo_isLimit {a b x:ℝ} (hx: x ∈ Set.Ioo a b) : LimitPt x (.Ioo a b) := by
  sorry

theorem mem_Ici_isLimit {a x:ℝ} (hx: x ∈ Set.Ici a) : LimitPt x (.Ici a) := by
  sorry

theorem mem_Ioi_isLimit {a x:ℝ} (hx: x ∈ Set.Ioi a) : LimitPt x (.Ioi a) := by
  sorry

theorem mem_Iic_isLimit {a x:ℝ} (hx: x ∈ Set.Iic a) : LimitPt x (.Iic a) := by
  sorry

theorem mem_Iio_isLimit {a x:ℝ} (hx: x ∈ Set.Iio a) : LimitPt x (.Iio a) := by
  sorry

theorem mem_R_isLimit {x:ℝ} : LimitPt x (.univ) := by
  sorry

/-- Definition 9.1.22.  We use here Mathlib's {name}`Bornology.IsBounded`-/

theorem isBounded_def (X: Set ℝ) : Bornology.IsBounded X ↔ ∃ M > 0, X ⊆ .Icc (-M) M := by
  simp [isBounded_iff_forall_norm_le]
  constructor
  . intro ⟨ C, hC ⟩; use (max C 1)
    refine ⟨ lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_ ⟩
    peel hC with x hx hC; rw [abs_le'] at hC; simp [hC.1]; linarith [le_max_left C 1]
  intro ⟨ M, hM, hXM ⟩; use M; intro x hx; specialize hXM hx; simp_all [abs_le']; linarith [hXM.1]

/-- Example 9.1.23 -/
theorem Icc_bounded (a b:ℝ) : Bornology.IsBounded (.Icc a b) := by
  rw [isBounded_def]
  use (max (|a|+1) (|b|+1) )  
  apply And.intro
  sorry
  rcases em (|b| ≥ |a|) with (hbbig|habig)
  
  
  intro x ⟨hx0,hx1⟩
  apply And.intro
  sorry
  sorry
  sorry
  


  
  
    
  
  
  
  
  
  

/-- Example 9.1.23 -/
theorem Ici_unbounded (a: ℝ) : ¬ Bornology.IsBounded (.Ici a) := by sorry

/-- Example 9.1.23 -/
theorem N_unbounded : ¬ Bornology.IsBounded ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by sorry

/-- Example 9.1.23 -/
theorem Z_unbounded : ¬ Bornology.IsBounded ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by sorry

/-- Example 9.1.23 -/
theorem Q_unbounded : ¬ Bornology.IsBounded ((fun n:ℚ ↦ (n:ℝ)) '' .univ) := by sorry

/-- Example 9.1.23 -/
theorem R_unbounded : ¬ Bornology.IsBounded (.univ: Set ℝ) := by sorry

/-- Theorem 9.1.24 / Exercise 9.1.13 (Heine-Borel theorem for the line)-/
theorem Heine_Borel (X: Set ℝ) :
  IsClosed X ∧ Bornology.IsBounded X ↔ ∀ a : ℕ → ℝ, (∀ n, a n ∈ X) →
  (∃ n : ℕ → ℕ, StrictMono n
    ∧ ∃ L ∈ X, Filter.atTop.Tendsto (fun j ↦ a (n j)) (nhds L)) := by  
  sorry

/-- Exercise 9.1.3 -/
example : ∃ (X Y:Set ℝ), closure (X ∩ Y) ≠ closure X ∩ closure Y := by
  let X :Set ℝ := .Ioo (-1) 0
  let Y : Set ℝ := .Ioo (0) 1
  use X, Y
  intro h0    
  replace h0 := subset_antisymm_iff.mp h0
  rcases h0 with ⟨h0,h1⟩
  clear h0
  have h0X : 0 ∈ closure X := by sorry
  have h0Y : 0 ∈ closure Y := by sorry
  have h0XY :0 ∈ closure X ∩ closure Y := ⟨h0X,h0Y⟩
  specialize h1 h0XY
  have hXintY : X ∩ Y = ∅ := by sorry
  rw [hXintY] at h1
  rw [closure_empty] at h1
  exact h1
    
  
  
/-- Exercise 9.1.5 -/
example (X:Set ℝ) : IsClosed (closure X) := by
  apply isClosed_sInter
  rintro θ ⟨hθ0,hθ1⟩
  exact hθ0

/-- Exercise 9.1.6 -/
example {X Y:Set ℝ} (hY: IsClosed Y) (hXY: X ⊆ Y) : closure X ⊆ Y := by
  rintro x hx
  specialize hx Y
  apply hx
  apply And.intro hY hXY

/-- Exercise 9.1.7 -/
example {n:ℕ} (X: Fin n → Set ℝ) (hX: ∀ i, IsClosed (X i)) :
  IsClosed (⋃ i, X i) := by
  induction' n with k hk
  rw [Set.iUnion_of_empty]
  exact isClosed_empty
  sorry
  
/-- Exercise 9.1.8 -/
example {I:Type} (X: I → Set ℝ) (hX: ∀ i, IsClosed (X i)) :
  IsClosed (⋂ i, X i) := by
  rw [←isOpen_compl_iff]
  rw [Set.compl_iInter]
  apply isOpen_iUnion
  intro ι
  specialize hX ι
  rwa [isOpen_compl_iff]

/-- Exercise 9.1.9 -/
example {X:Set ℝ} {x:ℝ} (hx: AdherentPt x X) : LimitPt x X ∨ IsolatedPt x X := by
  sorry

/-- Exercise 9.1.9 -/
example {X:Set ℝ} {x:ℝ} : ¬ (LimitPt x X ∧ IsolatedPt x X) := by
  sorry

/-- Exercise 9.1.10 -/
example {X:Set ℝ} (hX: X ≠ ∅) : Bornology.IsBounded X ↔
  sSup ((fun x:ℝ ↦ (x:EReal)) '' X) < ⊤ ∧
  sInf ((fun x:ℝ ↦ (x:EReal)) '' X) > ⊥ := by
  sorry

/-- Exercise 9.1.11 -/
example {X:Set ℝ} (hX: Bornology.IsBounded X) : Bornology.IsBounded (closure X) := by
  sorry

/-- Exercise 9.1.12.  As a followup: prove or disprove this exercise with {lean}`[Fintype I]` removed. -/
example {I:Type} [Fintype I] (X: I → Set ℝ) (hX: ∀ i, Bornology.IsBounded (X i)) :
  Bornology.IsBounded (⋃ i, X i) := by
  sorry

/-- Exercise 9.1.14 -/
example (I: Finset ℝ) : IsClosed (I:Set ℝ) ∧ Bornology.IsBounded (I:Set ℝ) := by
  sorry

/-- Exercise 9.1.15 -/
example {E:Set ℝ} (hE: Bornology.IsBounded E) (hnon: E.Nonempty): AdherentPt (sSup E) E ∧ AdherentPt (sSup E) Eᶜ := by
  sorry

end Chapter9
