import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Init.Data.Nat.Basic

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 4.1: The integers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of
  natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of {lean}`ℕ`.

- Equivalence with the Mathlib integers {name}`_root_.Int` (or {lean}`ℤ`), which we will use going forward.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := fun ⟨a0,a1⟩ => rfl      
    symm := by
      rintro ⟨ap,am⟩ ⟨bp,bm⟩ h0
      rw [h0]      
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [eq] at *
    omega)



/-- Definition 4.1.2 (Definition of addition) -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    exact mul_congr (Quotient.eq.mpr h1) (Quotient.eq.mpr h2)
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

--example : ((3:ℕ): Int) = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := Int.natCast_inj n 0

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    intro ⟨ap,am⟩ ⟨bp,bm⟩ h0
    simp only [PreInt.eq] at h0 
    rw [Int.eq,add_comm am,add_comm bm,h0]  
  )

theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
  AddGroup.ofLeftAxioms
    (by --addition is associative
     rintro ⟨ap,am⟩ ⟨bp,bm⟩ ⟨cp,cm⟩
     apply Quot.sound
     simp only [Setoid.r]
     abel_nf
     
    ) (by --zero is an additive identity
      rintro ⟨ap,am⟩
      apply Quot.sound
      simp only [Setoid.r]
      rw [zero_add,zero_add,add_comm]          
    ) (by
       rintro ⟨ap,am⟩
       apply Quot.sound
       simp only [Setoid.r]
       rw [add_zero,zero_add,add_comm] )    


/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by
    rintro ⟨ap,am⟩ ⟨bp,bm⟩
    apply Quot.sound
    simp only [Setoid.r]
    ring    
  

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := by
    rintro ⟨ap,am⟩ ⟨bp,bm⟩
    apply Quot.sound
    simp only [Setoid.r]
    ring
    
  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq];    
    ring_nf    
    

  one_mul := by
    rintro ⟨ap,am⟩
    apply Quot.sound
    simp only [Setoid.r]
    ring
        
  mul_one := by
    rintro ⟨ap,am⟩
    apply Quot.sound
    simp only [Setoid.r]
    ring
    

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := by
    rintro ⟨ap,am⟩ ⟨bp,bm⟩ ⟨cp,cm⟩ 
    apply Quot.sound
    simp only [Setoid.r]
    ring
  right_distrib := by
    rintro ⟨ap,am⟩ ⟨bp,bm⟩ ⟨cp,cm⟩ 
    apply Quot.sound
    simp only [Setoid.r]
    ring
  zero_mul := by
    rintro ⟨ap,am⟩
    apply Quot.sound
    simp only [Setoid.r]
    ring
  mul_zero := by
    rintro ⟨ap,am⟩
    apply Quot.sound
    simp only [Setoid.r]
    ring
    
  

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  apply Quot.sound  
  simp only [Setoid.r]
  ring
  

theorem h0 : (0 : Int) = (0 —— 0) := by sorry


theorem h1 (P Q R : Prop) : P ∨ Q ↔ (¬P → Q) := by
  exact?
  

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by        
  rcases eq_diff a with ⟨ap,am,rfl⟩
  rcases eq_diff b with ⟨bp,bm,rfl⟩
  rw [mul_eq,h0,Int.eq] at h
  rw [add_zero,zero_add] at h
  rw [h0,Int.eq,Int.eq,add_zero,zero_add,add_zero,zero_add]
  rw [or_iff_not_imp_left]
  intro h0
  replace h0 := Nat.lt_or_lt_of_ne h0
  rcases h0 with (h0|h0)
  have h1 : ∃ ℓ : ℕ, ap + ℓ + 1 = am := by sorry
  rcases h1 with ⟨ℓ,rfl⟩
  clear h0
  rw [add_mul,add_mul,add_mul,one_mul,one_mul,add_mul] at h
  have h1 : (ℓ + 1) * bm = (ℓ + 1) * bp := by sorry
  have h2 : (ℓ + 1) ≠ 0 := by sorry
  exact (Nat.mul_right_inj h2).mp (id (Eq.symm h1))
  have h1 : ∃ ℓ : ℕ, am + ℓ + 1 = ap := by sorry
  rcases h1 with ⟨ℓ,rfl⟩
  clear h0
  rw [add_mul,add_mul,add_mul,one_mul,one_mul,add_mul] at h
  have h1 : (ℓ + 1) * bp = (ℓ +1) * bm := by sorry
  have h2 : (ℓ + 1) ≠ 0 := by sorry
  exact (Nat.mul_right_inj h2).mp (id (h1))

  

/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  have h1 : a * c + (-b) *( c) = 0 := by sorry
  have h2 : a * c + (-b) * c = (a + (-b)) * c := Eq.symm (RightDistribClass.right_distrib a (-b) c)
  rw [h2] at h1
  have h3 := Int.mul_eq_zero h1
  rcases h3 with (h3|h3)
  sorry
  exact False.elim (hc h3)
  
  
  

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + Int.ofNat t) ∧ a ≠ b := by rfl

theorem Int.lt_iff' (a b : Int) : a < b ↔ ∃ t : ℕ, b = a + (t + 1) := by sorry

  

  

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) : a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  rw [Int.lt_iff']
  apply Iff.intro
  rintro ⟨t,rfl⟩ 
  use (t + 1)
  apply And.intro
  exact Ne.symm (Nat.zero_ne_add_one t)
  rfl
  rintro ⟨n,hn,rfl⟩
  rcases n with (_|predn)
  apply False.elim
  apply hn
  rfl
  use predn
  rfl
  

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  rw [Int.lt_iff'] at ⊢ h
  rcases h with ⟨θ ,rfl⟩
  use θ; abel


/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  rw [Int.lt_iff'] at ⊢ hab hc
  rcases hab with ⟨ℓ,rfl⟩
  rcases hc with ⟨predc,rfl⟩
  rw [zero_add]
  use (ℓ * predc + ℓ + predc)
  grind  
    

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  rw [Int.lt_iff'] at *
  rcases h with ⟨θ,rfl⟩
  use θ
  grind

  

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by sorry

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by sorry

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by sorry

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b):= by sorry

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by sorry

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by sorry

/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue  
        sorry
      | isFalse h =>
        apply isFalse
        sorry
  
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by sorry

/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_ge := sorry
  le_antisymm := sorry
  le_total := sorry
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by sorry

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by
  let P : Int → Prop := fun z ↦ (∃ t : ℕ, z = t)
  use P
  apply And.intro
  apply And.intro
  unfold P
  use 0
  simp only [Nat.cast_zero]
  rintro z ⟨t,rfl⟩
  use (t + 1)
  simp only [Nat.cast_add, Nat.cast_one]
  push Not
  use (-(1:ℕ))
  unfold P
  push Not
  intro θ h0
  rw [natCast_eq,neg_eq,natCast_eq,Int.eq] at h0
  rw [add_zero] at h0
  have h1 := Nat.zero_ne_add_one θ
  exact h1 h0  

/-- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
lemma Int.sq_nonneg_of_nonneg (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by  
  rcases Int.eq_diff n with ⟨np,nm,rfl⟩
  rw [mul_eq]
  rw [h0] at ⊢ h
  rw [le_iff] at ⊢ h
  rcases h with ⟨ℓ,hℓ⟩
  use ℓ*ℓ
  rw [natCast_eq,Int.add_eq,add_zero,zero_add] at hℓ ⊢
  rw [Int.eq,add_zero] at ⊢ hℓ
  rw [hℓ]
  ring

lemma Int.sq_nonneg_of_nonpos (n:Int) (h: n ≤ 0) : 0 ≤ n*n := by
  rcases Int.eq_diff n with ⟨np,nm,rfl⟩
  rw [mul_eq]
  rw [h0] at ⊢ h
  rw [le_iff] at ⊢ h
  rcases h with ⟨ℓ,hℓ⟩
  rw [natCast_eq,add_eq,Int.eq,zero_add,add_zero,add_zero] at hℓ
  use (ℓ * ℓ)
  rw [natCast_eq,add_eq,Int.eq,add_zero,add_zero,zero_add,hℓ,mul_add,add_mul,mul_add,add_mul]
  ring_nf

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by
  rcases (em (0 ≤ n)) with (hnonneg|hneg)
  apply Int.sq_nonneg_of_nonneg
  exact hnonneg
  have h1 : n ≤ 0 := by sorry
  apply Int.sq_nonneg_of_nonpos
  exact h1


    
  
  

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by
  have h1 := Int.sq_nonneg n
  rw [le_iff] at h1
  rcases h1 with ⟨m,h1⟩
  use m
  rwa [zero_add] at h1  

/--
  Not in textbook: create an equivalence between {name}`Int` and {lean}`ℤ`.
  This requires some familiarity with the API for Mathlib's version of the integers.
-/
abbrev Int.equivInt : Int ≃ ℤ := by sorry


  /- toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ (a: ℤ) - (b:ℤ)) (by
   -  rintro ⟨ap,am⟩ ⟨bp,bm⟩ h0
   -  dsimp
   -  simp only [PreInt.eq] at h0
   -  
   -  rcases ap with (_|predap)
   -  rw [zero_add] at h0
   -  dsimp
   -  rw [sub_eq_add_neg,zero_add]
   -  rw [h0]
   -  rcases am with (_|predam)
   -  rw [add_zero] at h0
   -  rw [add_zero]
   -  rw [sub_self]
   -  decide
   -  rcases bp with (_|predbp)
   -  rw [zero_add]   
   -  sorry)
   - invFun := sorry
   - left_inv n := sorry
   - right_inv n := sorry -/

/-- Not in textbook: equivalence preserves order and ring operations -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' := by sorry
  map_mul' := by sorry
  map_le_map_iff' := by sorry

end Section_4_1
