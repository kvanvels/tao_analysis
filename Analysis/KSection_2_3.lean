import Mathlib.Tactic
import Analysis.KSection_2_2
import Analysis.KSection_2_1



namespace KChapter2

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
abbrev KNat.mul (n m : KNat) : KNat := KNat.recurse (fun _ prod ↦ prod + m) 0 n

theorem zero_lt_iff_isPos (a : KNat) : a.IsPos ↔ 0 < a := by sorry

/-- This instance allows for the {kw (of := «term_*_»)}`*` notation to be used for natural number multiplication. -/
instance KNat.instMul : Mul KNat where
  mul := mul

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's {name}`Nat.zero_mul` -/
theorem KNat.zero_mul (m: KNat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod+m) _

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's {name}`Nat.succ_mul` -/
theorem KNat.succ_mul (n m: KNat) : (n♯) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

theorem KNat.one_mul' (m: KNat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]

/-- Compare with Mathlib's {name}`KNat.one_mul` -/
theorem KNat.one_mul (m: KNat) : 1 * m = m := by
  rw [one_mul', zero_add]



/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's {name}`Nat.mul_zero` -/
lemma KNat.mul_zero (n: KNat) : n * 0 = 0 := by
  induction' n with k hk
  have h1 : KNat.zero = 0 := by rfl
  rw [h1,zero_mul]
  rw [succ_mul,hk,add_zero]
  

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's {name}`KNat.mul_succ` -/
lemma KNat.mul_succ (n m:KNat) : n * m♯ = n * m + n := by
  induction' n with k hk
  have h1 : KNat.zero = 0 := by rfl
  rw [h1,zero_mul,zero_mul,add_zero]
  rw [succ_mul,hk,succ_mul,add_assoc,add_succ,add_assoc,add_succ m k,add_comm k m]
  
  
  
  

/-- Lemma 2.3.2 (Multiplication is commutative) / Exercise 2.3.1
Compare with Mathlib's {name}`KNat.mul_comm` -/
lemma KNat.mul_comm (n m: KNat) : n * m = m * n := by
  induction' m with k hk
  rw [zero_eq,mul_zero,zero_mul]
  rw [mul_succ,hk,succ_mul]
  

/-- Compare with Mathlib's {name}`Nat.mul_one` -/
theorem KNat.mul_one (m: KNat) : m * 1 = m := by
  rw [mul_comm, one_mul]

/-- This lemma will be useful to prove Lemma 2.3.3.
Compare with Mathlib's {name}`Nat.mul_pos` -/
lemma KNat.pos_mul_pos {n m: KNat} (h₁: n.IsPos) (h₂: m.IsPos) : (n * m).IsPos := by
  sorry
  

/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) / Exercise 2.3.2.
    Compare with Mathlib's {name}`KNat.mul_eq_zero`.  -/
lemma KNat.mul_eq_zero (n m: KNat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  apply Iff.intro
  intro h0
  rcases n with (_|predn)
  apply Or.inl
  rw [zero_eq]
  apply Or.inr
  rw [succ_mul] at h0
  rcases m with (_|predm)
  rw [zero_eq]
  apply False.elim
  rw [add_succ] at h0
  have h1 := succ_ne (predn * predm♯ + predm)
  exact h1 h0
  rintro (hn|hm)
  rw [hn,zero_mul]
  rw [hm,mul_zero]  

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's {name}`Nat.mul_add` -/
theorem KNat.mul_add (a b c: KNat) : a * (b + c) = a * b + a * c := by
  -- This proof is written to follow the structure of the original text.
  revert c; apply induction
  . rw [add_zero]
    rw [mul_zero, add_zero]
  intro c habc
  rw [add_succ, mul_succ]
  rw [mul_succ, ←add_assoc, ←habc]

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's {name}`KNat.add_mul`  -/
theorem KNat.add_mul (a b c: KNat) : (a + b)*c = a*c + b*c := by
  simp only [mul_comm, mul_add]

/-- Proposition 2.3.5 (Multiplication is associative) / Exercise 2.3.3
Compare with Mathlib's {name}`Nat.mul_assoc` -/
theorem KNat.mul_assoc (a b c: KNat) : (a * b) * c = a * (b * c) := by
  induction' c with k hk
  have h1 : KNat.zero = 0 := by rfl
  rw [h1,mul_zero,mul_zero,mul_zero]
  rw [mul_succ,hk,mul_succ,mul_add]
  

/-- (Not from textbook)  {name}`Nat` is a commutative semiring.
    This allows tactics such as {tactic}`ring` to apply to the Chapter 2 natural numbers. -/
instance KNat.instCommSemiring : CommSemiring KNat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- This illustration of the {tactic}`ring` tactic is not from the
    textbook. -/
example (a b c d:ℕ) : (a+b)*1*(c+d) = d*b+a*c+c*b+a*d+0 := by ring


/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's {name}`Nat.mul_lt_mul_of_pos_right` -/
theorem KNat.mul_lt_mul_of_pos_right {a b c: KNat} (h: a < b) (hc: c.IsPos) : a * c < b * c := by
   rw [zero_lt_iff_isPos c] at hc
   rcases h with ⟨ℓ,rfl⟩
   rcases hc with ⟨predc,rfl⟩
   use (ℓ * predc + predc + ℓ)
   rw [zero_add,add_mul,mul_succ,mul_succ,succ_mul,add_succ]
   

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem KNat.mul_gt_mul_of_pos_right {a b c: KNat} (h: a > b) (hc: c.IsPos) :
    a * c > b * c := mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's {name}`KNat.mul_lt_mul_of_pos_left` -/
theorem KNat.mul_lt_mul_of_pos_left {a b c: KNat} (h: a < b) (hc: c.IsPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem KNat.mul_gt_mul_of_pos_left {a b c: KNat} (h: a > b) (hc: c.IsPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc

/-- Corollary 2.3.7 (Cancellation law)
Compare with Mathlib's {name}`Nat.mul_right_cancel` -/
lemma KNat.mul_cancel_right {a b c: KNat} (h: a * c = b * c) (hc: c.IsPos) : a = b := by
  -- This proof is written to follow the structure of the original text.
  have := trichotomous a b
  obtain hlt | rfl | hgt := this
  . replace hlt := mul_lt_mul_of_pos_right hlt hc
    apply ne_of_lt at hlt
    contradiction
  . rfl
  replace hgt := mul_gt_mul_of_pos_right hgt hc
  apply ne_of_gt at hgt
  contradiction

/-- (Not from textbook) {name}`KNat` is an ordered semiring.
This allows tactics such as {tactic}`gcongr` to apply to the Chapter 2 natural numbers. -/
instance KNat.isOrderedRing : IsOrderedRing KNat where
  zero_le_one := by
    use 1
    rw [zero_add]
    
  mul_le_mul_of_nonneg_left := by
    rintro a _ b c ⟨r,rfl⟩
    use (a * r)
    ring
  mul_le_mul_of_nonneg_right := by
    rintro c _ a b ⟨r,rfl⟩
    use (r * c)
    ring
    

/-- This illustration of the {tactic}`gcongr` tactic is not from the
    textbook. -/
example (a b c d:KNat) (hab: a ≤ b) : c*a*d ≤ c*b*d := by
  gcongr
  . exact d.zero_le
  exact c.zero_le



/-- Proposition 2.3.9 (Euclid's division lemma) / Exercise 2.3.5
Compare with Mathlib's {name}`Nat.mod_eq_iff` -/
theorem KNat.exists_div_mod (n:KNat) {q: KNat} (hq: q.IsPos) :
    ∃ m r: KNat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  induction' n with k hk
  use 0,0
  apply And.intro (by rfl)
  apply And.intro (by rwa [←zero_lt_iff_isPos q])
  rw [zero_eq,zero_mul,add_zero]
  rcases hk with ⟨m,r,hmr0,hmr1,hmr2⟩
  rcases (em (r♯ < q)) with (hr0|hr1)
  use m, r♯
  apply And.intro (zero_le (r♯))
  apply And.intro hr0
  rw [hmr2]
  rw [add_succ]  
  use (m♯), 0
  simp only [Std.le_refl, _root_.add_zero, true_and]
  apply And.intro (by rwa [←zero_lt_iff_isPos q])
  have hrq : r♯ = q := by
    rcases hmr1 with ⟨ℓ,rfl⟩
    rcases ℓ with (_|predℓ)
    rw [zero_eq,add_succ,add_zero]
    clear hmr2
    push_neg at hr1
    rcases hr1 with ⟨θ,hθ ⟩
    rw [add_succ,←succ_add,add_assoc,succ_add predℓ] at hθ 
    have := ne_add_succ (r♯)  (predℓ + θ)
    have := this hθ
    apply False.elim this    
  rw [hmr2,succ_mul,←add_succ,hrq]  

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
abbrev KNat.pow (m n: KNat) : KNat := KNat.recurse (fun _ prod ↦ prod * m) 1 n

instance KNat.instPow : HomogeneousPow KNat where
  pow := KNat.pow

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's {name}`Nat.pow_zero` -/
@[simp]
theorem KNat.pow_zero (m: KNat) : m ^ (0:KNat) = 1 := recurse_zero (fun _ prod ↦ prod * m) _

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
@[simp]
theorem KNat.zero_pow_zero : (0:KNat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's {name}`Nat.pow_succ` -/
theorem KNat.pow_succ (m n: KNat) : (m:KNat) ^ n♯   = m^n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

/-- Compare with Mathlib's {name}`Nat.pow_one` -/
@[simp]
theorem KNat.pow_one (m: KNat) : m ^ (1:KNat) = m := by
  rw [←zero_succ, pow_succ]; simp

/-- Exercise 2.3.4-/
theorem KNat.sq_add_eq (a b: KNat) :
    (a + b) ^ (2 : KNat) = a ^ (2 : KNat) + 2 * a * b + b ^ (2 : KNat) := by
  sorry

end KChapter2
