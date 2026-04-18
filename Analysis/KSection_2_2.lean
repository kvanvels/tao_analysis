import Mathlib.Tactic
import Analysis.KSection_2_1

namespace KChapter2

/-- Definition 2.2.1. (Addition of natural numbers).
    Compare with Mathlib's {name}`Nat.add` -/
abbrev KNat.add (n m : KNat) : KNat := KNat.recurse (fun _ sum ↦ sum♯ ) m n

/-- This instance allows for the {kw (of := «term_+_»)}`+` notation to be used for natural number addition. -/
instance KNat.instAdd : Add KNat where
  add := add

/-- Compare with Mathlib's {name}`Nat.zero_add`. -/
@[simp]
theorem KNat.zero_add (m: KNat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum♯) _

/-- Compare with Mathlib's {name}`Nat.succ_add`. -/
theorem KNat.succ_add (n m: KNat) : n♯ + m = (n+m)♯  := by rfl



/-- Compare with Mathlib's {name}`KNat.one_add`. -/
theorem KNat.one_add (m:KNat) : 1 + m = m♯  := by
  rw [show 1 = 0♯  from rfl, succ_add, zero_add]

private
theorem KNat.two_add (m:KNat) : 2 + m = (m♯ )♯   := by
  rw [show 2 = 1♯  from rfl, succ_add, one_add]

theorem KNat.zero_eq : KNat.zero = 0 := by rfl


/-- Lemma 2.2.2 ({lean}`n + 0 = n`). Compare with Mathlib's {name}`KNat.add_zero`. -/
@[simp]
lemma KNat.add_zero (n:KNat) : n + 0 = n := by
  induction' n with k hk
  rw [zero_eq,zero_add]
  calc
    (k♯ + 0)
       = (k + 0)♯ := by rw [succ_add]
     _ = (k)♯ := by rw [hk]    
  

/-- Lemma 2.2.3 ({lean}`n+(m♯ ) = (n+m)♯`). Compare with Mathlib's {name}`Nat.add_succ`. -/
lemma KNat.add_succ (n m:KNat) : n + m♯ = (n + m)♯  := by
  induction' n with k hk
  rw [zero_eq,zero_add,zero_add]
  calc
    k♯ + m♯
      = (k + m♯)♯ := by rw [succ_add]
    _ = (k+m)♯♯ := by rw [hk]
    _ = (k♯+m)♯ := by rw [←succ_add]



/-- {lean}`n♯  = n + 1` (Why?). Compare with Mathlib's {name}`KNat.succ_eq_add_one` -/
theorem KNat.succ_eq_add_one (n:KNat) : n♯  = n + 1 := by
  calc
    n♯  = (n + 0)♯  := by rw [add_zero]
      _ = n + 0♯  := by rw [←add_succ]
      _ = n + 1   := by rw [zero_succ]


/-- Proposition 2.2.4 (Addition is commutative). Compare with Mathlib's {name}`KNat.add_comm` -/
theorem KNat.add_comm (n m:KNat) : n + m = m + n := by
  induction' m with k hk
  rw [zero_eq]
  rw [add_zero,zero_add]
  calc
    (n + k♯)
      = (n+k)♯ := by rw [add_succ]
    _ = (k + n)♯ := by rw [hk]
    _ = (k♯ + n) := by rw [succ_add]
  


/-- Proposition 2.2.5 (Addition is associative) / Exercise 2.2.1
    Compare with Mathlib's {name}`KNat.add_assoc`. -/
theorem KNat.add_assoc (a b c:KNat) : (a + b) + c = a + (b + c) := by
  induction' c with k hk  
  · rw [zero_eq,add_zero,add_zero]
  calc
    a + b + k♯
      = (a + b + k)♯  := by rw [add_succ]
    _ = (a + (b + k))♯   := by rw [hk]
    _ = a + (b + k)♯   := by rw [add_succ]
    _ = a + (b + k♯) := by rw [←add_succ]  
   
/-- Proposition 2.2.6 (Cancellation law).
    Compare with Mathlib's {name}`KNat.add_left_cancel`. -/
theorem KNat.add_left_cancel (a b c:KNat) (habc: a + b = a + c) : b = c := by
  induction' a with k hk
  rwa [zero_eq,zero_add,zero_add] at habc
  apply hk
  apply succ_inj  
  rw [succ_add,succ_add] at habc
  exact habc
  
  
  

theorem KNat.add_right_cancel (a b c:KNat) (habc: a + c = b + c) : a = b := by
  rw [add_comm a c,add_comm b c] at habc  
  exact KNat.add_left_cancel c a b habc
  
/-- (Not from textbook) {name}`KNat` can be given the structure of a commutative additive monoid.
This permits tactics such as {tactic}`abel` to apply to the Chapter 2 natural numbers. -/
instance KNat.addCommMonoid : AddCommMonoid KNat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec


/-- Definition 2.2.7 (Positive natural numbers).-/
def KNat.IsPos (n:KNat) : Prop := n ≠ 0

theorem KNat.isPos_iff (n:KNat) : n.IsPos ↔ n ≠ 0 := by rfl

/-- Proposition 2.2.8 (positive plus natural number is positive).
    Compare with Mathlib's {name}`KNat.add_pos_left`. -/
theorem KNat.add_pos_left {a:KNat} (b:KNat) (ha: a.IsPos) : (a + b).IsPos := by
  rcases a with (_|preda)
  apply False.elim
  unfold IsPos at ha
  rw [zero_eq] at ha
  apply ha
  rfl
  rw [succ_add]
  exact succ_ne (preda + b)  
  


/-- Compare with Mathlib's {name}`Nat.add_pos_right`.

This theorem is a consequence of the previous theorem and {name}`add_comm`, and {tactic}`grind` can automatically discover such proofs.
-/
theorem KNat.add_pos_right {a:KNat} (b:KNat) (ha: a.IsPos) : (b + a).IsPos := by
  rw [add_comm]
  exact @add_pos_left a b ha

/-- Corollary 2.2.9 (if sum vanishes, then summands vanish).
    Compare with Mathlib's {name}`Nat.add_eq_zero`. -/
theorem KNat.add_eq_zero (a b:KNat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  have helper (c d : KNat) (hcd : c + d = 0) : c = 0 := by
    by_contra h0
    rcases c with (_|predc)
    apply h0
    rfl
    clear h0
    rw [succ_add] at hcd
    have := succ_ne (predc + d)
    exact this hcd    
  apply And.intro (helper a b hab)
  rw [add_comm] at hab
  exact (helper b a hab)




/-- Lemma 2.2.10 (unique predecessor) / Exercise 2.2.2 -/
lemma KNat.uniq_succ_eq (a:KNat) (ha: a.IsPos) : ∃! b, b♯  = a := by
  rcases a with (_|preda)
  · apply False.elim
    unfold IsPos at ha
    apply ha
    rfl
  use preda
  apply And.intro rfl
  intro y hy
  exact succ.inj hy


/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the {kw (of := «term_≤_»)}`≤` notation on the natural numbers. -/
instance KNat.instLE : LE KNat where
  le n m := ∃ a:KNat, m = n + a

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the {kw (of := «term_<_»)}`<` notation on the natural numbers. -/
instance KNat.instLT : LT KNat where
  lt n m := ∃ a : KNat, m = n + a♯ 

/-- Compare with Mathlib's {name}`le_iff_exists_add`. -/
lemma KNat.le_iff (n m:KNat) : n ≤ m ↔ ∃ a:KNat, m = n + a := by rfl

lemma KNat.lt_iff (n m:KNat) : n < m ↔ (∃ a:KNat, m = n + a♯) := by rfl
  
  
  
  
  

/-- Compare with Mathlib's {name}`ge_iff_le`. -/
@[symm]
lemma KNat.ge_iff_le (n m:KNat) : n ≥ m ↔ m ≤ n := by rfl

/-- Compare with Mathlib's {name}`gt_iff_lt`. -/
@[symm]
lemma KNat.gt_iff_lt (n m:KNat) : n > m ↔ m < n := by rfl

/-- Compare with Mathlib's {name}`Nat.le_of_lt`. -/
lemma KNat.le_of_lt {n m:KNat} (hnm: n < m) : n ≤ m := sorry

/-- Compare with Mathlib's {name}`Nat.le_iff_lt_or_eq`. -/
lemma KNat.le_iff_lt_or_eq (n m:KNat) : n ≤ m ↔ n < m ∨ n = m := by
  apply Iff.intro
  rintro ⟨ℓ,rfl⟩
  rcases ℓ with (_|predℓ)
  rw [zero_eq]
  apply Or.inr
  rw [add_zero]
  apply Or.inl
  use predℓ
  rintro (⟨ℓ,rfl⟩|rfl)
  use ℓ♯
  use 0
  rw [add_zero]
  



/-- Compare with Mathlib's {name}`Nat.lt_succ_self`. -/
theorem KNat.lt_sefl_succ (n:KNat) : n < n♯  := by
  use 0
  rw [add_succ,add_zero]

/-- Proposition 2.2.12 (Basic properties of order for natural numbers) / Exercise 2.2.3

(a) (Order is reflexive). Compare with Mathlib's {name}`Nat.le_refl`.-/



@[refl]
theorem KNat.le_refl (a:KNat) : a ≤ a := ⟨0,(add_zero a).symm⟩
  

/-- The refl tag allows for the {tactic}`rfl` tactic to work for inequalities. -/
example (a b:KNat): a+b ≥ a+b := by rfl

/-- (b) (Order is transitive).  The {tactic}`obtain` tactic will be useful here.
    Compare with Mathlib's {name}`Nat.le_trans`. -/
theorem KNat.ge_trans {a b c:KNat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  rcases hab with ⟨p,rfl⟩
  rcases hbc with ⟨q,rfl⟩
  use q + p
  rw [add_assoc]
  

lemma KNat.ne_add_succ (a b : KNat) : a ≠ a + b♯  := by
  intro h0
  induction' a with k hk
  have h1 : KNat.zero = 0 := by rfl
  have h2 := KNat.succ_ne b
  rw [h1,zero_add] at h0
  apply h2
  rw [h0]
  rw [KNat.succ_add] at h0
  apply hk (KNat.succ.inj h0)  
  

theorem KNat.le_trans {a b c:KNat} (hab: a ≤ b) (hbc: b ≤ c) : a ≤ c := KNat.ge_trans hbc hab

/-- (c) (Order is anti-symmetric). Compare with Mathlib's {name}`Nat.le_antisymm`. -/
theorem KNat.ge_antisymm {a b:KNat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  rcases hab with ⟨p,rfl⟩
  rcases p with (_|predp)
  have h1 : KNat.zero = 0 := rfl
  rw [h1,add_zero]
  sorry


/-- (d) (Addition preserves order).  Compare with Mathlib's {name}`Nat.add_le_add_right`. -/
theorem KNat.add_ge_add_right (a b c:KNat) : a ≥ b ↔ a + c ≥ b + c := by
  apply Iff.intro
  rintro ⟨r,rfl⟩
  use r
  rw [add_assoc,add_comm r c,←add_assoc]
  rintro ⟨r,ha⟩
  use r
  rw [add_assoc b c r,add_comm c r,←add_assoc] at ha
  exact KNat.add_right_cancel a (b + r) c ha

/-- (d) (Addition preserves order).  Compare with Mathlib's {name}`Nat.add_le_add_left`.  -/
theorem KNat.add_ge_add_left (a b c:KNat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's {name}`Nat.add_le_add_right`.  -/
theorem KNat.add_le_add_right (a b c:KNat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's {name}`Nat.add_le_add_left`.  -/
theorem KNat.add_le_add_left (a b c:KNat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b iff a\#  ≤ b.  Compare with Mathlib's {name}`Nat.succ_le_iff`. -/
theorem KNat.lt_iff_succ_le (a b:KNat) : a < b ↔ a♯  ≤ b := by
  apply Iff.intro
  · rintro ⟨ℓ,hℓ⟩
    use ℓ
    calc
      b = (a + ℓ♯) := hℓ
      _ = (a + ℓ)♯ := by rw [add_succ]
      _ = (a♯ + ℓ) := by rw [←succ_add]  
  rintro ⟨ℓ,hℓ⟩
  use ℓ
  calc
    b = (a♯ + ℓ) := hℓ
    _ = (a + ℓ)♯ := by rw [succ_add]
    _ = (a + ℓ♯) := by rw [←add_succ]  


/- /-- (f) a < b if and only if b = a + d for positive d. -/
 - theorem KNat.lt_iff_add_pos (a b:KNat) :
 -     a < b ↔ ∃ d:KNat, d.IsPos ∧ b = a + d := by  
 -   apply Iff.intro
 -   rintro ⟨⟨r,rfl⟩ ,h1⟩
 -   rcases r with (_|predr)
 -   have h2 : KNat.zero = 0 := by rfl
 -   rw [h2,add_zero] at h1
 -   apply False.elim
 -   apply h1
 -   rfl
 -   use (predr\# )
 -   apply And.intro
 -   unfold IsPos
 -   apply KNat.succ_ne
 -   rfl
 -   rintro ⟨r,h0,rfl⟩
 -   apply And.intro
 -   use r
 -   rcases r with (_|predr)
 -   have h2 : KNat.zero = 0 := by rfl
 -   rw [h2] at h0
 -   apply False.elim
 -   apply h0
 -   rfl
 -   apply L a predr -/
  

/-- If a < b then a ̸= b,-/
theorem KNat.ne_of_lt {a b:KNat} : a < b → a ≠ b := by 
  rintro ⟨ℓ,rfl⟩
  exact ne_add_succ a ℓ
  
  
  

/-- if a > b then a ̸= b. -/
theorem KNat.ne_of_gt (a b:KNat) : a > b → a ≠ b := by
  intro h0
  rw [ne_comm]
  exact ne_of_lt h0


/-- If a > b and a < b then contradiction -/
theorem KNat.not_lt_of_gt (a b:KNat) : a < b ∧ a > b → False := by
  rintro ⟨⟨ℓ,hℓ⟩,⟨p,hp⟩⟩
  rw [hℓ] at hp
  rw [add_assoc,add_succ] at hp
  have h1 := ne_add_succ a (ℓ♯ +p)
  exact h1 hp
  
  


theorem KNat.not_lt_self {a: KNat} (h : a < a) : False := by
  rcases h with ⟨ℓ,hℓ⟩
  have h1 := ne_add_succ a ℓ
  exact h1 hℓ  


theorem KNat.lt_of_le_of_lt {a b c : KNat} (hab: a ≤ b) (hbc: b < c) : a < c := by
  rcases hab with ⟨ℓ,rfl⟩
  rcases hbc with ⟨θ,rfl⟩
  use (ℓ + θ)
  rw [add_succ,add_succ,add_assoc]


/-- This lemma was a {lit}`why?` statement from Proposition 2.2.13,
but is more broadly useful, so is extracted here. -/
theorem KNat.zero_le (a:KNat) : 0 ≤ a := by
  use a
  rw [zero_add]  


/-- Proposition 2.2.13 (Trichotomy of order for natural numbers) / Exercise 2.2.4
    Compare with Mathlib's {name}`trichotomous`.  Parts of this theorem have been placed
    in the preceding Lean theorems. -/
theorem KNat.trichotomous (a b:KNat) : a < b ∨ a = b ∨ a > b := by
  induction' a with k hk
  rcases b with (_|predb)
  apply Or.inr
  apply Or.inl rfl
  apply Or.inl
  use predb
  rw [zero_eq,zero_add]
  rcases hk with (⟨ℓ,rfl⟩|rfl|⟨ℓ,rfl⟩ )
  rcases ℓ with (_|predℓ)
  apply Or.inr
  apply Or.inl
  rw [zero_eq,add_succ,add_zero]
  apply Or.inl
  use predℓ
  rw [add_succ,←succ_add]
  apply Or.inr
  apply Or.inr
  use 0
  rw [add_succ,add_zero]
  apply Or.inr
  apply Or.inr
  use ℓ♯
  rw [←add_succ]          
  


/--
  (Not from textbook) Establish the decidability of this order computably.  The portion of the
  proof involving decidability has been provided; the remaining sorries involve claims about the
  natural numbers.  One could also have established this result by the {tactic}`classical` tactic
  followed by {syntax tactic}`exact Classical.decRel _`, but this would make this definition (as well as some
  instances below) noncomputable.

  Compare with Mathlib's {name}`Nat.decLe`.
-/
def KNat.decLe : (a b : KNat) → Decidable (a ≤ b)
  | 0, b => by
    apply isTrue
    use b
    rw [zero_add]
  | a♯ , b => by
    cases decLe a b with
    | isTrue h =>
      cases decEq a b with
      | isTrue h1 =>
        apply isFalse
        intro h0
        rw [h1] at h0
        rcases h0 with ⟨r,h0⟩
        rw [succ_add,←add_succ] at h0
        have h1 := KNat.ne_add_succ b r        
        exact h1 h0
      | isFalse h0 =>
        apply isTrue
        rcases h with ⟨r,h⟩
        have h1 : KNat.zero = 0 := by rfl
        rcases r with (_|predr)
        apply False.elim
        rw [h1,add_zero] at h
        apply h0
        rw [h]
        use predr
        rw [h,add_succ,succ_add]        
        
    | isFalse h =>
      apply isFalse
      intro h1
      apply h
      clear h
      rcases h1 with ⟨r,rfl⟩
      use (r♯ )
      rw [succ_add,add_succ]      


instance KNat.decidableRel : DecidableRel (· ≤ · : KNat → KNat → Prop) := KNat.decLe

/-- (Not from textbook) {name}`KNat` has the structure of a linear ordering. This allows for tactics
such as {tactic}`order` and {tactic}`calc` to be applicable to the Chapter 2 natural numbers. -/
instance KNat.instLinearOrder : LinearOrder KNat where
  le_refl := le_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_ge a b := by
    apply Iff.intro
    · rintro ⟨ℓ,rfl⟩
      apply And.intro
      · use ℓ♯
      rintro ⟨θ,hθ⟩
      rw [add_assoc,succ_add] at hθ
      have h1 := ne_add_succ a (ℓ + θ)
      exact h1 hθ
    rintro ⟨⟨ℓ,rfl⟩,h1⟩
    rcases ℓ with (_|predℓ)
    · apply False.elim
      rw [zero_eq,add_zero] at h1
      apply h1
      rfl
    use predℓ    

  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total a b := by
    induction' a with k hk
    apply Or.inl
    use b
    rw [zero_eq,zero_add]
    rcases hk with (⟨ℓ,rfl⟩|⟨ℓ,rfl⟩)
    
    rcases ℓ with (_|predℓ)
    apply Or.inr
    use 1
    rw [zero_eq,add_zero,succ_eq_add_one]
    apply Or.inl
    use predℓ
    rw [add_succ,succ_add]
    apply Or.inr
    use ℓ♯
    rw [add_succ]      

  toDecidableLE := decidableRel


/-- (Not from textbook) {name}`KNat` has the structure of an ordered monoid. This allows for tactics
such as {tactic}`gcongr` to be applicable to the Chapter 2 natural numbers. -/
instance KNat.isOrderedAddMonoid : IsOrderedAddMonoid KNat where
  add_le_add_left a b hab c := (KNat.add_le_add_right a b c).mp hab

/-- Proposition 2.2.14 (Strong principle of induction) / Exercise 2.2.5
    Compare with Mathlib's {name}`Nat.strong_induction_on`.
-/



theorem KNat.strong_induction {P: KNat → Prop}
  (hind: ∀ m: KNat,(∀ m', m' < m → P m') → P m) :
    ∀ m: KNat, P m := by  
  intro m
  have h1 : ∀ m' : KNat, m' < m → P m' := by
    induction' m with k hk
    · intro mm hmm
      apply False.elim
      rcases hmm with ⟨ℓ,hℓ⟩
      rw [zero_eq,add_succ] at hℓ
      have h1 := succ_ne (mm + ℓ)
      apply h1
      rw [hℓ]
      
    intro m' hm
    rcases em (m' < k) with (hmm|hmm)
    exact hk m' hmm
    push_neg at hmm
    have hmmm : m' = k := by
      apply le_antisymm
      rcases hm with ⟨ℓ,hℓ⟩
      use ℓ
      rw [add_succ] at hℓ
      apply succ_inj hℓ
      exact hmm
    rw [hmmm]    
    have hind' := hind k
    apply hind' hk    
  exact hind m h1
  
    
  
  



/-- Exercise 2.2.6 (backwards induction)
    Compare with Mathlib's {name}`Nat.decreasingInduction`. -/
theorem KNat.backwards_induction {n:KNat} {P: KNat → Prop}
  (hind: ∀ m, P (m♯ ) → P m) (hn: P n) :
    ∀ m, m ≤ n → P m := by
  sorry

/-- Exercise 2.2.7 (induction from a starting point)
    Compare with Mathlib's {name}`Nat.le_induction`. -/
theorem KNat.induction_from {n:KNat} {P: KNat → Prop} (hind: ∀ m, P m → P (m♯ )) :
    P n → ∀ m, m ≥ n → P m := by
  intro hstart m ⟨r,hmbig⟩
  rw [hmbig];   clear hmbig
  induction' r with k hk
  have h1 : KNat.zero = 0 := by rfl
  rw [h1,add_zero]
  exact hstart
  rw [add_succ]
  exact hind (n+k) hk

end KChapter2
