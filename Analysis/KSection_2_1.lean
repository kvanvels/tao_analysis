import Mathlib.Tactic

namespace KChapter2


inductive KNat where
| zero : KNat
| succ : KNat → KNat
deriving Repr, DecidableEq  -- this allows `decide` to work on `Nat`

/-- Axiom 2.1 (0 is a natural number) -/
instance KNat.instZero : Zero KNat := ⟨ zero ⟩

/-- Axiom 2.2 (Successor of a natural number is a natural number) -/
postfix:100 "♯" => KNat.succ



/-- Definition 2.1.3 (Definition of the numerals 0, 1, 2, etc.). Note:
to avoid ambiguity, one may need to use explicit casts such as
{lean}`(0:KNat)`, {lean}`(1:KNat)`, etc. to refer to this
  chapter's version of the natural numbers.  -/  
instance KNat.instOfNat {n:_root_.Nat} : OfNat KNat n where
  ofNat := _root_.Nat.rec 0 (fun _ n ↦ n♯) n

lemma KNat.zero_succ : 0♯ = 1 := by rfl

theorem KNat.succ_ne (n:KNat) : n♯ ≠ 0 := by
  by_contra h
  injection h

/--
  Axiom 2.4 (Different natural numbers have different successors).
  Compare with Mathlib's {name}`Nat.succ_inj`.
-/
theorem KNat.succ_inj {n m:KNat} (hnm: n♯ = m♯) : n = m := by  
  injection hnm

theorem KNat.succ_ne_succ (n m:KNat) : n ≠ m → n♯ ≠ m♯ := by
  intro h
  contrapose! h
  exact succ_inj h

theorem KNat.induction (P : KNat → Prop) (hbase : P 0) (hind : ∀ n, P n → P (n♯)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih => exact hind _ ih

/--
  Recursion. Analogous to the inbuilt Mathlib method {name}`Nat.rec` associated to
  the Mathlib natural numbers
-/
abbrev KNat.recurse (f: KNat → KNat → KNat) (c: KNat) : KNat → KNat := fun n ↦ match n with
| 0 => c
| n♯ => f n (recurse f c n)

/-- Proposition 2.1.16 (recursive definitions). Compare with Mathlib's {name}`Nat.rec_zero`. -/
theorem KNat.recurse_zero (f: KNat → KNat → KNat) (c: KNat) : KNat.recurse f c 0 = c := by rfl

/-- Proposition 2.1.16 (recursive definitions). Compare with Mathlib's {name}`Nat.rec_add_one`. -/
theorem KNat.recurse_succ (f: KNat → KNat → KNat) (c: KNat) (n: KNat) :
    recurse f c (n♯) = f n (recurse f c n) := by rfl

/-- Proposition 2.1.16 (recursive definitions). -/
theorem KNat.eq_recurse (f: KNat → KNat → KNat) (c: KNat) (a: KNat → KNat) :
    (a 0 = c ∧ ∀ n, a (n♯) = f n (a n)) ↔ a = recurse f c := by
  constructor
  . intro ⟨ h0, hsucc ⟩
    -- this proof is written to follow the structure of the original text.
    apply funext; apply induction
    . exact h0
    intro n hn
    rw [hsucc n, recurse_succ, hn]
  intro h
  rw [h]
  constructor -- could also use `split_ands` or `and_intros` here
  . exact recurse_zero _ _
  exact recurse_succ _ _


/-- Proposition 2.1.16 (recursive definitions). -/
theorem KNat.recurse_uniq (f: KNat → KNat → KNat) (c: KNat) :
    ∃! (a: KNat → KNat), a 0 = c ∧ ∀ n, a (n♯) = f n (a n) := by
  apply ExistsUnique.intro (recurse f c)
  . constructor -- could also use `split_ands` or `and_intros` here
    . exact recurse_zero _ _
    . exact recurse_succ _ _
  intro a
  exact (eq_recurse _ _ a).mp



end KChapter2
