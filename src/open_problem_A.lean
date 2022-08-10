import basic
import data.setoid.partition

open_locale big_operators
open emulators
variables (n m i j k : ℕ)
-- stirling numbers of the second kind
--S2(n, k) = k*S2(n-1, k) + S2(n-1, k-1), n > 1. 
--S2(1, k) = 0, k > 1. 
-- S2(1, 1) = 1.
-- def S2 : ℕ → ℕ → ℕ 
--   | (nat.succ x) 0:= 0
--   | 0 0 :=1
--   | 0 x := 0
--   | 1 1 := 1
--   |1  (nat.succ k) := 0
--   | (nat.succ n) (nat.succ k) := (nat.succ k)*(S2 n (nat.succ k))+ S2 n k
-- --ot(k) is also the number of ways a horse race with k horses can end with ties allowed.
-- -- here is an entry on these ot(k), and they are called Fubini Numbers. See https://oeis.org/A000670 about these Fubini numbers, ot(k).
-- def ot:  ℕ → ℕ 
--   | 0 := 1
--   | x := ∑  n in finset.range (x+1),  (S2 x n)*(nat.factorial x)
theorem sub_less (n k :ℕ )  : n - k < n.succ := begin

 sorry,
end

def ot:  ℕ → ℕ 
  | 0 := 1 
  | (nat.succ n) :=
    ∑  k in finset.range (n+1),  
    -- have k < n+1, from (@finset.mem_range (n+1) k),
    have n - k < n.succ, from (sub_less n k),
    (nat.choose (n+1) (k+1))*ot(n-k)

  
  
  
  -- have  n - k < n + 1, from sub_less (n) k,
  -- ∑  k in finset.range (n+1),  (nat.choose (n+1) (k+1))*ot(n-k)


lemma EC_is_finite: ∀(E: finset (vector ℚ k)), (@EC k ↑E).finite :=
begin
intros E,
rw EC,
have qu_finite: fintype (quotient (oe (k + k))) := begin
-- quotient.finite ( (oe (k + k))),
-- apply quotient.fintype,
sorry,
end,

sorry,
end
instance EC_fintype : fintype ↥((oe k).classes) := begin
sorry,
end
@[simp]
lemma OE_card_eq_OT : ∀(k:ℕ), (oe k).classes.to_finset.card = ot k :=
begin
intros k,
apply  nat.case_strong_induction_on  k,
{
sorry,
},
intros n hn,
rw ot,
have := hn (n-k),

sorry,
end

lemma ot4: ot 4  = 75 := begin
 sorry,
end
-- THEOREM 4.3.1. Every E ⊆ Q[-1,1]2 has the same emulators as some E' ⊆ E of cardinality ≤ 150.
theorem open_problem_A: 
∀(S: set (vector ℚ 2)), 
∃ (S' : finset (vector ℚ 2)), ↑S' ⊆ S 
∧ S'.card ≤  150 ∧ 
∀(E: set (vector ℚ 2)), 
(EM (↑S')  = EM S)  
:= begin
let x:ℕ := ot 4,
have x_ot_4  : x = ot 4 := by refl,
have x_eq_150: x = 75 := begin
rw x_ot_4,
rw ot,
simp,
sorry,
end,
intros S,
-- rw ←  EC_implies_Same_emulators,
sorry,
end

