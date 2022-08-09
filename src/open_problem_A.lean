import basic
open_locale big_operators
open emulators
variables (n m i j k : ℕ)
-- stirling numbers of the second kind
--S2(n, k) = k*S2(n-1, k) + S2(n-1, k-1), n > 1. 
--S2(1, k) = 0, k > 1. 
-- S2(1, 1) = 1.
def S2 : ℕ → ℕ → ℕ 
  | (nat.succ x) 0:= 0
  | 0 0 :=1
  | 0 x := 0
  | 1 1 := 1
  |1  (nat.succ k) := 0
  | (nat.succ n) (nat.succ k) := (nat.succ k)*(S2 n (nat.succ k))+ S2 n k
--ot(k) is also the number of ways a horse race with k horses can end with ties allowed.
-- here is an entry on these ot(k), and they are called Fubini Numbers. See https://oeis.org/A000670 about these Fubini numbers, ot(k).
def ot:  ℕ → ℕ 
  | 0 := 1
  | x := ∑  n in finset.range (x+1),  (S2 x n)*(nat.factorial x)
lemma EC_is_finite: ∀(E: finset (vector ℚ k)), (@EC k ↑E).finite :=
begin
sorry,
end
instance EC_fintype (E: finset (vector ℚ k)) : fintype (@EC k ↑E) := begin
sorry,
end
@[simp]
lemma EC_card :∀ (E: finset (vector ℚ k)), (@EC k ↑E).to_finset.card = ot E.card :=
begin
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
-- refl,
sorry,
end,
intros S,
-- rw ←  EC_implies_Same_emulators,
sorry,
end

