--- Q[-1,1] is the set of all rationals p such that -1  p  1.
import data.rat
import set_theory.zfc.basic
import data.vector
import data.rat
import tactic
import tactic.rewrite_all.basic
open vector
open_locale big_operators


def in_range (q:ℚ) : Prop := (( q > -1) ∧  (q < 1))
local notation `Q[-11]` := {x : ℚ // in_range x}
--We will use a,b,c,d,e,p,q,r,s,t,u,v,w for rational numbers in Q[-1,1] unless indicated otherwise.
variables (a b c d e p q r s t u v w : Q[-11])
-- We use n,m,i,j,k for positive integers unless otherwise indicated. 
variables (n m i j k : ℕ)
-- We use A,B,C,D,E,S,T,U,V for subsets of Q[-1,1]2 unless indicated otherwise. We use  for subset.
-- variables (A B C D E S T U V :  set ( Q[-11] ×  Q[-11]) )

--A
-- k is the set of all k-tuples of elements of A. They are written (x1,...,xk), where x1,...,xk  A. Usually, we focus on small k, say k = 1,2,3,4. 
def type_tuple (t:Type ) (n : ℕ )  : Type := vector t n
def tuple (n : ℕ ) : Type := type_tuple  ℚ n 

variables (A B C D E S T U V :   set (type_tuple ℚ k )) [fintype ↥S]
variables (v1 v2 v3 :   type_tuple ℚ k) 


-- start of the first file. put other stuff in a new file

-- definition of order equivalence
def order_equivalent (k : ℕ) (x y : vector ℚ k) : Prop :=
  ∀ (i j : fin k), (x.nth i) < (x.nth j) ↔ (y.nth i) < (y.nth j)

-- order equivalence is an equivalence relation
theorem order_equiv_is_equiv (k : ℕ) : equivalence (order_equivalent k) :=
begin
  split,
  intros x i j,
  refl,
  split,
  intros x y h i j,
  rw h i j,
  intros x y z h1 h2 i j,
  rw h1 i j,
  rw h2 i j,
end

-- equivalence classes under order equivalence
def oe (k : ℕ) : setoid (vector ℚ k) := {
  r := order_equivalent k,
  iseqv := order_equiv_is_equiv k
}
attribute [instance] oe

-- QoL
lemma quotient_eq {k : ℕ} (a b : vector ℚ k) : ⟦a⟧ = ⟦b⟧ ↔ order_equivalent k a b := 
begin
  rw quotient.eq,
  refl,
end

-- E is an emulator of S iff the concatenation of any two elements of E 
-- is order equivalent to a concatenation of some two elements of S
def is_emulator {k : ℕ} (E S : set (vector ℚ k)): Prop :=
∀ (x y ∈ E), ∃ (z w ∈ S), order_equivalent (k+k) (vector.append x y) (vector.append z w)

-- The EC is the set of equivalence classes of concatenations
def EC {k : ℕ} (S : set (vector ℚ k)) : set (quotient (oe (k+k))) :=
{c : quotient (oe (k+k)) | ∃ (x y ∈ S), c = ⟦vector.append x y⟧}

-- E is an emulator of S iff the EC of E is a subset of the EC of S
theorem emulator_iff_EC_subset {k : ℕ} (E S : set (vector ℚ k)) :
  is_emulator E S ↔ EC E ⊆ EC S :=
begin
  split,
  intros h x,
  apply quotient.induction_on x,
  intros a hE,
  rcases hE with ⟨x,y,hxE,hyE,he⟩,
  rcases h x y hxE hyE with ⟨z,w,hzS,hwS,h⟩,
  rw ← quotient_eq at h,
  rw he,
  exact ⟨z,w,⟨hzS,hwS,by rw h⟩⟩,

  intros h x hxE y hyE,
  have hEC : ⟦vector.append x y⟧ ∈ EC E,
    from ⟨x, hxE, y, hyE,by refl⟩,
  rcases h hEC with ⟨z,w,hzS,hwS,h⟩,
  rw quotient_eq at h,
  exact ⟨z,w,hzS,hwS,h⟩,
end

-- The EC of a subset is a subset of the EC
theorem subset_EC_subset {k : ℕ} (E S : set (vector ℚ k)) :
  E ⊆ S → EC E ⊆ EC S :=
begin
  intros hES x,
  apply quotient.induction_on x,
  intros a haE,
  rcases haE with ⟨x,hxE,y,hyE,h⟩,
  -- exact x,
  exact ⟨x,hES hxE,y,hES hyE,by rw h⟩,
end

-- Every subset is an emulator
theorem subset_emulator {k : ℕ} (E S : set (vector ℚ k)) :
  E ⊆ S → is_emulator E S :=
begin
  rw emulator_iff_EC_subset,
  exact subset_EC_subset E S,
end

-- Anything is an emulator of itself
theorem emulator_refl {k : ℕ} (S : set (vector ℚ k)) :
  is_emulator S S :=
begin
  apply subset_emulator,
  exact rfl.subset,
end

-- Emulator-ness is transitive
theorem emulator_trans {k : ℕ} (A B C : set (vector ℚ k)) :
  is_emulator A B → is_emulator B C → is_emulator A C :=
begin
  intros h1 h2,
  rw emulator_iff_EC_subset at h1 h2 ⊢,
  exact set.subset.trans h1 h2,
end

-- Two sets are related iff they are emulators of each other
def related {k : ℕ} (S T : set (vector ℚ k)) : Prop :=
  is_emulator S T ∧ is_emulator T S

-- Two sets are related iff the ECs are equal
theorem related_iff_EC_eq {k : ℕ} (S T : set (vector ℚ k)) :
  related S T ↔ EC S = EC T := 
begin
  split,
  rintro ⟨h1,h2⟩,
  rw emulator_iff_EC_subset at h1 h2,
  exact set.subset.antisymm h1 h2,

  intro h,
  split,
  rw emulator_iff_EC_subset,
  exact eq.subset h,
  rw emulator_iff_EC_subset,
  exact (eq.symm h).subset,
end

-- Two sets are related iff they have the same emulators
theorem related_iff_same_emulator {k : ℕ} (S T : set (vector ℚ k)) :
  related S T ↔ ∀ (E : set (vector ℚ k)), (is_emulator E S ↔ is_emulator E T) := 
begin
  split,
  rintros ⟨h1,h2⟩ E,
  rw emulator_iff_EC_subset at h1 h2 ⊢,
  rw emulator_iff_EC_subset,
  split,
    intro h,
    exact set.subset.trans h h1,
    intro h,
    exact set.subset.trans h h2,

  intro h,
  have h1 := (h S).1 (emulator_refl S),
  have h2 := (h T).2 (emulator_refl T),
  exact ⟨h1,h2⟩,
end

-- Two sets have the same emulators iff the ECs are equal
theorem same_emulator_iff_EC_eq {k : ℕ} (S T : set (vector ℚ k)) :
  (∀ (E : set (vector ℚ k)), (is_emulator E S ↔ is_emulator E T)) ↔ EC S = EC T :=
begin
  rw ← related_iff_same_emulator,
  rw related_iff_EC_eq,
end

-- Related-ness is an equivalence relation
theorem related_refl {k : ℕ} (S : set (vector ℚ k)) :
  related S S :=
begin
  exact ⟨emulator_refl S,emulator_refl S⟩,
end

theorem related_symm {k : ℕ} (S T : set (vector ℚ k)) :
  related S T → related T S :=
begin
  rintro ⟨h1,h2⟩,
  exact ⟨h2,h1⟩,
end

theorem related_trans {k : ℕ} (A B C : set (vector ℚ k)) :
  related A B → related B C → related A C :=
begin
  rintros ⟨h1,h2⟩ ⟨h3,h4⟩,
  exact ⟨emulator_trans A B C h1 h3,
        emulator_trans C B A h4 h2⟩,
end





-- new file here

/-
--ORDER INVARIANT. S  Q[-1,1]2 is order invariant if and only if for all order equivalent x,y  Q[-1,1]2, x  S  y  S. 

def is_order_invaraint (S:set (type_tuple ℚ k )) : Prop := 
   ∀ (x y : type_tuple ℚ k ), (order_equivalent k x y) → (x ∈ S ↔ y ∈ S )

def is_linear (f : type_tuple ℚ k  → Prop): Prop := ∃(c :ℚ), ∃(n m:fin k), 
(f =λ x, x.nth n > c)
∨ 
(f =λ x, x.nth n < c)
∨ 
(f =λ x, x.nth n < x.nth m)

def is_linear_comb (f : type_tuple ℚ k  → Prop): Prop := ∃ (g h :  type_tuple ℚ k  → Prop),
f =λx, g x ∧ h x ∧ is_linear k g ∧ is_linear k h
def is_order_theoretic (S:set (type_tuple ℚ k )):Prop 
:= ∃ (f : (type_tuple ℚ k  → Prop)),  is_linear_comb k f
-/

--(1,4), (4,1), (2,3), (3,2), (2,5), (5,2), (4,5), (5,4), (2,2), (3,3)
def ex: finset (type_tuple ℚ 2 )
  := {
    vector.cons 1 (vector.cons 4 vector.nil),
    vector.cons 4 (vector.cons 1 vector.nil),
    vector.cons 2 (vector.cons 3 vector.nil),
    vector.cons 3 (vector.cons 2 vector.nil),
    vector.cons 2 (vector.cons 5 vector.nil),
    vector.cons 5 (vector.cons 2 vector.nil),
    vector.cons 4 (vector.cons 5 vector.nil),
    vector.cons 5 (vector.cons 4 vector.nil),
    vector.cons 2 (vector.cons 2 vector.nil),
    vector.cons 3 (vector.cons 3 vector.nil)
    }

lemma excard: (ex.card = 10) := begin
sorry,
end

-- Maybe a new file for this
-- OPEN PROBLEM B. What is the smallest cardinality m of such an E in 11? What is the relationship between the n in Open Problem A and this m here? 
theorem open_problem_B: 
∃ (S : finset (vector ℚ 2 )) ,
 S.card = 10 ∧ 
 ∀ (E:set (vector ℚ 2 )), 
 (@is_emulator 2 (E) (↑S)) := begin
use ex,
split,
{
  exact excard,
},
intros E,
-- simp,
sorry,
end
def EM {k} (S: set (type_tuple ℚ k)): set (set (type_tuple ℚ k)) := {E : set (type_tuple ℚ k)| is_emulator E S }
lemma EC_implies_Same_emulators: (EC E = EC S ↔ (EM E = EM S)) := begin
sorry,
end
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
∀(S: set (type_tuple ℚ 2)), 
∃ (S' : finset (type_tuple ℚ 2)), ↑S' ⊆ S 
∧ S'.card ≤  150 ∧ 
∀(E: set (type_tuple ℚ 2)), 
(EM (↑S')  = EM S)  
:= begin
let x:ℕ := ot 4,
have x_ot_4  : x = ot 4 := by refl,
have x_eq_150: x = 150 := begin
rw x_ot_4,
sorry,
end,
intros S,
-- rw ←  EC_implies_Same_emulators,
sorry,
end

