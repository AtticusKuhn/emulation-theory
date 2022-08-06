--- Q[-1,1] is the set of all rationals p such that -1  p  1.
import data.rat
import set_theory.zfc.basic
import data.vector
import data.rat
import tactic
open vector


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
variables (v1 v2 v3 :   vector ℚ k) 

-- definition of order equivalence
def order_equivalent (k : ℕ) (x : vector ℚ k) (y : vector ℚ k) : Prop :=
∀(i j : fin k), (x.nth i) < (x.nth j) ↔ (y.nth i) < (y.nth j)

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
lemma quotient_eq' (k : ℕ) (a b : vector ℚ k) : ⟦a⟧ = ⟦b⟧ ↔ order_equivalent k a b := 
begin
  rw quotient.eq,
  refl,
end

-- set of equivalence classes of concatenations
def EC {k : ℕ} (S : set (vector ℚ k)) : set (quotient (oe (k+k))) :=
{c : quotient (oe (k+k)) | ∃ (x y ∈ S), c = ⟦vector.append x y⟧}

-- definition of emulators
def is_emulator {k : ℕ} (E S : set (vector ℚ k)): Prop :=
∀ (x y ∈ E), ∃ (z w ∈ S), order_equivalent (k+k) (vector.append x y) (vector.append z w)

-- very useful relation between emulators and EC's
theorem emulator_iff_EC_subset (k : ℕ) {E S : set (vector ℚ k)}: 
  is_emulator E S ↔ (EC E) ⊆ (EC S) :=
begin
  split,
  intros h x,
  apply quotient.induction_on x,
  intros a hE,
  rcases hE with ⟨x,y,hxE,hyE,he⟩,
  rcases h x y hxE hyE with ⟨z,w,hzS,hwS,h⟩,
  rw ← quotient_eq' at h,
  rw he,
  exact ⟨z,w,⟨hzS,hwS,by rw h⟩⟩,

  intros h x y hxE hyE,

  have hEC : ⟦vector.append x hxE⟧ ∈ EC E,
    from ⟨x,y,hxE,hyE,by refl⟩,
  rcases h hEC with ⟨z,w,hzS,hwS,h⟩,
  rw quotient_eq' at h,
  exact ⟨z,w,hzS,hwS,h⟩,
end

-- Every subset of E is an emulator of E.
theorem subset_is_emulator:  E ⊆  S → is_emulator  E S :=
begin
  intros E_subset_S,
  rw is_emulator,
  intros x x_in_E y y_in_E,
  use  x ,
  split,
  exact set.mem_of_subset_of_mem E_subset_S x_in_E,
  use y,
  split,
  exact set.mem_of_subset_of_mem E_subset_S y_in_E,
  exact (order_equiv_is_equiv (k+k)).1  (x.append y),
end
-- -If S is an emulator of E and T is an emulator of S then T is an emulator of E.

theorem emulator_trans :
  is_emulator A B → is_emulator B C → is_emulator A C :=
begin
  intros h1 h2,
  rw emulator_iff_EC_subset at h1 h2 ⊢,
  exact subset_trans h1 h2,
end

--This is useless
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


-- OPEN PROBLEM B. What is the smallest cardinality m of such an E in 11? What is the relationship between the n in Open Problem A and this m here? 
theorem open_problem_B: ∃ (S : set (type_tuple ℚ k )) [fintype ↥S] , S.to_finset.card = 10 := begin

sorry,
end