--- Q[-1,1] is the set of all rationals p such that -1  p  1.
import data.rat
import set_theory.zfc.basic

def in_range (q:ℚ) : Prop := (( q > -1) ∧  (q < 1))
local notation `Q[-11]` := {x : ℚ // in_range x}
--We will use a,b,c,d,e,p,q,r,s,t,u,v,w for rational numbers in Q[-1,1] unless indicated otherwise.
variables (a b c d e p q r s t u v w : Q[-11])
-- We use n,m,i,j,k for positive integers unless otherwise indicated. 
variables (n m i j k : ℕ)
-- We use A,B,C,D,E,S,T,U,V for subsets of Q[-1,1]2 unless indicated otherwise. We use  for subset.
-- variables (A B C D E S T U V :  set ( Q[-11] ×  Q[-11]) )

--A
-- k is the set of all k-tuples of elements of A. They are written (x1,...,xk), where x1,...,xk  A. Usually, we focus on small k, say k = 1,2,3,4. 
def type_tuple (t:Type ) (n : ℕ )  : Type := vector t n
def tuple (n : ℕ ) : Type := type_tuple  ℚ n 

variables (A B C D E S T U V :   set (type_tuple ℚ 2 )) 

-- -DEFINITION 4.2.1. Let x,y  Qk. x,y are order equivalent if and only if for all 1  i,j  k, xi < xj  yi < yj.
-- x,y are order equivalent iff for all 1≤i,j≤k, xi < xj iff yi < yj.
def order_equivalent (k: ℕ) (x: tuple k) (y: tuple k) : Prop :=
∀(i j: fin k), (x.nth i) < (x.nth j) ↔ (y.nth i) < (y.nth j)


 --THEOREM 4.2.1. Order equivalence is an equivalence relation on Qk. I.e., for all x,y,z  Qk, 
-- i. x,x are order equivalent.
-- ii. x,y are order equivalent if and only if y,x are order equivalent.
theorem order_equiv_is_equiv (k: ℕ): equivalence (order_equivalent k) :=
begin
  -- intro k,
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
-- An emulator of E  Q[-1,1]
-- 2 is an S  Q[-1,1]2 such that any pair of elements of S "look like" some pair of elements of E. I.e., for all x,y  S there exists z,w  E such that xy is order equivalent to zw. Note that we are allowing E to be finite or infinite, or even .
def is_emulator : Prop := ∀ (x y ∈   S), ∃ (z w ∈  E), (order_equivalent (4 : ℕ)  (vector.append x y) (vector.append z w))


-- Every subset of E is an emulator of E.
theorem subset_is_emulator:  E ⊆  S → is_emulator E S :=
begin
sorry,
end
-- -If S is an emulator of E and T is an emulator of S then T is an emulator of E.
theorem emulator_transitivity:   is_emulator S E ∧ is_emulator T S → is_emulator T E :=
begin
sorry,
end

def oe (k : ℕ): setoid (tuple k) := {
  r := order_equivalent k,
  iseqv := order_equiv_is_equiv k
}