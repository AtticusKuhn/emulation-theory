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

variables (A B C D E S T U V :   set (type_tuple ℚ 2 )) 

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
sorry,
end
-- -If S is an emulator of E and T is an emulator of S then T is an emulator of E.
theorem emulator_transitivity:   is_emulator S E ∧ is_emulator T S → is_emulator T E :=
begin
sorry,
end

--This is useless
--ORDER INVARIANT. S  Q[-1,1]2 is order invariant if and only if for all order equivalent x,y  Q[-1,1]2, x  S  y  S. 

def is_order_invaraint (S:set (type_tuple ℚ 2 )) : Prop := 
   ∀ (x y : type_tuple ℚ 2 ), (order_equivalent 2 x y) → (x ∈ S ↔ y ∈ S )

def x: vector ℕ  2  :=  vector.cons 2 (vector.cons 2 vector.nil)
