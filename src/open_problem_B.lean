import basic
open emulators
--(1,4), (4,1), (2,3), (3,2), (2,5), (5,2), (4,5), (5,4), (2,2), (3,3)
def ex: finset (vector ℚ 2 )
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
