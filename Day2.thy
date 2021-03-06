theory Day2

imports Main "HOL-Library.Code_Target_Numeral"

begin

datatype move = forward nat | up nat | down nat

record position =
  horizontal :: nat
  vertical :: nat

definition apply_move :: "position \<Rightarrow> move \<Rightarrow> position" where
"apply_move pos m = 
  (case m of 
    forward n \<Rightarrow> pos\<lparr> horizontal := horizontal pos + n \<rparr> |
    up n \<Rightarrow> pos\<lparr> vertical := vertical pos - n \<rparr> |
    down n \<Rightarrow> pos\<lparr> vertical := vertical pos + n \<rparr>)"

definition "initial_position \<equiv> \<lparr> horizontal = 0, vertical = 0 \<rparr>"

definition position_after_course :: "move list \<Rightarrow> position" where
"position_after_course c = foldl apply_move initial_position c"

record aimed_position =
  horizontal :: nat
  vertical :: nat
  aim :: nat

definition apply_move_aim :: "aimed_position \<Rightarrow> move \<Rightarrow> aimed_position" where
"apply_move_aim pos m = 
  (case m of 
    forward n \<Rightarrow> pos\<lparr> horizontal := horizontal pos + n, vertical := vertical pos + aim pos * n \<rparr> |
    up n \<Rightarrow> pos\<lparr> aim := aim pos - n \<rparr> |
    down n \<Rightarrow> pos\<lparr> aim := aim pos + n \<rparr>)"

definition "initial_aimed_position \<equiv> \<lparr> horizontal = 0, vertical = 0, aim = 0 \<rparr>"

definition position_after_course_aim :: "move list \<Rightarrow> aimed_position" where
"position_after_course_aim c = foldl apply_move_aim initial_aimed_position c"

definition "data \<equiv> [
forward 4,
down 9,
forward 2,
forward 2,
down 7,
up 2,
down 9,
up 8,
down 7,
down 9,
forward 4,
up 6,
down 2,
down 5,
down 1,
down 5,
forward 2,
up 4,
forward 2,
forward 3,
up 2,
forward 6,
up 8,
forward 8,
down 8,
up 8,
down 7,
down 2,
down 9,
forward 2,
forward 9,
down 4,
forward 8,
up 6,
down 3,
up 9,
forward 1,
forward 6,
up 3,
forward 8,
up 9,
forward 1,
down 9,
down 3,
down 7,
up 2,
up 7,
down 5,
forward 3,
down 1,
up 6,
down 2,
forward 4,
down 6,
down 8,
forward 2,
down 5,
forward 6,
down 5,
down 7,
forward 8,
forward 2,
down 9,
up 4,
forward 6,
forward 4,
up 6,
down 9,
down 7,
down 9,
forward 9,
forward 8,
down 7,
up 7,
forward 9,
forward 8,
up 1,
up 4,
down 3,
forward 6,
up 6,
down 2,
up 3,
down 6,
down 5,
forward 8,
forward 3,
forward 8,
down 4,
down 4,
down 5,
forward 6,
down 5,
forward 6,
down 2,
down 5,
up 4,
down 8,
up 5,
forward 5,
forward 6,
down 9,
up 5,
down 2,
forward 5,
down 7,
up 7,
down 9,
forward 2,
down 3,
down 3,
forward 8,
up 5,
up 1,
forward 1,
forward 3,
down 5,
forward 8,
forward 7,
forward 8,
down 5,
down 8,
up 2,
forward 8,
forward 8,
down 7,
forward 1,
forward 7,
down 6,
up 4,
forward 7,
forward 7,
down 3,
up 7,
forward 2,
down 7,
down 4,
forward 5,
down 8,
forward 9,
down 7,
forward 5,
up 6,
up 6,
down 8,
down 3,
forward 5,
forward 3,
down 8,
up 7,
forward 8,
up 6,
down 2,
forward 4,
up 3,
up 3,
down 9,
down 9,
up 1,
up 7,
forward 2,
down 1,
forward 9,
up 7,
up 6,
down 2,
down 3,
forward 4,
down 3,
down 3,
down 1,
forward 4,
forward 8,
forward 6,
forward 3,
up 4,
up 5,
up 4,
forward 1,
up 3,
down 9,
up 6,
forward 2,
down 5,
down 1,
forward 8,
forward 2,
down 6,
up 5,
up 3,
forward 7,
forward 2,
forward 7,
up 9,
forward 3,
up 9,
forward 1,
down 9,
forward 9,
down 3,
down 3,
down 2,
forward 9,
forward 2,
up 3,
forward 3,
down 7,
down 3,
forward 2,
forward 1,
forward 6,
up 9,
forward 4,
down 9,
down 8,
up 3,
up 5,
forward 8,
down 9,
forward 5,
forward 4,
down 5,
up 4,
forward 7,
forward 3,
down 9,
forward 7,
down 2,
down 7,
forward 3,
up 3,
forward 7,
down 9,
down 4,
down 8,
forward 8,
down 6,
forward 9,
forward 4,
up 9,
down 9,
down 6,
up 7,
up 2,
forward 2,
forward 7,
down 7,
forward 9,
down 6,
down 2,
forward 4,
forward 8,
down 4,
forward 4,
forward 4,
forward 6,
up 6,
down 9,
down 3,
down 7,
up 2,
up 2,
forward 4,
down 4,
forward 6,
down 2,
down 2,
forward 1,
down 1,
forward 7,
up 5,
forward 9,
forward 8,
down 4,
forward 8,
down 5,
up 4,
down 8,
forward 4,
forward 7,
down 9,
down 3,
forward 6,
down 6,
forward 6,
down 9,
down 6,
forward 5,
forward 5,
up 9,
down 9,
down 9,
down 1,
down 5,
forward 5,
down 7,
forward 3,
down 6,
forward 5,
forward 8,
down 6,
forward 7,
down 5,
forward 4,
down 4,
down 9,
forward 3,
down 9,
down 9,
down 1,
up 7,
forward 4,
up 1,
up 1,
forward 1,
down 9,
up 8,
down 8,
down 3,
down 7,
forward 4,
down 5,
down 5,
forward 7,
forward 7,
forward 6,
up 2,
down 4,
forward 8,
forward 3,
forward 3,
forward 2,
forward 4,
up 9,
up 1,
forward 2,
forward 2,
forward 6,
down 9,
up 8,
forward 4,
forward 5,
forward 4,
down 4,
down 8,
forward 6,
down 8,
forward 9,
forward 8,
down 1,
down 2,
forward 2,
up 4,
up 7,
forward 5,
down 7,
down 5,
down 3,
up 7,
down 4,
forward 8,
up 8,
down 1,
down 2,
up 6,
up 8,
forward 9,
down 5,
down 2,
forward 5,
forward 4,
up 6,
forward 7,
down 3,
up 5,
up 9,
forward 5,
forward 1,
down 6,
down 7,
forward 9,
down 8,
down 2,
forward 9,
forward 2,
down 3,
forward 9,
down 3,
down 9,
up 3,
forward 7,
up 2,
up 5,
forward 3,
down 9,
up 1,
down 2,
down 4,
down 6,
forward 5,
forward 5,
up 7,
up 3,
down 1,
down 1,
up 8,
down 4,
forward 1,
down 4,
down 5,
down 9,
forward 7,
up 2,
up 1,
down 7,
forward 9,
forward 9,
forward 8,
forward 9,
down 5,
forward 9,
forward 9,
up 9,
down 7,
down 8,
forward 2,
forward 9,
down 1,
forward 3,
forward 8,
up 4,
down 4,
forward 4,
forward 3,
down 7,
down 3,
forward 6,
forward 9,
forward 1,
down 2,
up 3,
down 9,
forward 5,
forward 6,
forward 8,
up 2,
up 1,
down 3,
up 4,
forward 1,
up 9,
forward 4,
down 1,
up 2,
down 8,
down 9,
forward 3,
down 2,
up 5,
forward 2,
down 6,
down 5,
down 8,
down 3,
down 7,
down 2,
forward 8,
down 9,
up 7,
down 7,
down 7,
down 7,
forward 4,
forward 1,
forward 9,
up 9,
forward 5,
forward 8,
forward 7,
forward 7,
down 1,
forward 3,
down 7,
forward 2,
forward 4,
up 7,
forward 1,
down 5,
forward 5,
forward 1,
down 8,
forward 7,
forward 2,
up 3,
down 1,
up 7,
down 1,
down 2,
forward 9,
forward 6,
forward 3,
forward 2,
down 4,
forward 7,
forward 7,
forward 5,
forward 7,
forward 2,
down 9,
down 8,
forward 8,
forward 9,
down 3,
up 7,
up 1,
down 4,
forward 2,
forward 7,
forward 3,
forward 9,
up 2,
down 3,
forward 4,
down 8,
down 6,
down 4,
down 6,
down 7,
forward 9,
down 9,
forward 8,
down 1,
down 1,
forward 1,
forward 1,
down 7,
down 3,
down 3,
forward 2,
down 7,
forward 8,
up 7,
down 5,
forward 7,
forward 9,
down 2,
forward 9,
forward 3,
forward 9,
forward 9,
down 3,
forward 1,
forward 7,
up 8,
forward 7,
forward 4,
forward 5,
forward 6,
down 4,
up 3,
down 5,
up 8,
up 5,
up 6,
forward 1,
down 1,
up 8,
down 8,
down 5,
forward 8,
up 9,
down 8,
forward 2,
up 6,
forward 3,
down 3,
down 8,
down 4,
forward 6,
forward 2,
down 9,
up 9,
down 2,
down 9,
up 1,
down 6,
up 2,
down 9,
forward 8,
forward 3,
forward 6,
down 6,
up 9,
up 8,
forward 4,
down 2,
forward 5,
up 4,
up 4,
down 5,
down 9,
forward 3,
down 1,
forward 1,
forward 6,
forward 2,
down 7,
forward 7,
up 5,
forward 2,
down 8,
forward 5,
down 1,
down 7,
forward 7,
down 4,
forward 7,
forward 2,
down 6,
forward 9,
forward 4,
up 3,
forward 8,
forward 2,
up 6,
up 3,
forward 9,
forward 4,
down 2,
forward 6,
down 1,
forward 5,
down 2,
up 1,
down 1,
forward 2,
forward 4,
down 7,
up 6,
forward 4,
forward 7,
up 8,
forward 3,
down 8,
forward 7,
down 2,
down 5,
forward 3,
forward 7,
down 5,
forward 2,
forward 8,
up 6,
forward 8,
down 7,
up 3,
down 2,
forward 2,
down 8,
down 2,
up 5,
up 1,
forward 6,
down 1,
forward 2,
down 1,
forward 6,
forward 9,
down 9,
down 8,
down 3,
forward 5,
forward 3,
down 3,
down 1,
forward 4,
forward 8,
forward 2,
down 7,
forward 9,
forward 4,
down 4,
forward 6,
down 4,
forward 8,
down 8,
down 2,
up 7,
down 9,
down 5,
up 4,
down 3,
up 5,
forward 8,
down 4,
down 6,
forward 1,
up 2,
down 6,
forward 4,
down 8,
forward 1,
up 7,
forward 6,
up 2,
forward 1,
down 8,
down 2,
forward 3,
down 3,
down 2,
up 9,
down 3,
down 4,
down 3,
forward 9,
down 6,
forward 8,
forward 8,
down 1,
forward 8,
down 5,
up 9,
up 5,
up 5,
forward 5,
forward 4,
down 7,
down 6,
forward 9,
up 4,
forward 7,
up 5,
forward 7,
down 5,
down 3,
forward 5,
down 8,
up 3,
forward 4,
up 2,
down 1,
down 6,
down 6,
up 3,
forward 5,
forward 8,
down 2,
forward 6,
down 5,
down 4,
forward 9,
down 6,
forward 6,
up 5,
forward 4,
forward 5,
forward 1,
up 6,
up 2,
down 8,
up 4,
up 2,
down 3,
forward 4,
down 5,
forward 8,
up 5,
forward 6,
forward 9,
down 6,
down 3,
up 3,
down 2,
up 9,
forward 5,
up 5,
forward 3,
forward 2,
down 5,
up 2,
down 5,
forward 8,
forward 2,
down 1,
up 2,
down 6,
up 8,
down 3,
down 2,
forward 2,
down 1,
forward 8,
forward 2,
up 6,
forward 6,
up 3,
up 8,
up 2,
up 4,
down 7,
forward 6,
down 3,
down 2,
forward 5,
down 7,
down 6,
forward 1,
down 4,
forward 4,
up 1,
down 3,
up 3,
down 4,
forward 1,
down 2,
forward 6,
down 7,
forward 3,
forward 1,
forward 5,
down 7,
down 9,
forward 7,
forward 2,
forward 7,
forward 8,
down 1,
down 1,
up 6,
forward 2,
up 7,
down 9,
up 4,
up 9,
forward 9,
forward 6,
down 3,
down 9,
forward 1,
forward 1,
up 8,
forward 6,
forward 1,
forward 9,
down 2,
down 1,
forward 2,
forward 9,
down 9,
down 6,
forward 5,
down 6,
forward 4,
down 3,
forward 1,
down 4,
up 5,
forward 6,
forward 3,
down 2,
up 3,
down 9,
down 2,
forward 1,
down 4,
up 2,
down 6,
forward 6,
forward 7,
forward 3,
forward 9,
up 7,
up 2,
forward 2,
up 2,
forward 1,
up 2,
forward 8,
forward 5,
down 6,
up 7,
down 4,
down 1,
up 8,
forward 1,
down 3,
up 8,
forward 8,
down 6,
down 1,
down 6,
forward 1,
forward 7,
up 3,
forward 6,
forward 1,
up 3,
down 5,
down 1,
forward 5,
down 5,
up 7,
up 3,
down 6,
forward 6,
up 7,
forward 5,
forward 2,
forward 1,
down 8,
forward 3,
down 3,
forward 5,
down 4,
up 4,
down 8,
down 7,
down 7,
up 9,
up 2,
down 4,
down 1,
down 4,
forward 9,
up 8,
up 4,
down 2,
forward 8,
forward 1,
down 2,
up 5,
down 3,
down 8,
down 8,
down 6,
down 5,
forward 7,
down 3,
forward 5,
down 6,
down 9,
down 2,
forward 8,
down 4,
up 2,
forward 4,
down 8,
down 5,
down 4,
forward 2,
up 3,
forward 4,
up 3,
down 8,
down 2,
up 8,
forward 4,
forward 6,
down 3,
forward 9,
forward 6,
forward 8,
forward 5,
forward 1,
forward 5,
down 3,
up 2,
forward 4,
down 4,
down 3,
forward 1,
forward 3,
forward 7,
forward 9,
down 2,
up 4,
down 3,
up 8,
forward 9,
down 5,
up 9,
down 1,
up 4,
forward 7,
forward 2,
forward 4,
up 8,
down 4,
down 1,
forward 8,
down 4,
down 7,
up 1,
down 3,
down 2,
forward 5,
up 6,
down 7,
forward 2
]"

value "5 * 10000000::nat"

value "hd data"

value "position_after_course_aim data"

end