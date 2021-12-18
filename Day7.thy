theory Day7

imports Main

begin

definition "ps_ex = [16,1,2,0,4,2,7,1,2,14]"

definition "s1 = {1,2,3}"
definition "s2 = {2,3,4::nat}"

record pos_align_dist =
  pos :: int
  dist :: int

definition dist_for :: "int \<Rightarrow> int list \<Rightarrow> int" where
"dist_for p ps = foldl (+) 0 (map (\<lambda>(p1, p2). abs (p2 - p1)) (List.product [p] ps))"

value "dist_for 2 [1,2]"

value "map (\<lambda>p. \<lparr> pos = p, dist = (dist_for p ps) \<rparr>) ps"

fun all_dist :: "int list \<Rightarrow> int" where
"all_dist ps = map (\<lambda>p. \<lparr> pos = p, dist = (dist_for p ps) \<rparr>
  (* (let pos_and_align_dists = ) ps in pos_and_align_dists) *)

value "List.product [1,2,3::nat] [2,3,4::nat]"
end