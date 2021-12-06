theory Day5

imports Main

begin

record segment =
  x0 :: nat
  y0 :: nat
  x1 :: nat
  y1 :: nat

record range =
  start :: nat
  end' :: nat

record point = 
  x :: nat
  y :: nat

text "
Two segments must be on the same line to have overlapping points. 
That means either all xs must be equal, or all ys must be equal. Distinguishing
between horizontal and vertical lines is also helpful to that we know which
values to access off of the segment, i.e. xs vs. ys"
definition on_same_line_horiz :: "segment \<Rightarrow> segment \<Rightarrow> bool" where
"on_same_line_horiz s1 s2 = (y0 s1 = y0 s2 \<and> y1 s1 = y1 s2 \<and> y0 s1 = y0 s2)"

definition on_same_line_vert :: "segment \<Rightarrow> segment \<Rightarrow> bool" where
"on_same_line_vert s1 s2 = (x0 s1 = x0 s2 \<and> x1 s1 = x1 s2 \<and> x0 s1 = x0 s2)"

text"
Find the range that the two segments overlap on. If they are non-overlapping,
then the range will 
"
definition min_x :: "segment \<Rightarrow> nat" where
"min_x s = min (x0 s) (x1 s)"

definition max_x :: "segment \<Rightarrow> nat" where
"max_x s = max (x0 s) (x1 s)"

definition min_y :: "segment \<Rightarrow> nat" where
"min_y s = min (y0 s) (y1 s)"

definition max_y:: "segment \<Rightarrow> nat" where
"max_y s = max (y0 s) (y1 s)"

definition overlap_range_horiz :: "segment \<Rightarrow> segment \<Rightarrow> range option" where
"overlap_range_horiz s1 s2 =
  (let overlap = \<lparr> start = max (min_x s1) (min_x s2), end' = min (max_x s1) (max_x s2) \<rparr> in
  (if (start overlap) > (end' overlap) then None else Some(overlap)))"

definition overlap_range_vert :: "segment \<Rightarrow> segment \<Rightarrow> range option" where
"overlap_range_vert s1 s2 =
  (let overlap = \<lparr> start = max (min_y s1) (min_y s2), end' = min (max_y s1) (max_y s2) \<rparr> in
  (if (start overlap) > (end' overlap) then None else Some(overlap)))"

definition make_point :: "nat \<Rightarrow> nat \<Rightarrow> point" where
"make_point xv yv = \<lparr> x = xv, y = yv \<rparr>"

definition expand_range_horiz :: "range option \<Rightarrow> nat \<Rightarrow> point list" where
"expand_range_horiz r yv = 
  (case r of
    Some r \<Rightarrow> map (\<lambda>xv. make_point xv yv) (upt (start r) ((end' r) + 1)) |
    None \<Rightarrow> [])"

definition expand_range_vert :: "range option \<Rightarrow> nat \<Rightarrow> point list" where
"expand_range_vert r xv = 
  (case r of
    Some r \<Rightarrow> map (\<lambda>yv. make_point xv yv) (upt (start r) ((end' r) + 1)) |
    None \<Rightarrow> [])"

definition vert :: "segment \<Rightarrow> bool" where
"vert s = (x0 s = x1 s)"

(* 2,2 \<rightarrow> 2,1 | 3,4 \<rightarrow> 1,4 *)
(* 9,4 \<rightarrow> 3,4 | 7,0 \<rightarrow> 7,4 *)
(*
8,0 \<rightarrow> 0,8 | 9,4 \<rightarrow> 3,4*)
definition are_orthogonal :: "segment \<Rightarrow> segment \<Rightarrow> bool" where
"are_orthogonal s1 s2 = 
  ((min_x s1 \<ge> min_x s2 \<and> max_x s1 \<le> max_x s2 \<and> min_y s1 \<ge> min_y s2 \<and> max_y s1 \<le> max_y s2)
  \<or> ((min_x s2 \<ge> min_x s1 \<and> max_x s2 \<le> max_x s1 \<and> min_y s2 \<ge> min_y s1 \<and> max_y s2 \<le> max_y s1)))"

definition overlapping_points :: "segment \<Rightarrow> segment \<Rightarrow> point list" where
"overlapping_points s1 s2 =
  (if s1 = s2 then
    []
  else if on_same_line_horiz s1 s2 then 
    expand_range_horiz (overlap_range_horiz s1 s2) (y0 s1)
  else if on_same_line_vert s1 s2 then
    expand_range_vert (overlap_range_vert s1 s2) (x0 s1)
  else if are_orthogonal s1 s2 then
    if vert s1 then [\<lparr> x = x0 s1, y = y0 s2 \<rparr>] else [\<lparr> x = x0 s2, y = y0 s1 \<rparr>]
  else
    [])"

type_synonym overlap_count_alist = "(point * nat) list"

text "This is an attempt at counting the overlapping points with a function.
The problem with this approach is that nat cannot be enumerated (it represents an
infinite amount of numbers) so it's difficult to pull the points that have been
'populated' in the function via set comprehensions."

type_synonym overlaps = "point set"

definition count_overlaps :: "point list \<Rightarrow> overlaps \<Rightarrow> overlaps" where
"count_overlaps ps oci = foldl (\<lambda>oc p. insert p oc) oci ps"

definition all_overlaps_with_seg :: "segment \<Rightarrow> segment list \<Rightarrow> overlaps \<Rightarrow> overlaps" where
"all_overlaps_with_seg s sl oci = foldl (\<lambda>oc s'. count_overlaps (overlapping_points s s') oc) oci sl"

definition all_overlaps :: "segment list \<Rightarrow> overlaps" where
"all_overlaps sl = foldl (\<lambda>os s. all_overlaps_with_seg s sl os) {} sl"

definition "small_data \<equiv> [
  \<lparr> x0 = 0, y0 = 9, x1 = 5, y1 = 9 \<rparr>,
  \<lparr> x0 = 8, y0 = 0, x1 = 0, y1 = 8 \<rparr>,
  \<lparr> x0 = 9, y0 = 4, x1 = 3, y1 = 4 \<rparr>,
  \<lparr> x0 = 2, y0 = 2, x1 = 2, y1 = 1 \<rparr>,
  \<lparr> x0 = 7, y0 = 0, x1 = 7, y1 = 4 \<rparr>,

  \<lparr> x0 = 6, y0 = 4, x1 = 2, y1 = 0 \<rparr>,
  \<lparr> x0 = 0, y0 = 9, x1 = 2, y1 = 9 \<rparr>,
  \<lparr> x0 = 3, y0 = 4, x1 = 1, y1 = 4 \<rparr>,
  \<lparr> x0 = 0, y0 = 0, x1 = 8, y1 = 8 \<rparr>,
  \<lparr> x0 = 5, y0 = 5, x1 = 8, y1 = 2 \<rparr>
]"

definition horiz_or_vert :: "segment \<Rightarrow> bool" where
"horiz_or_vert s = (x0 s = x1 s \<or> y0 s = y1 s)"

definition "h_or_v_segments \<equiv> filter horiz_or_vert small_data"
value "h_or_v_segments"

definition "line1 \<equiv> \<lparr> x0 = 0, y0 = 9, x1 = 5, y1 = 9 \<rparr>"
definition "line2 \<equiv> \<lparr> x0 = 0, y0 = 9, x1 = 2, y1 = 9 \<rparr>"

definition "line1h = \<lparr> x0 = 9, y0 = 4, x1 = 3, y1 = 4 \<rparr>"
definition "line2h = \<lparr> x0 = 3, y0 = 4, x1 = 1, y1 = 4 \<rparr>"

definition "hline = \<lparr> x0 = 9, y0 = 4, x1 = 3, y1 = 4 \<rparr>"
definition" hline2 = \<lparr> x0 = 7, y0 = 0, x1 = 7, y1 = 4 \<rparr>"

definition "lineb = \<lparr> x0 = 2, y0 = 2, x1 = 2, y1 = 1 \<rparr>"
definition "linei = \<lparr> x0 = 3, y0 = 4, x1 = 1, y1 = 4 \<rparr>"

definition "diag1 = \<lparr> x0 = 8, y0 = 0, x1 = 0, y1 = 8 \<rparr>"
definition "diag2 = \<lparr> x0 = 9, y0 = 4, x1 = 3, y1 = 4 \<rparr>"

value "card {1,2::nat}"
value "upt 0 2"
value "on_same_line_horiz line1 line2"
value "overlap_range_horiz line1 line2"
value "expand_range_horiz (overlap_range_horiz line1 line2) 9"
value "are_orthogonal diag1 diag2"
value "overlapping_points lineb linei"
value "overlap_range_horiz lineb linei"
value "all_overlaps small_data"
value "all_overlaps h_or_v_segments"
value "count_overlaps (overlapping_points line2 line1) {}"
value "all_overlaps_with_seg  \<lparr> x0 = 3, y0 = 4, x1 = 1, y1 = 4 \<rparr> h_or_v_segments {}"

value "drop 2 [1,2,3::nat]"

value "length data"

value "card (all_overlaps data)"

end