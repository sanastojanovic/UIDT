theory GeoCongruence
  imports Main GeoOrder Geo
begin


section \<open>Axioms of Congruence\<close>

locale GeometryCongruence = GeometryOrder +
    fixes cng :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (* Given points a b c d, if [a, b] is congruent to [c, d] then \<open>cng a b c d\<close>.*)
  assumes ax_cng_1: "\<And> a b c. cng a a b c \<Longrightarrow> b = c"
      and ax_cng_2: "\<And> a b. cng a b b a"
      and ax_cng_3: "\<And> a b c d e f. \<lbrakk>cng a b c d; cng a b e f\<rbrakk> \<Longrightarrow> cng c d e f"
      and ax_cng_4: "\<And> a b a' b' c c'. 
                        \<lbrakk>c \<in> segment_oo a b; c' \<in> segment_oo a' b'; 
                         cng a c a' c'; cng b c b' c'\<rbrakk> \<Longrightarrow> cng a b a' b'"
      and ax_cng_5: "\<And> a b c c'. \<lbrakk>a \<noteq> b; c \<noteq> c'\<rbrakk> \<Longrightarrow> (\<exists>! d \<in> half_line_o c c'. cng a b c d)"      
      and ax_cng_6: "\<And> a b c a' b' d'. 
                        \<lbrakk>a' \<noteq> b'; a' \<noteq> d'; b' \<noteq> d'; \<not> colinear a b c; cng a b a' b'\<rbrakk> 
                    \<Longrightarrow> (\<exists>! c' \<in> half_plane_o (line a' b') d'. cng a c a' c' \<and> cng b c b' c')"
      and ax_cng_7: "\<And> a b c a' b' c' d d'. 
                        \<lbrakk>d \<in> half_line_o b c; d' \<in> half_line_o b' c'; 
                         b \<noteq> c; b' \<noteq> c'; 
                         \<not> colinear a b c; \<not> colinear a' b' c';
                         cng a b a' b'; cng b c b' c'; cng c a c' a'; cng b d b' d'\<rbrakk> \<Longrightarrow> cng a d a' d'"
begin


(* mi16069_Svetozar_Ikovic_FORMULACIJA *)
(* theorem t10_1 *)
theorem cng_refl:
  shows "cng a b a b"
  sorry


(* mi16069_Svetozar_Ikovic_FORMULACIJA *)
(* theorem t10_1 *)
theorem cng_sym:
  assumes "cng a b c d"
  shows "cng c d a b"
  sorry


(* mi16069_Svetozar_Ikovic_FORMULACIJA *)
(* theorem t10_1 *)
theorem cng_trans:
  assumes "cng a b c d" "cng c d e f"
  shows "cng a b e f"
  sorry


(* mi16069_Svetozar_Ikovic_FORMULACIJA *)
theorem t10_2:
  assumes "p \<in> half_line_os_origin c" "a \<noteq> b"
  shows "\<exists>! d. inc_p_l d p \<and> cng a b c d"
  sorry


(* mi16069_Svetozar_Ikovic_FORMULACIJA *)
theorem t10_3:
  assumes
    "a \<noteq> b" "b \<noteq> c" "c \<noteq> a"
    "inc_p_l a l" "inc_p_l b l" "inc_p_l c l"
    "inc_p_l a' l'" "inc_p_l b' l'"
    "cng a b a' b'"
  shows "\<exists>! c'.
    cng a c a' c'
\<and>   cng b c b' c'
\<and>   inc_p_l c' l'
\<and>   (bet a b c \<longrightarrow> bet a' b' c')
\<and>   (bet b c a \<longrightarrow> bet b' c' a')
\<and>   (bet c a b \<longrightarrow> bet c' a' b')
"
  sorry


(* mi16069_Svetozar_Ikovic_FORMULACIJA *)
definition cng_n :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "cng_n a b \<equiv>
  (length a = length b) \<and> (
    \<forall> i < length a. \<forall> j < i.
    cng (a ! i) (a ! j) (b ! i) (b ! j)
  )
"


(* mi16069_Svetozar_Ikovic_FORMULACIJA *)
definition cng_3 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "cng_3 a1 a2 a3 a1' a2' a3' \<equiv> cng_n [a1, a2, a3] [a1', a2', a3']"


(* mi16069_Svetozar_Ikovic_FORMULACIJA *)
definition cng_4 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "cng_4 a1 a2 a3 a4 a1' a2' a3' a4' \<equiv> cng_n [a1, a2, a3, a4] [a1', a2', a3', a4']"


(* mi16069_Svetozar_Ikovic_FORMULACIJA *)
lemma cng_n_cng_3:
  "cng_n [a, b, c] [a', b', c'] = cng a b a' b' \<and> cng a c a' c' \<and>  cng b c b' c'"
  sorry


(* mi16087_Mihajlo_Zivkovic_FORMULACIJA *)
theorem t10_4:
  assumes "\<not> colinear a b c"
    and "inc_p_pl a \<pi>" and "inc_p_pl b \<pi>" and "inc_p_pl c \<pi>"
    and "cng_3 a b c a' b' c'"
    and "inc_p_pl a' \<pi>'" and "inc_p_pl b' \<pi>'" and "inc_p_pl c' \<pi>'"
    and "inc_p_pl x \<pi>"
  shows "\<exists>! x'. inc_p_pl x' \<pi>'
        \<and> cng_4 a b c x a' b' c' x'
        \<and> ((same_side_l (line a b) x c \<and> same_side_l (line b c) x a \<and> same_side_l (line c a) x b) 
                        \<longleftrightarrow> (same_side_l (line a' b') x' c' \<and> same_side_l (line b' c') x' a' \<and> same_side_l (line c' a') x' b'))"
  sorry


(* mi16087_Mihajlo_Zivkovic_FORMULACIJA *)
theorem t10_5:
  assumes "\<not> coplanar a b c d"
    and "cng_4 a b c d a' b' c' d'"
  shows "\<exists>! x'.  cng_n [a, b, c, d, x] [a', b', c', d', x']
        \<and> ((same_side_pl (plane a b c) x d \<and> same_side_pl (plane b c d) x a \<and> same_side_pl (plane c d a) x b \<and> same_side_pl (plane d a b) x c) 
                        \<longleftrightarrow> (same_side_pl (plane a' b' c') x' d' \<and> same_side_pl (plane b' c' d') x' a' \<and> same_side_pl (plane c' d' a') x' b' \<and> same_side_pl (plane d' a' b') x' c'))"
  sorry

(* mi16087_Mihajlo_Zivkovic_FORMULACIJA *)
definition isometry_line :: "('a => 'a) => 'b => bool" where
"isometry_line f l \<equiv> bij f \<and> (\<forall> a b.  inc_p_l a l \<and> inc_p_l b l \<and> cng a b (f a) (f b))"

(* mi16087_Mihajlo_Zivkovic_FORMULACIJA *)
definition isometry_plane :: "('a => 'a) => 'c \<Rightarrow> bool" where
"isometry_plane f p \<equiv> bij f \<and> (\<forall> a b. inc_p_pl a p \<and> inc_p_pl b p \<and> cng a b (f a) (f b))"

(* mi16087_Mihajlo_Zivkovic_FORMULACIJA *)
definition isometry_space :: "('a => 'a) \<Rightarrow> 'a set => bool" where
"isometry_space f s \<equiv> bij f \<and> (\<forall> a \<in> s. \<forall> b \<in> s. cng a b (f a) (f b))"


(* mi20350_Stefan_Mitrovic_FORMULACIJA *)
definition invariant_figure :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "invariant_figure f S \<equiv> (isometry_space f S) \<and> (f` S = S)"

(* mi20350_Stefan_Mitrovic_FORMULACIJA *)
theorem t10_6_line:
  assumes "isometry_line f l" "isometry_line g l" "isometry_line h l"
  shows "isometry_line (f \<circ> g) l"
  and "(f \<circ> g) \<circ> h = f \<circ> (g \<circ> h)"
  and "isometry_line (\<lambda>x. x) l"
  and "(\<exists>g. isometry_line g l \<and> (f \<circ> g = (\<lambda>x. x)) \<and> (g \<circ> f = (\<lambda>x. x)))"
  sorry

(* mi20350_Stefan_Mitrovic_FORMULACIJA *)
theorem t10_6_plane:
  assumes "isometry_plane f p" "isometry_plane g p" "isometry_plane h p"
  shows "isometry_plane (f \<circ> g) p"
  and "(f \<circ> g) \<circ> h = f \<circ> (g \<circ> h)"
  and "isometry_plane (\<lambda>x. x) p"
  and "(\<exists>g. isometry_plane g p \<and> (f \<circ> g = (\<lambda>x. x)) \<and> (g \<circ> f = (\<lambda>x. x)))"
  sorry

(* mi20350_Stefan_Mitrovic_FORMULACIJA *)
theorem t10_6_space:
  assumes "isometry_space f s" "isometry_space g s" "isometry_space h s"
  shows "isometry_space (f \<circ> g) s"
  and "(f \<circ> g) \<circ> h = f \<circ> (g \<circ> h)"
  and "isometry_space (\<lambda>x. x) s"
  and "(\<exists>g. isometry_space g s \<and> (f \<circ> g = (\<lambda>x. x)) \<and> (g \<circ> f = (\<lambda>x. x)))"
  sorry

(*
(*mi19218_Luka_Bura_FORMULACIJA *)
definition image_of_line :: "('a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'a set" where
  "image_of_line f l = {b. \<forall> a \<in> line_points l. f a = b}"

(*mi19218_Luka_Bura_FORMULACIJA *)
theorem t10_7a:
  assumes "isometry_line J l" "inc_p_l a l"
  shows "inc_p_l (J a) (J l)"
  sorry

(*mi19218_Luka_Bura_FORMULACIJA *)
definition image_of_half_line_o :: "('a => 'a) => ('a => bool) => ('a => bool)" where
"image_of_half_line_o f hl a = (\<exists> b. hl b \<and> f b = a)"

(*mi19218_Luka_Bura_FORMULACIJA *)
theorem t10_7b: 
  assumes "isometry_line J I"
    and "origin \<in> I" and "half_line_os_origin origin = hl"
  shows "\<forall> P. P \<in> hl \<longrightarrow> J(P) \<in> Collect (image_of_half_line_o J (\<lambda>x. x \<in> hl)) \<and> J(origin) = origin"
  sorry

(*mi19218_Luka_Bura_FORMULACIJA *)
definition image_of_segment :: "('a => 'a) => ('a => bool) => ('a => bool)" where
"image_of_segment f seg a = (\<exists> b. seg b \<and> f b = a)"

(*mi19218_Luka_Bura_FORMULACIJA *)
theorem t10_7c: 
  assumes "isometry_line J I"
    and "inc_p_l A I" and "inc_p_l B I"
    and "segment A B = seg"
  shows "\<forall> P. P \<in> seg \<longrightarrow> J(P) \<in> Collect (image_of_segment J (\<lambda>x. x \<in> seg)) \<and> J(A) = A' \<and> J(B) = B'"
  sorry

(*mi19218_Luka_Bura_FORMULACIJA *)
definition image_of_plane :: "('a => 'a) => ('a => bool) => ('a => bool)" where
"image_of_plane f \<pi> a = (\<exists> b. \<pi> b \<and> f b = a)"

(*mi19218_Luka_Bura_FORMULACIJA *)
theorem t10_8a:
  assumes "isometry_plane J \<pi>"
  shows "\<forall> P. inc_p_pl P \<pi> \<longrightarrow> inc_p_pl (J P) (image_of_plane J \<pi>)"
  sorry

(*mi19218_Luka_Bura_FORMULACIJA *)
definition image_of_half_plane :: "('a => 'a) => ('a => bool) => ('a => bool)" where
"image_of_half_plane f hp a = (\<exists> b. hp b \<and> f b = a)"

(*mi19218_Luka_Bura_FORMULACIJA *)
theorem t10_8b:
  assumes "isometry_plane J \<pi>"
    and "s \<subseteq> \<pi>" and "half_plane_with_boundary s = hp"
  shows "\<forall> P. P \<in> hp \<longrightarrow> J(P) \<in> Collect (image_of_half_plane J (\<lambda>x. x \<in> hp)) \<and> edge_of_half_plane J(s) = J(s)"
  sorry


*)

(*mi19113_Djordje_Petrovic_FORMULACIJA*)
theorem t10_9a:
  assumes "isometry_line J l"
    and "inc_p_l a l \<and> inc_p_l b l" 
    and "inc_p_l a' l \<and> inc_p_l b' l"
    and "same_direction (a, b) (a', b')"
 shows "same_direction (J a, J b) (J a', J b')"
  sorry

(*mi19113_Djordje_Petrovic_FORMULACIJA*)
theorem t10_9b:
  assumes "isometry_line J l"
    and "inc_p_l a l \<and> inc_p_l b l" 
    and "inc_p_l a' l \<and> inc_p_l b' l"
    and "opposite_direction (a, b) (a', b')"
 shows "opposite_direction (J a, J b) (J a', J b')"
  sorry

(*mi19113_Djordje_Petrovic_FORMULACIJA*)
theorem t10_10a:
  assumes "isometry_plane J \<pi>"
  and "inc_p_pl a \<pi> \<and> inc_p_pl b \<pi> \<and> inc_p_pl c \<pi>"
  and "inc_p_pl a' \<pi> \<and> inc_p_pl b' \<pi> \<and> inc_p_pl c' \<pi>"
  and "same_direction_triangle (a, b, c) (a', b', c')"  
  shows "same_direction_triangle (J a, J b, J c) (J a', J b', J c')"
  sorry

(*mi19113_Djordje_Petrovic_FORMULACIJA*)
theorem t10_10b:
  assumes "isometry_plane J \<pi>"
  and "inc_p_pl a \<pi> \<and> inc_p_pl b \<pi> \<and> inc_p_pl c \<pi>"
  and "inc_p_pl a' \<pi> \<and> inc_p_pl b' \<pi> \<and> inc_p_pl c' \<pi>"
  and "opposite_direction_triangle (a, b, c) (a', b', c')"  
  shows "opposite_direction_triangle (J a, J b, J c) (J a', J b', J c')"
  sorry


(*mi19113_Djordje_Petrovic_FORMULACIJA*)
theorem t10_11a:
  assumes "isometry_space J S"
  and "a \<in> S \<and> b \<in> S \<and> c \<in> S \<and> d \<in> S \<and> a' \<in> S \<and> b' \<in> S \<and> c' \<in> S \<and> d' \<in> S"
  and "same_direction_tetrahedron (a, b, c, d) (a', b', c', d')"
  shows "same_direction_tetrahedron (J a, J b, J c, J d) (J a', J b', J c', J d')"
  sorry

(*mi19113_Djordje_Petrovic_FORMULACIJA*)
theorem t10_11b:
  assumes "isometry_space J S"
  and "a \<in> S \<and> b \<in> S \<and> c \<in> S \<and> d \<in> S \<and> a' \<in> S \<and> b' \<in> S \<and> c' \<in> S \<and> d' \<in> S"
  and "opposite_direction_tetrahedron (a, b, c, d) (a', b', c', d')"
  shows "opposite_direction_tetrahedron (J a, J b, J c, J d) (J a', J b', J c', J d')"
  sorry


(*mi19113_Djordje_Petrovic_FORMULACIJA*)
theorem t10_12:
  assumes "a \<noteq> b \<and> inc_p_l a p \<and> inc_p_l a p"
    and "inc_p_l a' p \<and> inc_p_l a p \<and> cng a b a' b'"
  shows "\<exists>! J. isometry_line J p \<and> J a = a' \<and> J b = b'"
  sorry


(*mi19113_Djordje_Petrovic_FORMULACIJA*)
theorem t10_13:
  assumes "\<not> colinear a b c \<and> inc_p_pl a \<pi> \<and> inc_p_pl b \<pi> \<and> inc_p_pl c \<pi>"
    and "inc_p_pl a' \<pi> \<and> inc_p_pl b' \<pi> \<and> inc_p_pl c' \<pi> \<and> cng_3 a b c a' b' c'"
  shows "\<exists>! J. isometry_plane J \<pi> \<and>  J a = a' \<and> J b = b' \<and> J c = c'"
  sorry


(*mi17060_Aleksandar_Milosevic_FORMULACIJA*)
theorem t10_14:
  assumes "\<not>coplanar a b c d "
    and "a' \<in> S \<and> b' \<in> S \<and> c' \<in> S \<and> d' \<in> S 
    \<and> a \<in> S \<and> b \<in> S \<and> c \<in> S \<and> d \<in> S \<and> cng_4 a b c d a' b' c' d'"
  shows "\<exists>! I. isometry_space I S \<and> I a = a' \<and> I b = b' \<and> I c = c' \<and> I d = d'"
  sorry

(* mi17060_Aleksandar_Milosevic_FORMULACIJA*)
definition cng_figure :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "cng_figure fig1 fig2 \<longleftrightarrow> (\<exists>f. isometry_space f fig1 \<and> (\<forall>a. a \<in> fig1 \<longrightarrow> f a \<in> fig2))"


(*mi17060_Aleksandar_Milosevic_FORMULACIJA*)
(* theorem t10_15 *)
theorem cng_figure_refl:
  shows "cng_figure fig fig"
  sorry

(*mi17060_Aleksandar_Milosevic_FORMULACIJA*)
(* theorem t10_15 *)
theorem cng_figure_sym:
  assumes "cng_figure fig1 fig2"
  shows "cng_figure fig2 fig1"
  sorry

(*mi17060_Aleksandar_Milosevic_FORMULACIJA*)
(* theorem t10_15 *)
theorem cng_figure_trans:
  assumes "cng_figure fig1 fig2" "cng_figure fig2 fig3"
  shows "cng_figure fig1 fig3"
  sorry


(* mi17060_Aleksandar_Milosevic_FORMULACIJA*)
definition cng_segment :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "cng_segment a b c d \<longleftrightarrow> cng a b c d"

(* mi17060_Aleksandar_Milosevic_FORMULACIJA*)
definition midpoint :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "midpoint a b s \<longleftrightarrow> cng a s s b \<and> bet a s b"



(* mi18059_Luka_Radenkovic_FORMULACIJA *)
definition midpoint :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"midpoint A B S \<longleftrightarrow> bet A S B \<and> cng A S S B"

(* mi18059_Luka_Radenkovic_FORMULACIJA *)
theorem t11_1:
  assumes "A \<noteq> B"
  shows "\<exists>! S. midpoint A B S"
  sorry

(* mi18059_Luka_Radenkovic_FORMULACIJA *)
definition less_than :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"less_than A B C D \<longleftrightarrow> (\<exists> E. bet C E D \<and> cng A B C E)"

(* mi18059_Luka_Radenkovic_FORMULACIJA *)
definition greater_than :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"greater_than A B C D \<longleftrightarrow> less_than C D A B"

(* mi18059_Luka_Radenkovic_FORMULACIJA *)
definition less_than_or_equal :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"less_than_or_equal A B C D \<longleftrightarrow> \<not> greater_than A B C D"

(* mi18059_Luka_Radenkovic_FORMULACIJA *)
definition greater_than_or_equal :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"greater_than_or_equal A B C D \<longleftrightarrow> \<not> less_than A B C D"


(* mi18172_Radovan_Bozic_FORMULACIJA *)
theorem t11_2ref:
  assumes "less_than a b c d"
  shows "less_than a b a b \<and> less_than c d c d"
  sorry

(* mi18172_Radovan_Bozic_FORMULACIJA *)
theorem t11_2anti:
  assumes "less_than a b  c d" "less_than c d  a b"
  shows "a = a \<and> b = b \<and> c = c \<and> d = d"
  sorry

(* mi18172_Radovan_Bozic_FORMULACIJA *)
theorem t11_2tran:
  assumes "less_than a b  c d" "less_than c d e f"
  shows "less_than a b  e f"
  sorry

(* mi18172_Radovan_Bozic_FORMULACIJA *)
theorem t11_2d:
  shows "cng a b c d \<or> less_than a b c d \<or> greater_than a b c d"
  sorry

(* mi18172_Radovan_Bozic_FORMULACIJA *)
primrec colinear_dots :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "colinear_dots A B [] = True"
| "colinear_dots A B (x # xs) \<longleftrightarrow> (colinear A B x) \<and> (colinear_dots A B xs)"

(* mi18172_Radovan_Bozic_FORMULACIJA *)
fun cng_dots :: "('a \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "cng_dots [] [] = True"
| "cng_dots  ((a, b) # dots) (x # y # xs) \<longleftrightarrow> (cng a b x y) \<and> (cng_dots dots (y # xs))"

(* mi18172_Radovan_Bozic_FORMULACIJA *)
definition sum_of_lines :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) list  \<Rightarrow> bool" where
  "sum_of_lines A B dots \<longleftrightarrow> (\<exists> xs. distinct xs 
                                \<and> (length xs = length dots - 1)
                                \<and> (colinear_dots A B xs)
                                \<and> (cng_dots dots ((A # xs) @ [B]))
                             )"

(* mi18172_Radovan_Bozic_FORMULACIJA *)
definition two_lines_sub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "two_lines_sub a b a1 b1 a2 b2 = (if greater_than a b a1 b1 then 
        sum_of_lines a b [(a1, b1), (a2, b2)] else sum_of_lines a1 b1 [(a, b), (a2, b2)] )"

(* mi18172_Radovan_Bozic_FORMULACIJA *)
definition null_line :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "null_line a b = (a = b)"

(*
(* mi18172_Radovan_Bozic_FORMULACIJA *)
theorem t11_3a:
  assumes "is_angle p oo q"
  assumes "\<not>convex {oo, p, q}"
  assumes "is_angle p' oo' q'"
  assumes "\<not>convex {oo', p', q'}"
  shows "cng (oo p q) (o' p' q') \<longleftrightarrow> (cng oo p oo' p') \<and> (cng oo q oo' q') \<and> (cng p q p' q')"
  sorry

(* mi18172_Radovan_Bozic_FORMULACIJA *)
theorem t11_3a:
  assumes "is_angle p oo q"
  assumes "convex {oo, p, q}"
  assumes "is_angle p' oo' q'"
  assumes "convex {oo', p', q'}"
  shows "cng (oo p q) (o' p' q') \<longleftrightarrow> (cng oo p oo' p') \<and> (cng oo q oo' q') \<and> (cng p q p' q')"
  sorry
*)



end

end