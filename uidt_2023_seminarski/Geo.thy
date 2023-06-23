theory Geo
  imports Main

begin

typedecl point
typedecl line
typedecl plane

locale Geo = 
  fixes inc_p_l :: "point \<Rightarrow> line \<Rightarrow> bool" (* Given point a and line l, if a is incident to l then inc_p_l a l*)
    and inc_p_pl :: "point \<Rightarrow> plane \<Rightarrow> bool" (* Given point a and plane P, if a is incident to P then inc_p_pl a P*)
    and inc_l_pl :: "line \<Rightarrow> plane \<Rightarrow> bool" (* Given line l and plane P, if l is incident to P then inc_l_pl l P *)
begin

(* If points a, b, and c are incident to some line l, then \<open>colinear a b c\<close>. *)
definition colinear :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "colinear a b c \<equiv> \<exists> l :: line. inc_p_l a l \<and> inc_p_l b l \<and> inc_p_l c l"

(* If points a, b, c, and d are incident to some plane P, then \<open>coplanar a b c d\<close>. *)
definition coplanar :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "coplanar a b c d \<equiv> \<exists> P :: plane. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P \<and> inc_p_pl d P"

end

section \<open>Axioms of Incidence\<close>

locale GeometryIncidence = Geo +
  assumes ax_inc_1: "\<forall> l :: line. \<exists> a b :: point. a \<noteq> b \<and> inc_p_l a l \<and> inc_p_l b l" 
      and ax_inc_2: "\<forall> a b :: point. \<exists> l :: line. inc_p_l a l \<and> inc_p_l b l"
      and ax_inc_3: "\<forall> a b :: point. \<forall> l l' :: line. a \<noteq> b \<and> inc_p_l a l \<and> inc_p_l b l \<and> inc_p_l a l' \<and> inc_p_l b l' \<longrightarrow> l = l'"
      and ax_inc_4: "\<forall> P :: plane. \<exists> a b c :: point. \<not> colinear a b c \<and> inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P"
      and ax_inc_5: "\<forall> a b c :: point. \<exists> P :: plane. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P"
      and ax_inc_6: "\<forall> a b c :: point. \<forall> P P' :: plane. \<not> colinear a b c \<and> inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P \<and> inc_p_pl a P' \<and> inc_p_pl b P' \<and> inc_p_pl c P' \<longrightarrow> P = P'"
      and ax_inc_7: "\<forall> l :: line. \<forall> P :: plane. \<exists> a b :: point. a \<noteq> b \<and> inc_p_l a l \<and> inc_p_l b l \<and> inc_p_pl a P \<and> inc_p_pl b P \<and> inc_l_pl l P"
      and ax_inc_8: "\<forall> P Q :: plane. \<forall> a :: point. inc_p_pl a P \<and> inc_p_pl a Q \<longrightarrow> (\<exists> b :: point. a \<noteq> b \<and> inc_p_pl b P \<and> inc_p_pl b Q)"
      and ax_inc_9: "\<exists> a b c d :: point. \<not> coplanar a b c d"
begin

subsection \<open>Three Non-Collinear Points and Four Non-Coplanar Points\<close>

subsection \<open>Lines and Planes\<close>

(* \<open>line a b\<close> is line that is defined by two points a and b. (Use under assumption: a \<noteq> b!) *)
definition line :: "point \<Rightarrow> point \<Rightarrow> line" where
  "line a b \<equiv> THE l :: line. inc_p_l a l \<and> inc_p_l b l"

(* \<open>plane a b c\<close> is plane that is defined by three points a, b, and c. (Use under assumption: a \<noteq> b \<and> b \<noteq> c \<and> c \<noteq> a!) *)
definition plane :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> plane" where
  "plane a b c \<equiv> THE P :: plane. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P"

(* \<open>points_on_line\<close> is set of all points that are incident to line l. *)
definition points_on_line :: "line \<Rightarrow> point set" where
  "points_on_line l = {a. inc_p_l a l}"

subsection \<open>Fundamental Existence Theorems\<close>


(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_1:
  fixes a b c :: point
  assumes "\<not> (colinear a b c)"
  shows "distinct [a, b, c]"
  sorry

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_2:
  fixes a b c d :: point
  assumes "\<not> (coplanar a b c d)"
  shows "distinct [a, b, c, d]"
  sorry

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_3:
  fixes a b c d :: point
  assumes "\<not> (coplanar a b c d)"
  shows "\<not> (colinear a b c) \<and> \<not> (colinear a b d) \<and> \<not> (colinear a c d) \<and> \<not> (colinear b c d)"
  sorry

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_4_a:
  shows "\<exists> a b c d :: point. distinct [a, b, c, d]"
  sorry

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_4_b:
  shows "\<exists> p q r l s t :: line. distinct [p, q, r, l, s, t]"
  sorry

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_4_c:
  shows "\<exists> P Q R S :: plane. distinct [P, Q, R, S]"
  sorry

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_5:
  shows "\<exists> a b c :: point. \<not> (colinear a b c)"
  sorry

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_6:
  fixes a b :: point
  assumes "a \<noteq> b"
  shows "\<exists>! p :: line. inc_p_l a p \<and> inc_p_l b p"
  sorry


(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
theorem t1_7:
  fixes a b c :: point
  assumes "\<not> (colinear a b c)" and "a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c" 
  shows "\<exists>! P :: plane. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P"
  sorry

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
(* \<open>plane'\<close> \<rightarrow> plane that is defined by line and point that doesn't belongs to that line. (Use under assumption: \<not> (inc_p_l a p) *)
definition plane' :: "point \<Rightarrow> line \<Rightarrow> plane" where
"plane' a p \<equiv> THE P :: plane. inc_l_pl p P \<and> inc_p_pl a P"

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
theorem t1_8:
  fixes a :: point and p :: line
  assumes "\<not> (inc_p_l a p)"
  shows "\<exists>! P :: plane. inc_l_pl p P \<and> inc_p_pl a P"
  sorry

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
(* \<open>intersects\<close> \<rightarrow> do two lines have intersection. *)
definition intersects :: "line \<Rightarrow> line \<Rightarrow> bool" where
"intersects p q \<equiv> (\<exists> a :: point. inc_p_l a p \<and> inc_p_l a q)"

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
(* \<open>plane''\<close> \<rightarrow> plane that is defined by two lines that initersect. (Use under assumption: p \<noteq> q \<and> intersects p q) *)
definition plane'' :: "line \<Rightarrow> line \<Rightarrow> plane" where
"plane'' p q \<equiv> THE P :: plane. inc_l_pl p P \<and> inc_l_pl q P"

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
theorem t1_9:
  fixes p q :: line
  assumes "intersects p q" and "p \<noteq> q"
  shows "\<exists>! P :: plane. inc_l_pl p P \<and> inc_l_pl q P"
  sorry

(* mi17122_Tamara_Tomic_FORMULACIJA *)
(* \<open>passing_lines p q\<close> : passing lines are lines which are not in the same plane,  *)
definition passing_lines :: "line \<Rightarrow> line \<Rightarrow> bool" where
  "passing_lines p q \<equiv> \<not>(\<exists> P :: plane. inc_l_pl p P \<and> inc_l_pl q P)"

(* mi17122_Tamara_Tomic_FORMULACIJA *)
theorem t1_10:
  "\<exists> p q :: line. passing_lines p q"
  sorry

subsection \<open>Intersections of Lines and Planes\<close>

(* mi17122_Tamara_Tomic_FORMULACIJA *)
(* \<open>intersection p q\<close> is a point where two lines intersect (Use under assumption: p \<noteq> q) *)
definition intersection :: "line \<Rightarrow> line \<Rightarrow> point" where
  "intersection p q \<equiv> THE a :: point. inc_p_l a p \<and> inc_p_l a q"

(* mi17122_Tamara_Tomic_FORMULACIJA *)
theorem t1_11:
  fixes a b :: point and p q :: line
  assumes "p \<noteq> q" "inc_p_l a p \<and> inc_p_l a q \<and> inc_p_l b p \<and> inc_p_l b q"
  shows "a = b"
  sorry

(* mi17122_Tamara_Tomic_FORMULACIJA *)
(* \<open>point_line_plane_intersect p P\<close> point where line and plane intersect *)
definition point_line_plane_intersect :: "line \<Rightarrow> plane \<Rightarrow> point" where
  "point_line_plane_intersect p P \<equiv> THE a :: point. inc_p_l a p \<and> inc_p_pl a P"

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
theorem t1_12:
  fixes a b :: point and l :: line and P :: plane
  assumes "\<not> inc_l_pl l P" "inc_p_l a l \<and> inc_p_pl a P \<and> inc_p_l b l \<and> inc_p_pl b P"
  shows "a = b"
  sorry

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* \<open>planes_intersect_line P Q\<close> is line that is defined as intersection of planes P and Q. (Use under assumption: P \<noteq> Q and P and Q have intersection (i.e. not parallel)!) *)
definition plane_plane_intersect_line :: "plane \<Rightarrow> plane \<Rightarrow> line" where
  "plane_plane_intersect_line P Q \<equiv> THE l :: line. inc_l_pl l P \<and> inc_l_pl l Q"

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
theorem t1_13:
  fixes P Q :: plane
  assumes "P \<noteq> Q" "\<exists> a :: point. inc_p_pl a P \<and> inc_p_pl a Q"
  shows "\<exists> l :: line. \<forall> a :: point. inc_p_l a l \<longleftrightarrow> inc_p_pl a P \<and> inc_p_pl a Q"
  sorry

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* If lines in set of lines L are concurrent then \<open>concurrent_lines L\<close>. *)
definition concurrent_lines :: "line set \<Rightarrow> bool" where
  "concurrent_lines L \<equiv> \<exists> a :: point. \<forall> l \<in> L. inc_p_l a l"

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* If lines in set of lines L are coplanar then \<open>coplanar_lines L\<close>. *)
definition coplanar_lines :: "line set \<Rightarrow> bool" where
  "coplanar_lines L \<equiv> \<exists> P :: plane. \<forall> l \<in> L. inc_l_pl l P"

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
theorem t1_14:
  fixes L :: "line set"
  assumes "\<forall> l \<in> L. \<forall> k \<in> L. intersects l k"
  shows "concurrent_lines L \<or> coplanar_lines L"
  sorry

end

section \<open>Linear Axioms of Order\<close>

locale GeometryOrder = GeometryIncidence +
    fixes bet :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" (* Given points a, b, and c, if b between a and c then \<open>bet a b c\<close>.*)
  assumes ax_ord_1: "\<forall> a b c :: point. bet a b c \<longrightarrow> a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c \<and> colinear a b c"
      and ax_ord_2: "\<forall> a b c :: point. bet a b c \<longrightarrow> bet c b a"
      and ax_ord_3: "\<forall> a b c :: point. bet a b c \<longrightarrow> \<not> bet a c b"
      and ax_ord_4: "\<forall> a b :: point. a \<noteq> b \<longrightarrow> (\<exists> c :: point. bet a b c)"
      and ax_ord_5: "\<forall> a b :: point. a \<noteq> b \<longrightarrow> (\<exists> c :: point. bet a c b)"
      and ax_ord_6: "\<forall> a b c :: point. a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c \<and> colinear a b c \<longrightarrow> bet a b c \<or> bet b c a \<or> bet c a b"
     (*Pasova akosioma nedostaje*)
begin

(* \<open>open_segment a b\<close> is set of all points between a and b. *)
definition open_segment :: "point \<Rightarrow> point \<Rightarrow> point set" where
  "open_segment a b = {c. bet a c b}"

(* \<open>half_line a b\<close> is set of all points between a and b and all points c such that b is between a and c, including a and b. (Use under assumption: a \<noteq> b!*)
definition half_line :: "point \<Rightarrow> point \<Rightarrow> point set" where
  "half_line a b = {c. c = a \<or> c = b \<or> bet a c b \<or> bet a b c}"

(* \<open>half_lines_origin a\<close> is set of all half-lines with origin a. *)
definition half_lines_origin :: "point \<Rightarrow> point set set" where
  "half_lines_origin a = {p. \<forall> b :: point. p = half_line a b}"

(* Given points a and b, and line l, if l between a and b then \<open>bet_line a l b\<close>.*)
definition bet_line :: "point \<Rightarrow> line \<Rightarrow> point \<Rightarrow> bool" where
  "bet_line a l b \<equiv> \<exists> c \<in> points_on_line l. bet a c b"

(* \<open>half_plane l a\<close> is a set of all points between a and l and all points c such that a is between c and l, including points on l and a. (Use under assumption: \<not> inc_p_l a l.*)
definition half_plane :: "line \<Rightarrow> point \<Rightarrow> point set" where
  "half_plane l a = {c. \<forall> b \<in> points_on_line l. c = a \<or> c = b \<or> bet b c a \<or> bet b a c}"

(* \<open>half_planes\<close> is set of all half-planes with boundary l. *)
definition half_planes_boundary :: "line \<Rightarrow> point set set" where
  "half_planes_boundary l = {P. \<forall> a :: point. P = half_plane l a}"
  
(* mi17017 Sara_Selakovic_FORMULACIJA *)
theorem t2_4:
  fixes a b :: point
  assumes "a \<noteq> b"
  shows "bet a c b"
  sorry

(* mi17017_Sara_Selakovic_FORMULACIJA *)
(* \<open> bet4 \<close> \<longrightarrow> Given points a, b, c and d. If b and c between a and d, in the way that b between a and c, and c between b and d, then \<open> bet4 a b c d \<close> *)
definition bet4 :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
"bet4 a b c d \<equiv> bet a b c \<and> bet b c d"

(* mi17017_Sara_Selakovic_FORMULACIJA *)
theorem t2_5:
  fixes a b c d :: point
  assumes "bet a b c" and "bet b c d"
  shows "bet4 a b c d"
  sorry

(* mi17017_Sara_Selakovic_FORMULACIJA *)
theorem t2_6:
  fixes a b c d :: point
  assumes "bet a b c" and "bet a c d"
  shows "bet4 a b c d"
  sorry

(* mi17017_Sara_Selakovic_FORMULACIJA *)
theorem t2_7:
  fixes a b c d :: point
  assumes "bet a b c" and "bet a b d" and "c \<noteq> d"
  shows "(bet4 a b c d) \<or> (bet4 a b d c)"
  sorry

(* mi17017_Sara_Selakovic_FORMULACIJA *)
theorem t2_8:
  fixes a b c d :: point
  assumes "bet a c b" and "bet a d b" and "c \<noteq> d"
  shows "(bet4 a d c b) \<or> (bet4 a c d b)"
  sorry

end

section \<open>Axioms of Congruence\<close>

locale GeometryCongruence = GeometryOrder +
    fixes cng :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" (* Given points a b c d, if [a, b] is congruent to [c, d] then \<open>cng a b c d\<close>.*)
  assumes ax_cng_1: "\<forall> a b c :: point. cng a a b c \<longrightarrow> b = c"
      and ax_cng_2: "\<forall> a b :: point. cng a b b a"
      and ax_cng_3: "\<forall> a b c d e f :: point. cng a b c d \<and> cng a b e f \<longrightarrow> cng c d e f"
      and ax_cng_4: "\<forall> a b a' b' :: point. \<forall> c \<in> open_segment a b. \<forall> c' \<in> open_segment a' b'. cng a c a' c' \<and> cng b c b' c' \<longrightarrow> cng a b a' b'"
      and ax_cng_5: "\<forall> a b c :: point. \<forall> p \<in> half_lines_origin c. a \<noteq> b \<longrightarrow> (\<exists>! d \<in> p. cng a b c d)"      
      and ax_cng_6: "\<forall> a b c a' b' :: point. \<forall> P \<in> half_planes_boundary (line a' b'). a' \<noteq> b' \<and> \<not> colinear a b c \<and> cng a b a' b' \<longrightarrow> (\<exists>! c' \<in> P. cng a c a' c' \<and> cng b c b' c')"
      and ax_cng_7: "\<forall> a b c a' b' c' :: point. \<forall> d \<in> half_line b c. \<forall> d' \<in> half_line b' c'. b \<noteq> c \<and> b' \<noteq> c' \<and> \<not> colinear a b c \<and> \<not> colinear a' b' c' \<and> cng a b a' b' \<and> cng b c b' c' \<and> cng c a c' a' \<and> cng b d b' d' \<longrightarrow> cng a d a' d'"
begin

end

section \<open>Axioms of Continuity\<close>

end
