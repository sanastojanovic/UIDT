theory Geo
  imports Main

begin

section \<open>Introduction\<close>

text \<open>
Type 'a denotes points.
Type 'b denotes lines.
Type 'c denotes planes.
\<close>
locale Geometry = 
  fixes inc_p_l :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (* Given point a and line l, if a is incident to l then inc_p_l a l*)
    and inc_p_pl :: "'a \<Rightarrow> 'c \<Rightarrow> bool" (* Given point a and plane P, if a is incident to P then inc_p_pl a P*)
    and inc_l_pl :: "'b \<Rightarrow> 'c \<Rightarrow> bool" (* Given line l and plane P, if l is incident to P then inc_l_pl l P *)
begin

(* If points a, b, and c are incident to some line l, then \<open>colinear a b c\<close>. *)
definition colinear :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "colinear a b c \<equiv> \<exists> l :: 'b. inc_p_l a l \<and> inc_p_l b l \<and> inc_p_l c l"

(* If points a, b, c, and d are incident to some plane P, then \<open>coplanar a b c d\<close>. *)
definition coplanar :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "coplanar a b c d \<equiv> \<exists> P :: 'c. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P \<and> inc_p_pl d P"

end

section \<open>Axioms of Incidence\<close>

locale GeometryIncidence = Geometry +
  assumes ax_inc_1: "\<And> l. \<exists> a b. a \<noteq> b \<and> inc_p_l a l \<and> inc_p_l b l" 
      and ax_inc_2: "\<And> a b. \<exists> l. inc_p_l a l \<and> inc_p_l b l"
      and ax_inc_3: "\<And> a b l l'. \<lbrakk>a \<noteq> b; inc_p_l a l; inc_p_l b l; inc_p_l a l'; inc_p_l b l'\<rbrakk> \<Longrightarrow> l = l'"
      and ax_inc_4: "\<And> P. \<exists> a b c. \<not> colinear a b c \<and> inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P"
      and ax_inc_5: "\<And> a b c. \<exists> P. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P"
      and ax_inc_6: "\<And> a b c P P'. \<lbrakk>\<not> colinear a b c; inc_p_pl a P; inc_p_pl b P; inc_p_pl c P;
                                     inc_p_pl a P'; inc_p_pl b P'; inc_p_pl c P'\<rbrakk> \<Longrightarrow> P = P'"
      and ax_inc_7: "\<And> l P a b. \<lbrakk>a \<noteq> b; inc_p_l a l; inc_p_l b l; inc_p_pl a P; inc_p_pl b P\<rbrakk> \<Longrightarrow> inc_l_pl l P"
      and ax_inc_8: "\<And> P Q a. \<lbrakk>inc_p_pl a P; inc_p_pl a Q\<rbrakk> \<Longrightarrow> (\<exists> b. a \<noteq> b \<and> inc_p_pl b P \<and> inc_p_pl b Q)"
      and ax_inc_9: "\<exists> a b c d. \<not> coplanar a b c d"
begin

subsection \<open>Three Non-Collinear Points and Four Non-Coplanar Points\<close>

subsection \<open>Lines and Planes\<close>

(* \<open>line a b\<close> is line that is defined by two points a and b. (Use under assumption: a \<noteq> b!) *)
definition line :: "'a \<Rightarrow> 'a \<Rightarrow> 'b" where
  "line a b \<equiv> THE l. inc_p_l a l \<and> inc_p_l b l"

(* \<open>plane a b c\<close> is plane that is defined by three points a, b, and c. (Use under assumption: \<not> colinear a b c \<and> a \<noteq> b \<and> b \<noteq> c \<and> c \<noteq> a!) *)
definition plane :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'c" where
  "plane a b c \<equiv> THE P. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P"

(* \<open>points_on_line\<close> is set of all points that are incident to line l. *)
definition points_on_line :: "'b  \<Rightarrow> 'a set" where
  "points_on_line l = {a. inc_p_l a l}"

(* \<open>points_on_plane\<close> is set of all points that are incident to plane P. *)
definition points_on_plane :: "'c  \<Rightarrow> 'a set" where
  "points_on_plane P = {a. inc_p_pl a P}"

subsection \<open>Fundamental Existence Theorems\<close>

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_1:
  assumes "\<not> colinear a b c"
  shows "distinct [a, b, c]"
  sorry

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_2:
  assumes "\<not> coplanar a b c d"
  shows "distinct [a, b, c, d]"
  sorry

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_3:
  assumes "\<not> coplanar a b c d"
  shows "\<not> colinear a b c" "\<not> colinear a b d" "\<not> colinear a c d" "\<not> colinear b c d"
  sorry

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_4_a:
  shows "\<exists> a b c d :: 'a. distinct [a, b, c, d]"
  sorry

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_4_b:
  shows "\<exists> p q r l s t :: 'b. distinct [p, q, r, l, s, t]"
  sorry

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_4_c:
  shows "\<exists> P Q R S :: 'c. distinct [P, Q, R, S]"
  sorry

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_5:
  shows "\<exists> a b c. \<not> colinear a b c"
  sorry

(* mi18269_Marija_Culic_FORMULACIJA *)
theorem t1_6:
  assumes "a \<noteq> b"
  shows "\<exists>! p. inc_p_l a p \<and> inc_p_l b p"
  sorry

lemma line:
  assumes "a \<noteq> b"
  shows "inc_p_l a (line a b) \<and> inc_p_l b (line a b)"
  unfolding line_def
  using t1_6[OF assms]
  by (smt (verit, best) Uniq_def the1_equality')

lemma line_equality:
  assumes "a \<noteq> b" and "inc_p_l a l" "inc_p_l b l"
  shows "l = line a b"
  unfolding line_def
  using assms t1_6[OF assms(1)]
  by (simp add: the1_equality)

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
theorem t1_7:
  assumes "\<not> colinear a b c" and "a \<noteq> b" "a \<noteq> c" "b \<noteq> c" 
  shows "\<exists>! P. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P"
  sorry

lemma plane_a:
  assumes "\<not> colinear a b c" "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
  shows "inc_p_pl a (plane a b c)"
  unfolding plane_def
  using t1_7[OF assms]
  by (smt (verit, ccfv_threshold) theI_unique)

lemma plane_b:
  assumes "\<not> colinear a b c" "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
  shows "inc_p_pl b (plane a b c)"
  unfolding plane_def
  using t1_7[OF assms]
  by (smt (verit, ccfv_threshold) theI_unique)

lemma plane_c:
  assumes "\<not> colinear a b c" "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
  shows "inc_p_pl c (plane a b c)"
  unfolding plane_def
  using t1_7[OF assms]
  by (smt (verit, ccfv_threshold) theI_unique)

lemma plane:
  assumes "\<not> colinear a b c" "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
  shows "inc_p_pl a (plane a b c) \<and> inc_p_pl b (plane a b c) \<and> inc_p_pl c (plane a b c)"
  using plane_a[OF assms] plane_b[OF assms] plane_c[OF assms]
  by simp

lemma plane_equality:
  assumes "\<not> colinear a b c" "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
      and "inc_p_pl a P" "inc_p_pl b P" "inc_p_pl c P"
    shows "P = plane a b c"
  unfolding plane_def
  using assms t1_7[OF assms(1,2,3,4)]
  by (smt (verit, ccfv_threshold) the_equality)

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
(* \<open>plane'\<close> \<rightarrow> plane that is defined by line and point that doesn't belongs to that line. (Use under assumption: \<not> (inc_p_l a p) *)
definition plane_p_l :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" where
  "plane_p_l a p \<equiv> THE P. inc_p_pl a P \<and>  inc_l_pl p P"

lemma plane_p_l_unique:
  assumes "\<not> inc_p_l a l"
  shows "\<exists>! P. inc_p_pl a P \<and> inc_l_pl l P"
  using assms
  sorry

lemma plane_p_l:
  assumes "\<not> inc_p_l a l"
  shows "inc_p_pl a (plane_p_l a l)" "inc_l_pl l (plane_p_l a l)"
  unfolding plane_p_l_def
  using plane_p_l_unique[OF assms]
  by (smt (verit, ccfv_threshold) the_equality)+

lemma plane_p_l_equality:
  assumes "\<not> inc_p_l a l" 
          "inc_p_pl a P" "inc_l_pl l P"
  shows "P = plane_p_l a l"
  unfolding plane_p_l_def
  using plane_p_l_unique assms
  by (smt (verit, del_insts) the_equality)

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
theorem t1_8:
  assumes "\<not> inc_p_l a p"
  shows "\<exists>! P. inc_l_pl p P \<and> inc_p_pl a P"
  sorry

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
(* \<open>intersects\<close> \<rightarrow> do two lines have intersection. *)
definition intersects :: "'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "intersects p q \<equiv> (\<exists> a. inc_p_l a p \<and> inc_p_l a q)"

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
(* \<open>plane''\<close> \<rightarrow> plane that is defined by two lines that initersect. (Use under assumption: p \<noteq> q \<and> intersects p q) *)
definition plane_l_l :: "'b \<Rightarrow> 'b \<Rightarrow> 'c" where
  "plane_l_l p q \<equiv> THE P. inc_l_pl p P \<and> inc_l_pl q P"

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
theorem t1_9:
  assumes "intersects p q" and "p \<noteq> q"
  shows "\<exists>! P. inc_l_pl p P \<and> inc_l_pl q P"
  sorry

(* mi17122_Tamara_Tomic_FORMULACIJA *)
(* \<open>coplanar_lines p q\<close> : two lines are coplanar if they are in the same plane *)
definition coplanar_lines :: "'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "coplanar_lines p q \<equiv> \<exists> P. inc_l_pl p P \<and> inc_l_pl q P"

(* mi17122_Tamara_Tomic_FORMULACIJA *)
(* \<open>skew_lines p q\<close> : skew lines are lines which are not coplanar *)
definition skew_lines :: "'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "skew_lines p q \<equiv> \<not>(coplanar_lines p q)"

(* mi17122_Tamara_Tomic_FORMULACIJA *)
theorem t1_10:
  "\<exists> p q. skew_lines p q"
  sorry

subsection \<open>Intersections of Lines and Planes\<close>

(* mi17122_Tamara_Tomic_FORMULACIJA *)
(* \<open>intersection p q\<close> is a point where two lines intersect (Use under assumption: p \<noteq> q) *)
definition intersection_l_l :: "'b \<Rightarrow> 'b \<Rightarrow> 'a" where
  "intersection_l_l p q \<equiv> THE a. inc_p_l a p \<and> inc_p_l a q"

(* mi17122_Tamara_Tomic_FORMULACIJA *)
theorem t1_11:
  assumes "p \<noteq> q" "inc_p_l a p" "inc_p_l a q" "inc_p_l b p" "inc_p_l b q"
  shows "a = b"
  sorry

(* mi17122_Tamara_Tomic_FORMULACIJA *)
(* \<open>intersection' p P\<close> point where line and plane intersect (Use under assumption: \<not> inc_l_pl p P) *)
definition intersection_l_pl :: "'b \<Rightarrow> 'c \<Rightarrow> 'a" where
  "intersection_l_pl p P \<equiv> THE a. inc_p_l a p \<and> inc_p_pl a P"

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
theorem t1_12:
  assumes "\<not> inc_l_pl l P" "inc_p_l a l" "inc_p_pl a P" "inc_p_l b l" "inc_p_pl b P"
  shows "a = b"
  sorry

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* \<open>plane_plane_intersect_line P Q\<close> is line that is defined as intersection of planes P and Q. (Use under assumption: P \<noteq> Q and P and Q have intersection (i.e. not parallel)!) *)
definition intersection_pl_pl :: "'c \<Rightarrow> 'c \<Rightarrow> 'b" where
  "intersection_pl_pl P Q \<equiv> THE l. inc_l_pl l P \<and> inc_l_pl l Q"

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
theorem t1_13:
  assumes "P \<noteq> Q" "\<exists> a. inc_p_pl a P \<and> inc_p_pl a Q"
  shows "\<exists> l. \<forall> a. inc_p_l a l \<longleftrightarrow> inc_p_pl a P \<and> inc_p_pl a Q"
  sorry

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* If lines in set of lines L are concurrent then \<open>concurrent_lines L\<close>. *)
definition concurrent_line_set :: "'b set \<Rightarrow> bool" where
  "concurrent_line_set L \<equiv> \<exists> a. \<forall> l \<in> L. inc_p_l a l"

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* If lines in set of lines L are coplanar then \<open>coplanar_lines L\<close>. *)
definition coplanar_line_set :: "'b set \<Rightarrow> bool" where
  "coplanar_line_set L \<equiv> \<exists> P. \<forall> l \<in> L. inc_l_pl l P"

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
theorem t1_14:
  assumes "\<forall> l\<^sub>2 \<in> L. \<forall> l\<^sub>2 \<in> L. intersects l\<^sub>1 l\<^sub>2"
  shows "concurrent_line_set L \<or> coplanar_line_set L"
  sorry

end

section \<open>Linear Axioms of Order\<close>

locale GeometryOrder = GeometryIncidence +
    fixes bet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (* Given points a, b, and c, if b between a and c then \<open>bet a b c\<close>.*)
  assumes ax_ord_1: "\<forall> a b c :: 'a. bet a b c \<longrightarrow> a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c \<and> colinear a b c"
      and ax_ord_2: "\<forall> a b c :: 'a. bet a b c \<longrightarrow> bet c b a"
      and ax_ord_3: "\<forall> a b c :: 'a. bet a b c \<longrightarrow> \<not> bet a c b"
      and ax_ord_4: "\<forall> a b :: 'a. a \<noteq> b \<longrightarrow> (\<exists> c :: 'a. bet a b c)"
      and ax_ord_5: "\<forall> a b :: 'a. a \<noteq> b \<longrightarrow> (\<exists> c :: 'a. bet a c b)"
      and ax_ord_6: "\<forall> a b c :: 'a. a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c \<and> colinear a b c \<longrightarrow> bet a b c \<or> bet b c a \<or> bet c a b"
      and ax_Pasch: "\<forall> a b c :: 'a. \<forall> p :: 'b. \<not> (colinear a b c) \<and> inc_l_pl p (plane a b c) \<and> (\<not> inc_p_l a p) 
                    \<and> (bet b (intersection p (line b c)) c) \<longrightarrow>  (bet c (intersection p (line c a)) a) \<or> (bet a (intersection p (line a b)) b)"
begin

(* \<open>open_segment a b\<close> is set of all points between a and b. *)
definition open_segment :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "open_segment a b = {c. bet a c b}"

(* \<open>half_line a b\<close> is set of all points between a and b and all points c such that b is between a and c, including a and b. (Use under assumption: a \<noteq> b!*)
definition half_line :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "half_line a b = {c. c = a \<or> c = b \<or> bet a c b \<or> bet a b c}"

(* \<open>half_lines_origin a\<close> is set of all half-lines with origin a. *)
definition half_lines_origin :: "'a \<Rightarrow> 'a set set" where
  "half_lines_origin a = {p. \<exists> b. p = half_line a b}"

(* Given points a and b, and line l, if l between a and b then \<open>bet_line a l b\<close>.*)
definition bet_line :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool" where
  "bet_line a l b \<equiv> \<exists> c \<in> points_on_line l. bet a c b"

(* \<open>half_plane l a\<close> is a set of all points between a and l and all points c such that a is between c and l, including points on l and a. (Use under assumption: \<not> inc_p_l a l.*)
definition half_plane :: "'b \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "half_plane l a = {c. \<forall> b \<in> points_on_line l. c = a \<or> c = b \<or> bet b c a \<or> bet b a c}"

(* \<open>half_planes\<close> is set of all half-planes with boundary l. *)
definition half_planes_boundary :: "'b \<Rightarrow> 'a set set" where
  "half_planes_boundary l = {P. \<forall> a. P = half_plane l a}"

(* mi17227_Anita_Jovanovic_FORMULACIJA *)
(* < bet3 > \<rightarrow> only one is true*)
definition one_of_three where
  "one_of_three X Y Z \<equiv> (X \<and> \<not> Y \<and> \<not> Z) \<or> (\<not> X \<and> Y \<and> \<not> Z) \<or> (\<not> X \<and> \<not> Y \<and> Z)"

definition bet3 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "bet3 a b c \<equiv> one_of_three (bet a b c) (bet b c a) (bet c a b)"

(* mi17227_Anita_Jovanovic_FORMULACIJA *)
theorem t2_1:
  assumes "colinear a b c" and "distinct [a, b, c]" 
  shows "bet3 a b c"
  sorry

(* mi17227_Anita_Jovanovic_FORMULACIJA *)
theorem t2_2:
  assumes "a \<noteq> b"
  shows "inc_p_l x (line a b) \<longleftrightarrow> 
             (x = a \<or> x = b) \<or> 
             (bet3 a b x)"
  sorry

(* mi17227_Anita_Jovanovic_FORMULACIJA *)
theorem t2_3:
  assumes "\<not> colinear a b c" and 
          "a \<noteq> b" "a \<noteq> c" "b \<noteq> c" and  
          "bet b p c" and "bet c q a" and "bet a r b"
  shows "\<not> colinear p q r"
  sorry

(* mi17017_Sara_Selakovic_FORMULACIJA *)
theorem t2_4:
  assumes "a \<noteq> b"
  shows "\<exists>c. bet a c b"
  sorry

(* mi17017_Sara_Selakovic_FORMULACIJA *)
(* \<open> bet4 \<close> \<longrightarrow> Given points a, b, c and d. If b and c between a and d, in the way that b between a and c, and c between b and d, then \<open> bet4 a b c d \<close> *)
definition bet4 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "bet4 a b c d \<equiv> bet a b c \<and> bet b c d"

(* mi17017_Sara_Selakovic_FORMULACIJA *)
theorem t2_5:
  assumes "bet a b c" and "bet b c d"
  shows "bet4 a b c d"
  sorry

(* mi17017_Sara_Selakovic_FORMULACIJA *)
theorem t2_6:
  assumes "bet a b c" and "bet a c d"
  shows "bet4 a b c d"
  sorry

(* mi17017_Sara_Selakovic_FORMULACIJA *)
theorem t2_7:
  assumes "bet a b c" and "bet a b d" and "c \<noteq> d"
  shows "(bet4 a b c d) \<or> (bet4 a b d c)"
  sorry

(* mi17017_Sara_Selakovic_FORMULACIJA *)
theorem t2_8:
  assumes "bet a c b" and "bet a d b" and "c \<noteq> d"
  shows "(bet4 a d c b) \<or> (bet4 a c d b)"
  sorry

(* mi19009_Mina Cerovic FORMULACIJA *)
(* \<open>left_half_open_segment a b\<close> is set of all points between a and b, including a. *)
definition left_half_open_segment :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "left_half_open_segment a b = {c. bet a c b} \<union> {a}"

(* mi19009_Mina Cerovic FORMULACIJA *)
(* \<open>right_half_open_segment a b\<close> is set of all points between a and b, including b. *)
definition right_half_open_segment :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "right_half_open_segment a b = {c. bet a c b} \<union> {b}"

(* mi19009_Mina Cerovic FORMULACIJA *)
(* \<open>segment a b\<close> is set of all points between a and b, including a and b. *)
definition segment :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "segment a b = {c. bet a c b} \<union> {a} \<union> {b}"

(* mi19009_Mina Cerovic FORMULACIJA *)
theorem t3_1:
  assumes "c \<in> open_segment a b" and "c \<noteq> d"
  shows "d \<in> open_segment a b \<longleftrightarrow> 
          (d \<in> open_segment a c \<and> d \<notin> open_segment c b) \<or> 
          (d \<notin> open_segment a c \<and> d \<in> open_segment c b)"
  sorry
 
(* mi19009_Mina Cerovic FORMULACIJA *)
theorem t3_2:
  fixes a b c :: 'a
  assumes "colinear a b c" 
  shows "open_segment a b \<inter> open_segment b c = {} \<longleftrightarrow> bet a b c"
  sorry

(* mi19009_Mina Cerovic FORMULACIJA *)
(* \<open>linear_arrangement\<close> *)
fun linear_arrangement :: "'a list \<Rightarrow> bool" where
  "linear_arrangement [] = True" |
  "linear_arrangement [a] = True" |
  "linear_arrangement [a, b] = True" |
  "linear_arrangement (a # b # c # l) \<longleftrightarrow> (bet a b c) \<and> linear_arrangement (b # c # l)"

end

section \<open>Axioms of Congruence\<close>

locale GeometryCongruence = GeometryOrder +
    fixes cng :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (* Given points a b c d, if [a, b] is congruent to [c, d] then \<open>cng a b c d\<close>.*)
  assumes ax_cng_1: "\<forall> a b c :: 'a. cng a a b c \<longrightarrow> b = c"
      and ax_cng_2: "\<forall> a b :: 'a. cng a b b a"
      and ax_cng_3: "\<forall> a b c d e f :: 'a. cng a b c d \<and> cng a b e f \<longrightarrow> cng c d e f"
      and ax_cng_4: "\<forall> a b a' b' :: 'a. \<forall> c \<in> open_segment a b. \<forall> c' \<in> open_segment a' b'. cng a c a' c' \<and> cng b c b' c' \<longrightarrow> cng a b a' b'"
      and ax_cng_5: "\<forall> a b c :: 'a. \<forall> p \<in> half_lines_origin c. a \<noteq> b \<longrightarrow> (\<exists>! d \<in> p. cng a b c d)"      
      and ax_cng_6: "\<forall> a b c a' b' :: 'a. \<forall> P \<in> half_planes_boundary (line a' b'). a' \<noteq> b' \<and> \<not> colinear a b c \<and> cng a b a' b' \<longrightarrow> (\<exists>! c' \<in> P. cng a c a' c' \<and> cng b c b' c')"
      and ax_cng_7: "\<forall> a b c a' b' c' :: 'a. \<forall> d \<in> half_line b c. \<forall> d' \<in> half_line b' c'. b \<noteq> c \<and> b' \<noteq> c' \<and> \<not> colinear a b c \<and> \<not> colinear a' b' c' \<and> cng a b a' b' \<and> cng b c b' c' \<and> cng c a c' a' \<and> cng b d b' d' \<longrightarrow> cng a d a' d'"
begin

end

section \<open>Axioms of Continuity\<close>

end
