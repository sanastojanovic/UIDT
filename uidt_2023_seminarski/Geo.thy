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
begin

(* If points a, b, and c are incident to some line l, then \<open>colinear a b c\<close>. *)
definition colinear :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "colinear a b c \<equiv> \<exists> l :: 'b. inc_p_l a l \<and> inc_p_l b l \<and> inc_p_l c l"

(* If points a, b, c, and d are incident to some plane P, then \<open>coplanar a b c d\<close>. *)
definition coplanar :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "coplanar a b c d \<equiv> \<exists> P :: 'c. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P \<and> inc_p_pl d P"

(* Given line l and plane P, if l is incident to P then inc_l_pl l P *)
definition inc_l_pl :: "'b \<Rightarrow> 'c \<Rightarrow> bool" where
  "inc_l_pl l P \<equiv> \<forall> a. inc_p_l a l \<longrightarrow> inc_p_pl a P"

end

section \<open>Axioms of Incidence\<close>

locale GeometryIncidence = Geometry +
  assumes ax_inc_1: "\<And> l. \<exists> a b. a \<noteq> b \<and> inc_p_l a l \<and> inc_p_l b l" 
      and ax_inc_2: "\<And> a b. \<exists> l. inc_p_l a l \<and> inc_p_l b l"
      and ax_inc_3: "\<And> a b l l'. \<lbrakk>a \<noteq> b; inc_p_l a l; inc_p_l b l; inc_p_l a l'; inc_p_l b l'\<rbrakk> \<Longrightarrow> l = l'"
      and ax_inc_4: "\<And> P. \<exists> a b c. \<not> colinear a b c \<and> inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P"
      and ax_inc_5: "\<And> a b c. \<exists> P. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P"
      and ax_inc_6: "\<And> a b c P P'. \<lbrakk>\<not> colinear a b c; 
                                     inc_p_pl a P; inc_p_pl b P; inc_p_pl c P;
                                     inc_p_pl a P'; inc_p_pl b P'; inc_p_pl c P'\<rbrakk> \<Longrightarrow> P = P'"
      and ax_inc_7: "\<And> l P a b. \<lbrakk>a \<noteq> b; inc_p_l a l; inc_p_l b l; 
                                         inc_p_pl a P; inc_p_pl b P\<rbrakk> \<Longrightarrow>
                                     inc_l_pl l P"
      and ax_inc_8: "\<And> P Q a. \<lbrakk>inc_p_pl a P; inc_p_pl a Q\<rbrakk> \<Longrightarrow> 
                                     (\<exists> b. a \<noteq> b \<and> inc_p_pl b P \<and> inc_p_pl b Q)"
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

lemma inc_trans:
  assumes "inc_l_pl l P" "inc_p_l a l"
  shows "inc_p_pl a P"
  using assms
  using inc_l_pl_def
  by blast


(* mi18269_Marija_Culic_FORMULACIJA *)
(* mi18269_Marija_Culic_DOKAZ *)
theorem t1_1:
  assumes "\<not> colinear a b c"
  shows "distinct [a, b, c]"
proof (rule ccontr)
  assume "\<not> distinct [a, b, c]"
  then have "\<not> (a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c)" by simp
  then have "a = b \<or> a = c \<or> b = c" by blast
  then have "colinear a b c"
    unfolding colinear_def using ax_inc_2 by auto
  with assms show False by auto
qed

(* mi18269_Marija_Culic_FORMULACIJA *)
(* mi18269_Marija_Culic_DOKAZ *)
theorem t1_2:
  assumes "\<not> coplanar a b c d"
  shows "distinct [a, b, c, d]"
proof (rule ccontr)
  assume "\<not> distinct [a, b, c, d]"
  then have "\<not> (a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d)" by simp
  then have "a = b \<or> a = c \<or> a = d \<or> b = c \<or> b = d \<or> c = d" by auto
  then have "coplanar a b c d" 
    unfolding coplanar_def using ax_inc_5 by blast
  with assms show False by auto
qed

(* mi18269_Marija_Culic_FORMULACIJA *)
(* mi18269_Marija_Culic_DOKAZ *)
theorem t1_3:
  assumes "\<not> coplanar a b c d"
  shows "\<not> colinear a b c \<and> \<not> colinear a b d \<and> \<not> colinear a c d \<and> \<not> colinear b c d"
proof -
  {
    assume "colinear a b c"
    then obtain p :: 'b where "inc_p_l a p" and "inc_p_l b p" and "inc_p_l c p" using ax_inc_2 using colinear_def by blast
    then obtain P :: 'c where "inc_p_pl a P" and "inc_p_pl b P" and "inc_p_pl d P" using ax_inc_5 by blast
    then have "a \<noteq> b" using t1_2 assms by auto
    then have "inc_l_pl p P" using ax_inc_7  by (simp add: \<open>inc_p_l a p\<close> \<open>inc_p_l b p\<close> \<open>inc_p_pl a P\<close> \<open>inc_p_pl b P\<close>)
    then have "coplanar a b c d" using \<open>inc_p_l c p\<close> \<open>inc_p_pl a P\<close> \<open>inc_p_pl b P\<close> \<open>inc_p_pl d P\<close> coplanar_def inc_trans by blast
    with assms have False by simp
  }
  moreover {
    assume "colinear a b d"
    then obtain p :: 'b where "inc_p_l a p" and "inc_p_l b p" and "inc_p_l d p" using ax_inc_2 using colinear_def by blast
    then obtain P :: 'c where "inc_p_pl a P" and "inc_p_pl b P" and "inc_p_pl c P" using ax_inc_5 by blast
    then have "a \<noteq> b" using t1_2 assms by auto
    then have "inc_l_pl p P" using ax_inc_7  by (simp add: \<open>inc_p_l a p\<close> \<open>inc_p_l b p\<close> \<open>inc_p_pl a P\<close> \<open>inc_p_pl b P\<close>)
    then have "coplanar a b c d" using \<open>inc_p_l d p\<close> \<open>inc_p_pl a P\<close> \<open>inc_p_pl b P\<close> \<open>inc_p_pl c P\<close> coplanar_def inc_trans by blast
    with assms have False by simp
  }
  moreover {
    assume "colinear a c d"  
    then obtain p :: 'b where "inc_p_l a p" and "inc_p_l c p" and "inc_p_l d p" using ax_inc_2 using colinear_def by blast
    then obtain P :: 'c where "inc_p_pl a P" and "inc_p_pl c P" and "inc_p_pl b P" using ax_inc_5 by blast
    then have "a \<noteq> c" using t1_2 assms by auto
    then have "inc_l_pl p P" using ax_inc_7  by (simp add: \<open>inc_p_l a p\<close> \<open>inc_p_l c p\<close> \<open>inc_p_pl a P\<close> \<open>inc_p_pl c P\<close>)
    then have "coplanar a b c d" using \<open>inc_p_l d p\<close> \<open>inc_p_pl a P\<close> \<open>inc_p_pl c P\<close> \<open>inc_p_pl b P\<close> coplanar_def inc_trans by blast
    with assms have False by simp
  }
  moreover {
    assume "colinear b c d"
    then obtain p :: 'b where "inc_p_l b p" and "inc_p_l c p" and "inc_p_l d p" using ax_inc_2 using colinear_def by blast
    then obtain P :: 'c where "inc_p_pl b P" and "inc_p_pl c P" and "inc_p_pl a P" using ax_inc_5 by blast
    then have "b \<noteq> c" using t1_2 assms by auto
    then have "inc_l_pl p P" using ax_inc_7  by (simp add: \<open>inc_p_l b p\<close> \<open>inc_p_l c p\<close> \<open>inc_p_pl b P\<close> \<open>inc_p_pl c P\<close>)
    then have "coplanar a b c d" using \<open>inc_p_l d p\<close> \<open>inc_p_pl b P\<close> \<open>inc_p_pl c P\<close> \<open>inc_p_pl a P\<close> coplanar_def inc_trans by blast
    with assms have False by simp
  }
  ultimately show ?thesis by auto
qed

(* mi18269_Marija_Culic_FORMULACIJA *)
(* mi18269_Marija_Culic_DOKAZ *)
theorem t1_4_a:
  shows "\<exists> a b c d :: 'a. distinct [a, b, c, d]"
  using ax_inc_9 t1_2 by blast

(* mi18269_Marija_Culic_FORMULACIJA *)
(* mi18269_Marija_Culic_DOKAZ *)
theorem t1_4_b: "\<exists> p q r l s t :: 'b. distinct [p, q, r, l, s, t]"
proof -
  have "\<exists> a b c d :: 'a. \<not> coplanar a b c d" using ax_inc_9 by simp
  then obtain a b c d :: 'a where "\<not> coplanar a b c d" "distinct [a, b, c, d]"  using t1_2 by auto
  then obtain p :: 'b where "inc_p_l a p" and "inc_p_l b p"  using ax_inc_2 by auto
  then obtain q :: 'b where "inc_p_l a q" and "inc_p_l c q" using ax_inc_2 by auto
  then obtain r :: 'b where "inc_p_l a r" and "inc_p_l d r" using ax_inc_2 by auto
  then obtain l :: 'b where "inc_p_l b l" and "inc_p_l c l" using ax_inc_2 by auto
  then obtain s :: 'b where "inc_p_l b s" and "inc_p_l d s" using ax_inc_2 by auto
  then obtain t :: 'b where "inc_p_l c t" and "inc_p_l d t" using ax_inc_2 by auto

  then have "distinct [p, q, r, l, s, t]"
    by (metis (full_types) Geometry.colinear_def \<open>\<not> coplanar a b c d\<close> \<open>inc_p_l a p\<close> \<open>inc_p_l a q\<close> \<open>inc_p_l a r\<close> \<open>inc_p_l b l\<close> \<open>inc_p_l b p\<close> \<open>inc_p_l b s\<close> \<open>inc_p_l c l\<close> \<open>inc_p_l c q\<close> \<open>inc_p_l d r\<close> \<open>inc_p_l d s\<close> distinct_length_2_or_more distinct_singleton t1_3)
  show ?thesis  using \<open>distinct [p, q, r, l, s, t]\<close> by blast
qed

(* mi18269_Marija_Culic_FORMULACIJA *)
(* mi18269_Marija_Culic_DOKAZ *)
theorem t1_4_c:
  shows "\<exists> P Q R S :: 'c. distinct [P, Q, R, S]"
proof -
  have "\<exists> a b c d :: 'a. \<not> coplanar a b c d" using ax_inc_9 by simp
  then obtain a b c d :: 'a where "\<not> coplanar a b c d" "distinct [a, b, c, d]"  using t1_2 by auto
  then obtain P :: 'c where "inc_p_pl a P" and "inc_p_pl b P" and "inc_p_pl c P"  using ax_inc_5 by blast
  then obtain Q :: 'c where "inc_p_pl a Q" and "inc_p_pl b Q" and "inc_p_pl d Q"  using ax_inc_5 by blast
  then obtain R :: 'c where "inc_p_pl a R" and "inc_p_pl c R" and "inc_p_pl d R"  using ax_inc_5 by blast
  then obtain S :: 'c where "inc_p_pl b S" and "inc_p_pl c S" and "inc_p_pl d S"  using ax_inc_5 by blast 

  then have "distinct [P, Q, R, S]"
    using \<open>\<not> coplanar a b c d\<close> \<open>inc_p_pl a P\<close> \<open>inc_p_pl a Q\<close> \<open>inc_p_pl a R\<close> \<open>inc_p_pl b P\<close> \<open>inc_p_pl b Q\<close> \<open>inc_p_pl c P\<close> \<open>inc_p_pl c R\<close> \<open>inc_p_pl d Q\<close> \<open>inc_p_pl d R\<close> coplanar_def by auto
  show ?thesis using \<open>distinct [P, Q, R, S]\<close> by blast
qed

(* mi18269_Marija_Culic_FORMULACIJA *)
(* mi18269_Marija_Culic_DOKAZ *)
theorem t1_5:
  shows "\<exists> a b c. \<not> colinear a b c"
  using ax_inc_4 by blast

(* mi18269_Marija_Culic_FORMULACIJA *)
(* mi18269_Marija_Culic_DOKAZ *)
theorem t1_6:
  assumes "a \<noteq> b"
  shows "\<exists>! p. inc_p_l a p \<and> inc_p_l b p"
  using assms ax_inc_3 ax_inc_2
  unfolding colinear_def
  by auto

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
(* mi20045_Aleksandar_Zecevic_DOKAZ *)
theorem t1_12:
  assumes "\<not> inc_l_pl l P" "inc_p_l a l" "inc_p_pl a P" "inc_p_l b l" "inc_p_pl b P"
  shows "a = b"
  using assms ax_inc_7 by auto

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* \<open>plane_plane_intersect_line P Q\<close> is line that is defined as intersection of planes P and Q. (Use under assumption: P \<noteq> Q and P and Q have intersection (i.e. not parallel)!) *)
definition intersection_pl_pl :: "'c \<Rightarrow> 'c \<Rightarrow> 'b" where
  "intersection_pl_pl P Q \<equiv> THE l. inc_l_pl l P \<and> inc_l_pl l Q"

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* mi20045_Aleksandar_Zecevic_DOKAZ *)
theorem t1_13:
  assumes "P \<noteq> Q" "inc_p_pl a P" "inc_p_pl a Q"
  shows "\<exists> l. \<forall> p. inc_p_l p l \<longleftrightarrow> inc_p_pl p P \<and> inc_p_pl p Q"
proof -
  obtain b where "b \<noteq> a" "inc_p_pl b P" "inc_p_pl b Q"
    by (metis assms(2) assms(3) ax_inc_8)
  moreover
  obtain l where "inc_p_l a l" "inc_p_l b l"
    using ax_inc_2 by auto
  ultimately
  have "\<forall> p. inc_p_l p l \<longleftrightarrow> inc_p_pl p P \<and> inc_p_pl p Q"
    by (metis (full_types) assms ax_inc_7 inc_trans plane_p_l_equality)
  then show ?thesis
    by auto
qed

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* If lines in set of lines L are concurrent then \<open>concurrent_lines L\<close>. *)
definition concurrent_line_set :: "'b set \<Rightarrow> bool" where
  "concurrent_line_set L \<equiv> \<exists> a. \<forall> l \<in> L. inc_p_l a l"

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* If lines in set of lines L are coplanar then \<open>coplanar_lines L\<close>. *)
definition coplanar_line_set :: "'b set \<Rightarrow> bool" where
  "coplanar_line_set L \<equiv> \<exists> P. \<forall> l \<in> L. inc_l_pl l P"


(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* mi20045_Aleksandar_Zecevic_DOKAZ *)
(* Auxiliary lemma for next (1.14) theorem. *)
lemma noncoplanar_intersecting_lines:
  assumes "l\<^sub>1 \<noteq> l\<^sub>2" "inc_p_l a l\<^sub>1" "inc_p_l a l\<^sub>2"
      and "inc_l_pl l\<^sub>1 P" "inc_l_pl l\<^sub>2 P" "\<not> inc_l_pl l\<^sub>3 P"
      and "intersects l\<^sub>1 l\<^sub>3" "intersects l\<^sub>2 l\<^sub>3"
    shows "inc_p_l a l\<^sub>3"
  by (smt (verit) assms ax_inc_3 inc_l_pl_def intersects_def t1_12)

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* mi20045_Aleksandar_Zecevic_DOKAZ *)
theorem t1_14:
  assumes "\<forall> l\<^sub>1 \<in> L. \<forall> l\<^sub>2 \<in> L. intersects l\<^sub>1 l\<^sub>2"
  shows "concurrent_line_set L \<or> coplanar_line_set L"
proof -
  consider (empty) "L = {}" |
           (singleton) "card L = 1" |
           (pair) "card L = 2" |
           (general) "card L = 0 \<and> L \<noteq> {} \<or> card L \<ge> 3"
    by linarith
  then show ?thesis
  proof cases
    case empty
    then show ?thesis
      by (simp add: concurrent_line_set_def)
  next
    case singleton
    then show ?thesis
      by (metis ax_inc_1 card_1_singletonE concurrent_line_set_def singletonD)
  next
    case pair
    then show ?thesis
      by (metis assms card_2_iff' concurrent_line_set_def intersects_def)
  next
    case general
    then have "L \<noteq> {}" "card L \<noteq> 1" "card L \<noteq> 2"
      by auto
    then obtain p q where "p \<in> L" "q \<in> L" "p \<noteq> q"
      by (meson is_singletonI' is_singleton_altdef)
    obtain a where "inc_p_l a p" "inc_p_l a q"
      using \<open>p \<in> L\<close> \<open>q \<in> L\<close> assms intersects_def by blast
    obtain P where "inc_l_pl p P" "inc_l_pl q P"
      using \<open>p \<in> L\<close> \<open>q \<in> L\<close> \<open>p \<noteq> q\<close> assms t1_9 by blast
    show ?thesis 
    proof (rule disjCI)
      assume "\<not> coplanar_line_set L"
      then obtain r where "r \<in> L" "\<not> inc_l_pl r P"
        using coplanar_line_set_def by blast
      then have "inc_p_l a r"
        using \<open>inc_l_pl p P\<close> \<open>inc_l_pl q P\<close> \<open>inc_p_l a p\<close> \<open>inc_p_l a q\<close> \<open>p \<in> L\<close> \<open>p \<noteq> q\<close> \<open>q \<in> L\<close> assms noncoplanar_intersecting_lines by blast
      have "\<forall> l \<in> L. inc_p_l a l"
      proof
        fix l
        assume "l \<in> L"
        show "inc_p_l a l"
        proof cases
          assume "inc_l_pl l P"
          obtain b where "inc_p_l b l" "inc_p_l b r"
            using \<open>l \<in> L\<close> \<open>r \<in> L\<close> assms intersects_def by blast
          then have "a = b"
            using \<open>\<not> inc_l_pl r P\<close> \<open>inc_l_pl l P\<close> \<open>inc_l_pl q P\<close> \<open>inc_p_l a q\<close> \<open>inc_p_l a r\<close> inc_l_pl_def t1_12 by auto
          then show ?thesis
            by (simp add: \<open>inc_p_l b l\<close>)
        next
          assume "\<not> inc_l_pl l P"
          then show ?thesis
            using \<open>inc_l_pl p P\<close> \<open>inc_l_pl q P\<close> \<open>inc_p_l a p\<close> \<open>inc_p_l a q\<close> \<open>l \<in> L\<close> \<open>p \<in> L\<close> \<open>p \<noteq> q\<close> \<open>q \<in> L\<close> assms noncoplanar_intersecting_lines by blast
        qed
      qed
      then show "concurrent_line_set L"
        using concurrent_line_set_def by auto
    qed
  qed
qed

end

section \<open>Linear Axioms of Order\<close>

locale GeometryOrder = GeometryIncidence +
    fixes bet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (* Given points a, b, and c, if b between a and c then \<open>bet a b c\<close>.*)
  assumes ax_ord_1: "\<And> a b c. bet a b c \<Longrightarrow> a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c \<and> colinear a b c"
      and ax_ord_2: "\<And> a b c. bet a b c \<Longrightarrow> bet c b a"
      and ax_ord_3: "\<And> a b c. bet a b c \<Longrightarrow> \<not> bet a c b"
      and ax_ord_4: "\<And> a b. a \<noteq> b \<Longrightarrow> (\<exists> c. bet a b c)"
      and ax_ord_5: "\<And> a b c. \<lbrakk>a \<noteq> b; b \<noteq> c; a \<noteq> c; colinear a b c\<rbrakk> \<Longrightarrow> bet a b c \<or> bet b c a \<or> bet c a b"
      and ax_Pasch: "\<And> a b c l. \<lbrakk>\<not> colinear a b c; inc_l_pl l (plane a b c); \<not> inc_p_l a l; 
                                 bet b (intersection l (line b c)) c\<rbrakk> \<Longrightarrow> 
                                 (bet c (intersection l (line c a)) a) \<or> 
                                 (bet a (intersection l (line a b)) b)"
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
  "half_planes_boundary l = {P. \<exists> a. P = half_plane l a}"

(* mi17227_Anita_Jovanovic_FORMULACIJA *)
(* < bet3 > \<rightarrow> only one is true*)
definition one_of_three where
  "one_of_three X Y Z \<equiv> (X \<and> \<not> Y \<and> \<not> Z) \<or> (\<not> X \<and> Y \<and> \<not> Z) \<or> (\<not> X \<and> \<not> Y \<and> Z)"

definition bet3 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "bet3 a b c \<equiv> one_of_three (bet a b c) (bet b c a) (bet c a b)"


(* mi17227_Anita_Jovanovic_FORMULACIJA *)
(* mi20357_Jelena_Mitrovic_DOKAZ *)

theorem t2_1:
  assumes "colinear a b c" and "distinct [a, b, c]"
  shows "bet3 a b c"
proof -
  have "a ≠ b" and "b ≠ c" and "a ≠ c"
    using assms by auto
  consider "bet a b c" | "bet b c a" | "bet c a b"
    using assms ax_ord_5[of a b c] by auto
  then show ?thesis
  proof cases
    assume "bet a b c"
    then have "one_of_three (bet a b c) (bet b c a) (bet c a b)"
      unfolding one_of_three_def 
      using ax_ord_2 ax_ord_3 by blast
    then show ?thesis
      unfolding bet3_def by auto
  next
    assume "bet b c a"
    then have "one_of_three (bet a b c) (bet b c a) (bet c a b)"
      unfolding one_of_three_def 
      using ax_ord_2 ax_ord_3 by blast
    then show ?thesis
      unfolding bet3_def by auto
  next
    assume "bet c a b"
    then have "one_of_three (bet a b c) (bet b c a) (bet c a b)"
      unfolding one_of_three_def 
      using ax_ord_2 ax_ord_3 by blast
    then show ?thesis
      unfolding bet3_def by auto
  qed
qed


(* mi17227_Anita_Jovanovic_FORMULACIJA *)
(* mi20357_Jelena_Mitrovic_DOKAZ *)

theorem t2_2:
  assumes "a ≠ b"
  shows "inc_p_l x (line a b) ⟷
             (x = a ∨ x = b) ∨
             (bet3 a b x)"
proof
  assume "inc_p_l x (line a b)"
  consider "x = a" | "x = b" | "bet a x b" | "bet a b x"| "bet b a x "
    using assms
    by (meson ‹inc_p_l x (line a b)› ax_ord_2 ax_ord_5 colinear_def line)
  thus "(x = a ∨ x = b) ∨ bet3 a b x"
    by (metis ax_ord_2 ax_ord_3 bet3_def one_of_three_def)
next
  assume "(x = a ∨ x = b) ∨ bet3 a b x"
  thus "inc_p_l x (line a b)"
  proof (elim disjE)
    assume "x = a"
    hence "inc_p_l x (line a b)"
      using assms line by auto
    thus ?thesis .
  next
    assume "x = b"
    hence "inc_p_l x (line a b)"
      using assms line by auto
    thus ?thesis .
  next
    assume "bet3 a b x"
    hence " ((bet a x b) ∧ ¬(bet b a x)  ∧  ¬(bet a b x)) ∨ (¬(bet a x b) ∧ (bet b a x)  ∧  ¬(bet a b x)) ∨ (¬(bet a x b) ∧ ¬(bet b a x)  ∧  (bet a b x))" using bet3_def[of a b x] 
      by (metis GeometryOrder.ax_ord_2 GeometryOrder_axioms one_of_three_def) 
thus "inc_p_l x (line a b)"
   proof (elim disjE)
assume "bet a x b ∧ ¬ bet b a x ∧ ¬ bet a b x"
hence "inc_p_l x (line a b)"
using assms line 
  using ax_ord_1 colinear_def line_equality by blast
  thus ?thesis.

next
assume " ¬ bet a x b ∧ bet b a x ∧ ¬ bet a b x"
hence "inc_p_l x (line a b)"
using assms line 
  using ax_ord_1 colinear_def line_equality by blast
  thus ?thesis.

next
assume "¬ bet a x b ∧ ¬ bet b a x ∧ bet a b x"
hence "inc_p_l x (line a b)"
using assms line 
  using ax_ord_1 colinear_def line_equality by blast
  thus ?thesis.
qed
qed
qed

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
(* \<open>left_half_open_segment a b\<close> is set of all points between a and b, including b. *)
definition left_half_open_segment :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "left_half_open_segment a b = {c. bet a c b} \<union> {b}"

(* mi19009_Mina Cerovic FORMULACIJA *)
(* \<open>right_half_open_segment a b\<close> is set of all points between a and b, including a. *)
definition right_half_open_segment :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "right_half_open_segment a b = {c. bet a c b} \<union> {a}"

(* mi19009_Mina Cerovic FORMULACIJA *)
(* \<open>segment a b\<close> is set of all points between a and b, including a and b. *)
definition segment :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "segment a b = {c. bet a c b} \<union> {a} \<union> {b}"

(* mi19009_Mina Cerovic FORMULACIJA *)
(* \<open>exactly_one a b\<close> is true if exactly one of a b is true*)
definition exactly_one :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "exactly_one a b \<longleftrightarrow> (a \<and> \<not>b) \<or> (\<not>a \<and> b)"

theorem t3_1:
  assumes "c \<in> open_segment a b" and "c \<noteq> d"
  shows "d \<in> open_segment a b \<longleftrightarrow> exactly_one (d \<in> open_segment a c) (d \<in> open_segment c b)" 
  sorry
 
(* mi19009_Mina Cerovic FORMULACIJA *)
theorem t3_2:
  fixes a b c :: 'a
  assumes "colinear a b c" 
  shows "open_segment a b \<inter> open_segment b c = {} \<longleftrightarrow> bet a b c"
  sorry

(* mi19009_Mina Cerovic FORMULACIJA *)
(* Given points (A1,A2,...,An), if Ai between Ai-1 and Ai+1 for all i\<in>[2, n-1], then \<open>linear_arrangement [A1,...,An]\<close>*)
fun linear_arrangement :: "'a list \<Rightarrow> bool" where
  "linear_arrangement [] = True" |
  "linear_arrangement [a] = True" |
  "linear_arrangement [a, b] = True" |
  "linear_arrangement (a # b # c # l) \<longleftrightarrow> (bet a b c) \<and> linear_arrangement (b # c # l)"

(*mi16407_Nevena_Radulovic FORMULACIJA *)
(*\<open>all_open_segments a\<close> is a list of open segments created from consecutive points in list a*)
fun all_open_segments::"'a list\<Rightarrow>'a set list" where
  "all_open_segments [] = []"
| "all_open_segments [x] = []"
| "all_open_segments [x,y] = [open_segment x y]"
| "all_open_segments (x#y#xs) = (open_segment x y) # (all_open_segments (y # xs))"

(*mi16407_Nevena_Radulovic FORMULACIJA *)
(*\<open>inc_p_open_segmenst\<close> Given point x and a list of points A, returns True if x is an element of any segment cunstructed from consecutive points of list A*)
fun inc_p_open_segments::"'a\<Rightarrow>'a list\<Rightarrow>bool" where
  "inc_p_open_segments x [] \<longleftrightarrow> False" 
| "inc_p_open_segments x [a] \<longleftrightarrow> False" 
| "inc_p_open_segments x [a,b] \<longleftrightarrow> x\<in>(open_segment a b)" 
| "inc_p_open_segments x (a1#a2#as)\<longleftrightarrow> x\<in>(open_segment a1 a2) \<or> inc_p_open_segments x (a2 # as)"

lemma "inc_p_open_segments x xs \<longleftrightarrow> (\<exists> s \<in> set (all_open_segments xs). x \<in> s)"
  by (induction xs rule: all_open_segments.induct) auto

(*mi16407_Nevena_Radulovic FORMULACIJA *)
theorem t3_3_inc:
 assumes "linear_arrangement A" "x \<notin> set A"
  shows "x \<in> open_segment (hd A) (last A) \<longleftrightarrow> inc_p_open_segments x A"
  sorry

(*mi16407_Nevena_Radulovic FORMULACIJA *)
theorem t3_3_unique:
  assumes "linear_arrangement A" "x1 \<notin> set A" "x2 \<notin> set A"
           "x1 \<in> open_segment (hd A) (last A) \<longleftrightarrow> inc_p_open_segments x1 A" 
           "x2 \<in> open_segment (hd A) (last A) \<longleftrightarrow> inc_p_open_segments x2 A"
  shows "x1=x2"
  sorry

(*mi16407_Nevena_Radulovic FORMULACIJA *)
(*\<open>colinear_points a\<close> Returns true if all points from list a are colinear*)
definition colinear_points::"'a list\<Rightarrow>bool" where
  "colinear_points A \<longleftrightarrow>(\<exists> l. \<forall>a \<in> set A. inc_p_l a l)"

(*mi16407_Nevena_Radulovic FORMULACIJA *)
(*\<open>disjoint \<close> Given set of sets of points returns true if elements are disjoint*)
definition disjoint :: "'a set set \<Rightarrow> bool" where
  "disjoint S \<equiv> \<forall> s1 \<in> S. \<forall> s2 \<in> S. s1 \<inter> s2 = {}"

(*mi16407_Nevena_Radulovic FORMULACIJA *)
(*\<open>disjoint_open_segments \<close> Given list of points of points returns true if open segments created from elements of the list are disjoint*)
definition disjoint_open_segments :: "'a list \<Rightarrow> bool" where
  "disjoint_open_segments A \<equiv> disjoint (set (all_open_segments A))"

(*mi16407_Nevena_Radulovic FORMULACIJA *)
theorem t3_4_a:
  assumes "disjoint_open_segments A" "colinear_points A"
  shows "linear_arrangement A"
  sorry

(*mi16407_Nevena_Radulovic FORMULACIJA *)
theorem t3_4_b:
  assumes "linear_arrangement A"
  shows "disjoint_open_segments A \<and> colinear_points A"
  sorry

(*mi16407_Nevena_Radulovic FORMULACIJA *)
theorem linear_arrangement_a:
  assumes "length A > 2"
  shows "linear_arrangement A \<longleftrightarrow> (\<forall> i j k::nat. i < j \<and> j < k \<and> k < (length A) \<longrightarrow> bet (A!i) (A!j) (A!k))"
  sorry

(*mi16407_Nevena_Radulovic FORMULACIJA *)
theorem linear_arrangement_b:
  assumes "length A > 2" "\<forall> i::nat. i < (length A - 2) \<and> bet (A!i) (A!(i+1)) (A!(i+2))"
  shows "linear_arrangement A"
  sorry

(*mi16407_Nevena_Radulovic FORMULACIJA *)
theorem linear_arrangement_distinct:
  assumes "linear_arrangement A"
  shows "distinct A"
  sorry

(*mi16407_Nevena_Radulovic FORMULACIJA *)
(*\<open>colinear_points_set a\<close> Returns true if all points from set a are colinear*)
definition colinear_points_set::"'a set\<Rightarrow>bool" where
"colinear_points_set A \<longleftrightarrow>(\<exists> l::'b. \<forall>a::'a\<in>A. inc_p_l a l)"

(*mi16407_Nevena_Radulovic FORMULACIJA *)
theorem t3_5:
  assumes "colinear_points_set A" "card A > 3"
  shows "\<exists> x y::'a list. x\<noteq>y \<and> set x=A \<and> set y=A \<and> linear_arrangement x \<and> linear_arrangement y \<and>
       \<not>(\<exists> z::'a list. z\<noteq>x \<and> z\<noteq>y \<and> set z = A \<and> linear_arrangement z)"
  sorry

(*mi18107 Lidija Djalovic FORMULACIJA  *)    
(*<convex> : the set F is convex if every two points A B from the set and points along AB belong to F *)
definition convex :: "'a set => bool" where
"convex F \<equiv> (\<forall> a \<in> F. \<forall> b \<in> F. \<forall> c \<in> segment a b. c \<in> F)"

(*mi18107 Lidija Djalovic FORMULACIJA  *)
theorem t3_6_aux:
  assumes "convex A" "convex B"
  shows "convex (A \<inter> B)"
  sorry

(*mi18107 Lidija Djalovic FORMULACIJA  *)
theorem t3_6:
  assumes "\<forall> F \<in> G. convex F"
  shows "convex (\<Inter> G)"
  sorry

(*mi18107 Lidija Djalovic FORMULACIJA  *)
(*< polygon_line> : function creates a set from a list of points that forms a polygon line  *)
fun polygon_line :: "'a list \<Rightarrow> 'a set" where
  "polygon_line [] = {}"
| "polygon_line [x] = {x}"
| "polygon_line (a # b # xs) = {a} \<union> (open_segment a b) \<union> polygon_line (b # xs)"

(*mi18107 Lidija Djalovic FORMULACIJA  *)
(*<polygon> :polygon represents the union of the polygon line of list A and open along the first and last points of the polygon line
  - we assume that no three points are collinear  *)
definition polygon :: "'a list \<Rightarrow> 'a set" where
  "polygon A \<equiv> (open_segment (hd A) (last A)) \<union> polygon_line A"
   
(*mi18107 Lidija Djalovic FORMULACIJA  *)
(*<triangle>: polygon formed by three points*)
definition triangle :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "triangle a b c \<equiv> polygon [a, b, c]"

(*mi18107 Lidija Djalovic FORMULACIJA  *)
(*<quadrilateral>: polygon formed by four points*)
definition quadrilateral :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "quadrilateral a b c d \<equiv> polygon [a, b, c, d]"

(*mi18107 Lidija Djalovic FORMULACIJA  *)
(* <simple_polygon_line> : for a given list of points, we check whether it forms a simple polygonal line *)
fun simple_polygon_line :: "'a list \<Rightarrow> bool" where 
  "simple_polygon_line [] = True"
| "simple_polygon_line [a] = True" 
| "simple_polygon_line (a # b # A) = ((open_segment a b \<inter> polygon_line (b # A)) = {} \<and> simple_polygon_line (b # A)) "

(*mi18107 Lidija Djalovic FORMULACIJA  *)
(* <simple_polygon> : for a given list of points, we define a simple polygon using the simple_polygon_line function*)
definition simple_polygon :: "'a list \<Rightarrow> bool" where
  "simple_polygon A \<equiv> (((open_segment (hd A) (last A)) \<inter> polygon_line A) = {}) \<and> simple_polygon_line A  "

definition connected_points :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "connected_points a b F \<equiv> \<exists> A. a = hd A \<and> b = last A \<and> (\<forall> x \<in> polygon_line A. x \<in> F)"

definition connected_figure :: "'a set \<Rightarrow> bool" where
  "connected_figure F \<equiv> \<forall> a \<in> F. \<forall> b \<in> F. connected_points a b F"

lemma convex_connected:
  assumes "convex F"
  shows "connected_figure F"
  using assms
  unfolding connected_figure_def connected_points_def convex_def
  by (meson GeometryOrder.linear_arrangement.simps(3) GeometryOrder_axioms distinct_length_2_or_more linear_arrangement_distinct)

lemma t3_7:
  assumes "c \<in> open_segment a b"
  shows "open_segment a b - {c} = open_segment a c \<union> open_segment c b"
  using assms
  unfolding open_segment_def
  by (meson GeometryOrder.linear_arrangement.simps(3) GeometryOrder_axioms distinct_length_2_or_more linear_arrangement_distinct)

lemma t3_8:
  assumes "linear_arrangement A" "a = hd A" "b = last A"
  shows "open_segment a b - set A = fold (\<union>) (all_open_segments A) {}"
  using assms
  by (meson GeometryOrder.linear_arrangement.simps(3) GeometryOrder_axioms distinct_length_2_or_more linear_arrangement_distinct)

(*mi20357_Jelena_Mitrovic_FORMULACIJA  *)
definition point_of_same_side :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"point_of_same_side x a b \<equiv> colinear x a b \<and> \<not> bet a x b"

(*mi20357_Jelena_Mitrovic_FORMULACIJA  *)
definition point_not_of_same_side :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"point_not_of_same_side x a b \<equiv> bet a x b"

(*mi20357_Jelena_Mitrovic_FORMULACIJA  *)
theorem  point_of_same_side_reflexivity:
  shows "point_of_same_side x a a"
  sorry

(*mi20357_Jelena_Mitrovic_FORMULACIJA  *)
theorem  point_of_same_side_symmetry:
  assumes "point_of_same_side x a b "
  shows "point_of_same_side x b a"
  sorry

(*mi20357_Jelena_Mitrovic_FORMULACIJA  *)
theorem point_of_same_side_transitivity:
  assumes "point_of_same_side x a b \<and> point_of_same_side x b c"
  shows "point_of_same_side x a c"
  sorry

(*mi20357_Jelena_Mitrovic_FORMULACIJA  *)
definition complement_half_line :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "complement_half_line x a = {b. point_not_of_same_side x a b}"

(*mi20357_Jelena_Mitrovic_FORMULACIJA  *)
theorem t4_2:
assumes "\<forall>p \<in> set(lp). inc_l_p p l "
shows "points_on_line l - (set lp) = {a \<in> points_on_line l. \<not> bet (hd lp) a (last lp)  \<and> a \<noteq> hd lp \<and> a \<noteq> last lp} \<union> fold (\<union>) (all_open_segments lp) {} " 
  sorry

(*mi19167_Ivana_Neskovic_FORMULACIJA  *)
definition on_the_same_side_of_the_line :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" where
" on_the_same_side_of_the_line a b l pi = (inc_p_pl a pi \<and> inc_p_pl b pi \<and> inc_l_pl l pi \<and>
 \<not>( inc_p_l a l) \<and> \<not> (inc_p_l b l) \<and> (\<nexists>x. x \<in> points_on_line l \<and> x \<in> segment a b)) "

(*mi19167_Ivana_Neskovic_FORMULACIJA  *)
definition  on_the_different_sides_of_the_line::  "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" where
" on_the_different_sides_of_the_line a b l pi = (inc_p_pl a pi \<and> inc_p_pl b pi \<and> inc_l_pl l pi \<and>
 (\<exists>x. x \<in> points_on_line l \<and> x \<in> segment a b) )"


(*mi19167_Ivana_Neskovic_FORMULACIJA  *)
theorem  on_the_same_side_of_the_line_reflexivity:
  shows " on_the_same_side_of_the_line a a l pi"
  sorry

(*mi19167_Ivana_Neskovic_FORMULACIJA  *)
theorem   on_the_same_side_of_the_line_symmetry:
  assumes " on_the_same_side_of_the_line a b l pi  "
  shows " on_the_same_side_of_the_line b a l pi "
  sorry

(*mi19167_Ivana_Neskovic_FORMULACIJA  *)
theorem  on_the_same_side_of_the_line_transitivity:
  assumes " on_the_same_side_of_the_line a b l pi \<and>  on_the_same_side_of_the_line b c l pi"
  shows " on_the_same_side_of_the_line a c l pi"
  sorry

(*mi19167_Ivana_Neskovic_FORMULACIJA  *)
definition open_half_plane :: "'b \<Rightarrow> 'a \<Rightarrow> 'a set" where
"open_half_plane l a = {c. \<forall> b \<in> points_on_line l. bet b c a \<or> bet b a c}"

(*mi19167_Ivana_Neskovic_FORMULACIJA  *)
theorem t4_4: 
  assumes "  on_the_different_sides_of_the_line a b l pi"
  shows "(\<exists>x. x \<in> open_segment a b   \<and>  x\<in> points_on_line l ) "
  sorry


(*mi19082_Tamara_Stamatovic_FORMULACIJA*)
definition complement_half_plane :: "'b \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "complement_half_plane l a = {c. \<forall> b \<in> points_on_line l. bet a b c}"


(*mi19082_Tamara_Stamatovic_FORMULACIJA*)
definition on_the_same_side_of_the_plane :: "'a \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool" where
 "on_the_same_side_of_the_plane a b pi = ((\<not>inc_p_pl a pi \<and> \<not>inc_p_pl b pi) \<and> (a \<noteq> b) \<and> (\<nexists> x. x \<in> points_on_plane pi \<and> x \<in> segment a b) )"


(*mi19082_Tamara_Stamatovic_FORMULACIJA*)
definition on_the_different_sides_of_the_plane :: "'a \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool" where
 "on_the_different_sides_of_the_plane a b pi = ((\<not>inc_p_pl a pi \<and> \<not>inc_p_pl b pi) \<and> (a \<noteq> b) \<and> (\<exists> x. x \<in> points_on_plane pi \<and> x \<in> segment a b) )"


(*mi19082_Tamara_Stamatovic_FORMULACIJA*)
theorem  on_the_same_side_of_the_plane_reflexivity:
  shows "on_the_same_side_of_the_plane a a pi"
  sorry

(*mi19082_Tamara_Stamatovic_FORMULACIJA*)
theorem on_the_same_side_of_the_plane_symmetry:
  assumes "on_the_same_side_of_the_plane a b pi"
  shows "on_the_same_side_of_the_plane b a pi"
  sorry

(*mi19082_Tamara_Stamatovic_FORMULACIJA*)
theorem on_the_same_side_of_the_plane_transitivity:
  assumes "on_the_same_side_of_the_plane a b pi \<and> on_the_same_side_of_the_plane b c pi"
  shows "on_the_same_side_of_the_plane a c pi"
  sorry


(*mi19082_Tamara_Stamatovic_FORMULACIJA*)
definition open_half_space:: "'c \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "open_half_space pi a = {c. \<forall> b \<in> points_on_plane pi. a = c \<or> b = c \<or> on_the_same_side_of_the_plane b c pi}"

(*mi19432_Marko_Bekonja_FORMULACIJA *)
definition complement_half_space::"'c \<Rightarrow> 'a \<Rightarrow> 'a set" where
"complement_half_space pi A = {x. on_the_different_sides_of_the_plane x A pi}"
                                                                              
(*mi19432_Marko_Bekonja_FORMULACIJA *)
definition angle_line::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
"angle_line A C B = half_line C A \<union> half_line C B"

(*mi19432_Marko_Bekonja_FORMULACIJA *)
definition on_the_same_side_of_the_angle_line::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"on_the_same_side_of_the_angle_line x y a b c \<equiv> \<exists>p. x = hd p \<and> y = last p \<and>
  polygon_line p \<subset> points_on_plane (plane a b c) \<and> (polygon_line p \<inter> angle_line a b c) = {}"

(*mi19432_Marko_Bekonja_FORMULACIJA *)
definition on_the_different_sides_of_the_angle_line::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"on_the_different_sides_of_the_angle_line x y a b c \<equiv> \<not> (on_the_same_side_of_the_angle_line x y a b c)"

(*mi19432_Marko_Bekonja_FORMULACIJA *)
lemma on_the_same_side_of_the_angle_line_reflexivity:
  shows "on_the_same_side_of_the_angle_line x x a b c"
  sorry

(*mi19432_Marko_Bekonja_FORMULACIJA *)
lemma on_the_same_side_of_the_angle_line_symmetry:
  assumes "on_the_same_side_of_the_angle_line x y a b c"
  shows "on_the_same_side_of_the_angle_line y x a b c"
  sorry

(*mi19432_Marko_Bekonja_FORMULACIJA *)
lemma on_the_same_side_of_the_angle_line_transitivity:
  assumes "on_the_same_side_of_the_angle_line x y a b c" 
      and "on_the_same_side_of_the_angle_line y z a b c"
    shows "on_the_same_side_of_the_angle_line x z a b c"
  sorry

(*mi19096_Vladimir_Jovanovic_FORMULACIJA*)
definition open_angle :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "open_angle A B C Y \<equiv> {X. on_the_same_side_of_the_angle_line X Y A B C }"

(*mi19096_Vladimir_Jovanovic_FORMULACIJA*)
definition closed_angle :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "closed_angle A B C Y \<equiv> open_angle A B C Y \<union> (half_line C A) \<union> (half_line C B)"

(*mi19096_Vladimir_Jovanovic_FORMULACIJA*)
definition complement_angle :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "complement_angle A B C Y \<equiv> {X. on_the_different_sides_of_the_angle_line X Y A B C}"

(*mi19096_Vladimir_Jovanovic_FORMULACIJA*)
theorem t5_2:
  assumes "coplanar P Q X B"
      and "distinct [P, Q, X, B]"
      and "A \<in> (angle_line P X Q)"
      and "B \<notin> (angle_line P X Q)"
    shows "\<exists>p. A = hd p \<and> B = last p \<and> polygon_line p \<subset> points_on_plane (plane P Q X) \<and> (polygon_line p \<inter> complement_angle P X Q B) = {}" 
  using assms
  sorry

(*mi19096_Vladimir_Jovanovic_FORMULACIJA*)
theorem t5_3:
  assumes "X \<in> complement_angle A B C Y "
    shows "complement_angle A B X Y \<union> complement_angle X B C Y \<union> half_line B X = complement_angle A B C Y"
  using assms
  sorry

(* mi19087_Andrijana_Bosiljcic_FORMULACIJA *)
(* \<open>intersects_l_os\<close> \<rightarrow> do line and open_segment have intersection. *)
definition intersects_l_os :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"intersects_l_os l a b \<equiv> (\<exists> x . inc_p_l x l \<and> x \<in> (open_segment a b))"

(* mi19087_Andrijana_Bosiljcic_FORMULACIJA *)
(* \<open>intersection_l_os\<close> is a point where line and open_segment intersect *)
definition intersection_l_os :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"intersection_l_os l a b \<equiv> (THE x . inc_p_l x l \<and> x \<in> (open_segment a b))"

(* mi19087_Andrijana_Bosiljcic_FORMULACIJA *)
theorem t5_6:
  assumes "convex (angle_line A T B)" and
          "P \<in> (half_line T A) \<and> Q \<in> (half_line T B)"
  shows "(\<forall> x \<in> (half_line T C). x \<in> (angle_line A T B)) \<longleftrightarrow> 
         (\<exists> y . y \<in> (half_line T C) \<and> y \<in> (open_segment P Q))"
  using assms
  sorry

(* mi19087_Andrijana_Bosiljcic_FORMULACIJA *)
definition point_segment_span :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
"point_segment_span a b c = {x . \<forall>y \<in> (segment b c) . x \<in> (points_on_line (line a y))}"

(* mi19087_Andrijana_Bosiljcic_FORMULACIJA *)
theorem t5_8:
  assumes "\<not> (colinear A B C)"
  shows "inc_p_pl D (plane A B C) \<longleftrightarrow> D \<in> point_segment_span A B C \<or> D \<in> point_segment_span B C A \<or> D \<in> point_segment_span C A B"
  using assms
  sorry



(*mi18147_Andjela_Stajic_FORMULACIJA*)
definition diedral_surface :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a set" where
"diedral_surface a b l \<equiv> half_plane l a \<union> half_plane l b"

(*mi18147_Andjela_Stajic_FORMULACIJA*)
definition on_the_same_side_of_diedral_surface :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" where
"on_the_same_side_of_diedral_surface x y a b l \<equiv> 
(\<exists>p. (x = hd p) \<and> (y = last p) \<and> (polygon_line p \<inter> (diedral_surface a b l) = {}))"

(*mi18147_Andjela_Stajic_FORMULACIJA*)
definition on_opposite_sides_of_diedral_surface :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" where
"on_opposite_sides_of_diedral_surface x y a b l \<equiv> \<not> on_the_same_side_of_diedral_surface x y a b l"

(*mi18147_Andjela_Stajic_FORMULACIJA*)
lemma on_the_same_side_reflexivity:
  shows "on_the_same_side_of_diedral_surface x x a b l"
  sorry

lemma on_the_same_side_symmetry:
  assumes "on_the_same_side_of_diedral_surface x y a b l"
  shows "on_the_same_side_of_diedral_surface y x a b l"
  sorry

lemma on_the_same_side_transitivity:
  assumes "on_the_same_side_of_diedral_surface x y a b l" 
      and "on_the_same_side_of_diedral_surface y z a b l"
    shows "on_the_same_side_of_diedral_surface x z a b l"
  sorry

(*mi18147_Andjela_Stajic_FORMULACIJA*)
definition open_diedra :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a set" where
"open_diedra y a b l = {x. on_the_same_side_of_diedral_surface x y a b l}"
end

section \<open>Axioms of Congruence\<close>

locale GeometryCongruence = GeometryOrder +
    fixes cng :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (* Given points a b c d, if [a, b] is congruent to [c, d] then \<open>cng a b c d\<close>.*)
  assumes ax_cng_1: "\<And> a b c. cng a a b c \<Longrightarrow> b = c"
      and ax_cng_2: "\<And> a b. cng a b b a"
      and ax_cng_3: "\<And> a b c d e f. \<lbrakk>cng a b c d; cng a b e f\<rbrakk> \<Longrightarrow> cng c d e f"
      and ax_cng_4: "\<And> a b a' b' c c'. \<lbrakk>c \<in> open_segment a b; c' \<in> open_segment a' b'; cng a c a' c'; cng b c b' c'\<rbrakk> \<Longrightarrow> cng a b a' b'"
      and ax_cng_5: "\<And> a b c p. \<lbrakk>p \<in> half_lines_origin c; a \<noteq> b\<rbrakk> \<Longrightarrow> (\<exists>! d \<in> p. cng a b c d)"      
      and ax_cng_6: "\<And> a b c a' b' P. \<lbrakk>P \<in> half_planes_boundary (line a' b'); a' \<noteq> b'; \<not> colinear a b c; cng a b a' b'\<rbrakk> \<Longrightarrow> (\<exists>! c' \<in> P. cng a c a' c' \<and> cng b c b' c')"
      and ax_cng_7: "\<And> a b c a' b' c' d d'. 
                        \<lbrakk>d \<in> half_line b c; d' \<in> half_line b' c'; 
                         b \<noteq> c; b' \<noteq> c'; 
                         \<not> colinear a b c; \<not> colinear a' b' c';
                         cng a b a' b'; cng b c b' c'; cng c a c' a'; cng b d b' d'\<rbrakk> \<Longrightarrow> cng a d a' d'"
begin

end

section \<open>Axioms of Continuity\<close>

end
