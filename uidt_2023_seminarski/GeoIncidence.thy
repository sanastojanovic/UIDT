theory GeoIncidence
imports Main
begin

chapter \<open>Incidence\<close>

section \<open>Axioms of incidence\<close>

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
  "colinear a b c \<equiv> \<exists> l. inc_p_l a l \<and> inc_p_l b l \<and> inc_p_l c l"

(* If points a, b, c, and d are incident to some plane P, then \<open>coplanar a b c d\<close>. *)
definition coplanar :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "coplanar a b c d \<equiv> \<exists> P. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P \<and> inc_p_pl d P"

(* Given line l and plane P, if l is incident to P then inc_l_pl l P *)
definition inc_l_pl :: "'b \<Rightarrow> 'c \<Rightarrow> bool" where
  "inc_l_pl l P \<equiv> \<forall> a. inc_p_l a l \<longrightarrow> inc_p_pl a P"

(* \<open>line_points\<close> is set of all points that are incident to line l. *)
definition line_points :: "'b  \<Rightarrow> 'a set" where
  "line_points l = {a. inc_p_l a l}"

(* \<open>plane_points\<close> is set of all points that are incident to plane P. *)
definition plane_points :: "'c  \<Rightarrow> 'a set" where
  "plane_points P = {a. inc_p_pl a P}"

(*mi16407_Nevena_Radulovic FORMULACIJA *)
(*\<open>colinear_set a\<close> Returns true if all points from a set a are colinear*)
definition colinear_set :: "'a set \<Rightarrow> bool" where
  "colinear_set A \<longleftrightarrow>(\<exists> l. \<forall>a \<in> A. inc_p_l a l)"

(*mi16407_Nevena_Radulovic FORMULACIJA *)
(* \<open>colinear_n a\<close> Returns true if all points from a list a are colinear *)
definition colinear_n :: "'a list \<Rightarrow> bool" where
  "colinear_n as \<longleftrightarrow> colinear_set (set as)"

definition coplanar_set :: "'a set \<Rightarrow> bool" where
  "coplanar_set A \<longleftrightarrow> (\<exists> pl. \<forall> a \<in> A. inc_p_pl a pl)"
end

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

section \<open>Consequences of axioms of incidence\<close>

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

lemma inc_trans:
  assumes "inc_l_pl l P" "inc_p_l a l"
  shows "inc_p_pl a P"
  using assms
  using inc_l_pl_def
  by blast

lemma t1_3':
  assumes "colinear a b c" "a \<noteq> b"
  shows "coplanar a b c d"
proof-
  from assms obtain p :: 'b where "inc_p_l a p" and "inc_p_l b p" and "inc_p_l c p"
    using ax_inc_2 colinear_def by blast
  then obtain P :: 'c where "inc_p_pl a P" and "inc_p_pl b P" and "inc_p_pl d P" 
    using ax_inc_5 by blast
  with `a \<noteq> b` have "inc_l_pl p P" using ax_inc_7 
    by (simp add: \<open>inc_p_l a p\<close> \<open>inc_p_l b p\<close> \<open>inc_p_pl a P\<close> \<open>inc_p_pl b P\<close>)
  then show "coplanar a b c d" 
    using \<open>inc_p_l c p\<close> \<open>inc_p_pl a P\<close> \<open>inc_p_pl b P\<close> \<open>inc_p_pl d P\<close> coplanar_def inc_trans by blast
qed
  
theorem t1_3:
  assumes "\<not> coplanar a b c d"
  shows "\<not> colinear a b c" "\<not> colinear a b d" "\<not> colinear a c d" "\<not> colinear b c d"
proof -
  have *: "distinct [a, b, c, d]"
    using assms
    using t1_2 by blast
  
  show "\<not> colinear a b c"
    using assms * t1_3'[of a b c d]
    by auto

  show "\<not> colinear a b d"
    using assms * t1_3'[of a b d c]
    unfolding coplanar_def
    by auto

  show "\<not> colinear a c d"
    using assms * t1_3'[of a c d b]
    unfolding coplanar_def
    by auto

  show "\<not> colinear b c d"
    using assms * t1_3'[of b c d a]
    unfolding coplanar_def
    by auto
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

(* \<open>line a b\<close> is line that is defined by two points a and b. (Use under assumption: a \<noteq> b!) *)
definition line :: "'a \<Rightarrow> 'a \<Rightarrow> 'b" where
  "line a b \<equiv> THE l. inc_p_l a l \<and> inc_p_l b l"

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
(* mi19432_Marko_Bekonja_DOKAZ *)
theorem t1_7:
  assumes "\<not> colinear a b c"
  shows "\<exists>! P. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P"
  using assms(1) ax_inc_5 ax_inc_6 by auto

(* \<open>plane a b c\<close> is plane that is defined by three points a, b, and c. (Use under assumption: \<not> colinear a b c \<and> a \<noteq> b \<and> b \<noteq> c \<and> c \<noteq> a!) *)
definition plane :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'c" where
  "plane a b c \<equiv> THE P. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P"

lemma plane_a:
  assumes "\<not> colinear a b c" 
  shows "inc_p_pl a (plane a b c)"
  unfolding plane_def
  using t1_7[OF assms]
  by (smt (verit, del_insts) theI)

lemma plane_b:
  assumes "\<not> colinear a b c"
  shows "inc_p_pl b (plane a b c)"
  unfolding plane_def
  using t1_7[OF assms]
  by (smt (verit, del_insts) theI)  

lemma plane_c:
  assumes "\<not> colinear a b c"
  shows "inc_p_pl c (plane a b c)"
  unfolding plane_def
  using t1_7[OF assms]
  by (smt (verit, del_insts) theI)  

lemma plane:
  assumes "\<not> colinear a b c" 
  shows "inc_p_pl a (plane a b c) \<and> inc_p_pl b (plane a b c) \<and> inc_p_pl c (plane a b c)"
  using plane_a[OF assms] plane_b[OF assms] plane_c[OF assms]
  by simp

lemma plane_equality:
  assumes "\<not> colinear a b c"
      and "inc_p_pl a P" "inc_p_pl b P" "inc_p_pl c P"
    shows "P = plane a b c"
  unfolding plane_def
  using t1_7[OF assms(1)] assms
  using plane plane_def by auto
  

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
(* \<open>plane_p_l\<close> \<rightarrow> plane that is defined by line and point that doesn't belongs to that line. (Use under assumption: \<not> (inc_p_l a p) *)
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
(* mi20357_Jelena_Mitrovic_DOKAZ*)
theorem t1_8:
  assumes "\<not> inc_p_l a p"
  shows "\<exists>! P. inc_l_pl p P \<and> inc_p_pl a P"
  using assms
  using plane_p_l_unique
  by blast

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
(* \<open>intersecing_l_l\<close> \<rightarrow> do two lines have intersection. *)
definition intersecting_lines :: "'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "intersecting_lines p q \<equiv> (\<exists> a. inc_p_l a p \<and> inc_p_l a q)"

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
(* \<open>plane_ll\<close> \<rightarrow> plane that is defined by two lines that initersect. (Use under assumption: p \<noteq> q \<and> intersects p q) *)
definition plane_l_l :: "'b \<Rightarrow> 'b \<Rightarrow> 'c" where
  "plane_l_l p q \<equiv> THE P. inc_l_pl p P \<and> inc_l_pl q P"

(* mi17261_Tamara_Jevtimijevic_FORMULACIJA *)
(* mi19432_Marko_Bekonja_DOKAZ *)
theorem t1_9:
  assumes "intersecting_lines p q" and "p \<noteq> q"
  shows "\<exists>! P. inc_l_pl p P \<and> inc_l_pl q P"
proof-
  from assms(1) have "\<exists>a. inc_p_l a p \<and> inc_p_l a q" using intersecting_lines_def by auto
  from this obtain a where *:"inc_p_l a q \<and> inc_p_l a p" by auto
  from assms(2) have "\<exists>b. inc_p_l b p \<and> \<not>inc_p_l b q" using ax_inc_1 ax_inc_3 by blast
  from this obtain b where **:"inc_p_l b p \<and> \<not>inc_p_l b q" by auto
  from assms(2) have "\<exists>c. inc_p_l c q \<and> \<not>inc_p_l c p" using ax_inc_1 ax_inc_3 by blast
  from this obtain c where ***:"inc_p_l c q \<and> \<not>inc_p_l c p" by auto
  from * ** *** have ****:"\<not> colinear a b c" by (metis colinear_def t1_6)
  from * ** *** have razlicite:"a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c" by auto
  from this and t1_7 and **** have "\<exists>!P. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P" by auto
  from this obtain P where tacke_ravan:"inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P" by auto
  from * ** have tacke_prava1:"inc_p_l a p \<and> inc_p_l b p" by auto
  from * *** have tacke_prava2:"inc_p_l a q \<and> inc_p_l c q" by auto
  from tacke_ravan and tacke_prava1 and razlicite and ax_inc_7 have "inc_l_pl p P" by auto
  from tacke_ravan and tacke_prava2 and razlicite and ax_inc_7 have "inc_l_pl q P" by auto
  from this and \<open>inc_l_pl p P\<close> have "inc_l_pl p P \<and> inc_l_pl q P" by auto
  from this show "\<exists>! P. inc_l_pl p P \<and> inc_l_pl q P" by (metis "**" inc_trans plane_p_l_unique)
qed

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

(* mi17122_Tamara_Tomic_FORMULACIJA *)
(* \<open>intersection p q\<close> is a point where two lines intersect (Use under assumption: p \<noteq> q) *)
definition intersection_l_l :: "'b \<Rightarrow> 'b \<Rightarrow> 'a" where
  "intersection_l_l p q \<equiv> THE a. inc_p_l a p \<and> inc_p_l a q"

(* mi17122_Tamara_Tomic_FORMULACIJA *)
(* mi19432_Marko_Bekonja_DOKAZ *)
theorem t1_11:
  assumes "p \<noteq> q" "inc_p_l a p" "inc_p_l a q" "inc_p_l b p" "inc_p_l b q"
  shows "a = b"
proof (rule ccontr)
  assume "a \<noteq> b"
  from this and assms(2) assms(3) assms(4) assms(5) and ax_inc_3 have "p = q" by auto
  from this and assms(1) show "False" by auto
qed

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
(* \<open>intersection_pl_pl P Q\<close> is line that is defined as intersection of planes P and Q. (Use under assumption: P \<noteq> Q and P and Q have intersection (i.e. not parallel)!) *)
definition intersection_pl_pl :: "'c \<Rightarrow> 'c \<Rightarrow> 'b" where
  "intersection_pl_pl P Q \<equiv> THE l. inc_l_pl l P \<and> inc_l_pl l Q"

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* mi20045_Aleksandar_Zecevic_DOKAZ *)
theorem t1_13:
  assumes "P \<noteq> Q" "inc_p_pl a P" "inc_p_pl a Q"
  shows "\<exists> l. plane_points P \<inter> plane_points Q = line_points l"
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
    unfolding plane_points_def line_points_def
    by auto
qed

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* If lines in set of lines L are concurrent then \<open>concurrent_line_set L\<close>. *)
definition concurrent_line_set :: "'b set \<Rightarrow> bool" where
  "concurrent_line_set L \<equiv> \<exists> a. \<forall> l \<in> L. inc_p_l a l"

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* If lines in set of lines L are coplanar then \<open>coplanar_line_set L\<close>. *)
definition coplanar_line_set :: "'b set \<Rightarrow> bool" where
  "coplanar_line_set L \<equiv> \<exists> P. \<forall> l \<in> L. inc_l_pl l P"

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* mi20045_Aleksandar_Zecevic_DOKAZ *)
(* Auxiliary lemma for the next (1.14) theorem. *)
lemma noncoplanar_intersecting_lines:
  assumes "l\<^sub>1 \<noteq> l\<^sub>2" "inc_p_l a l\<^sub>1" "inc_p_l a l\<^sub>2"
      and "inc_l_pl l\<^sub>1 P" "inc_l_pl l\<^sub>2 P" "\<not> inc_l_pl l\<^sub>3 P"
      and "intersecting_lines l\<^sub>1 l\<^sub>3" "intersecting_lines l\<^sub>2 l\<^sub>3"
    shows "inc_p_l a l\<^sub>3"
  by (smt (verit) assms ax_inc_3 inc_l_pl_def intersecting_lines_def t1_12)

(* mi20045_Aleksandar_Zecevic_FORMULACIJA *)
(* mi20045_Aleksandar_Zecevic_DOKAZ *)
theorem t1_14:
  assumes "\<forall> l\<^sub>1 \<in> L. \<forall> l\<^sub>2 \<in> L. intersecting_lines l\<^sub>1 l\<^sub>2"
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
      by (metis assms card_2_iff' concurrent_line_set_def intersecting_lines_def)
  next
    case general
    then have "L \<noteq> {}" "card L \<noteq> 1" "card L \<noteq> 2"
      by auto
    then obtain p q where "p \<in> L" "q \<in> L" "p \<noteq> q"
      by (meson is_singletonI' is_singleton_altdef)
    obtain a where "inc_p_l a p" "inc_p_l a q"
      using \<open>p \<in> L\<close> \<open>q \<in> L\<close> assms intersecting_lines_def by blast
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
            using \<open>l \<in> L\<close> \<open>r \<in> L\<close> assms intersecting_lines_def by blast
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
end