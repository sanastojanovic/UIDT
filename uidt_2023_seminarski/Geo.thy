theory Geo
  imports Main

begin

typedecl point
typedecl line
typedecl plane

section \<open>Axioms of Incidence\<close>

locale GeometryIncidence = 
  fixes inc_p_l :: "point \<Rightarrow> line \<Rightarrow> bool" (* Given point a and line l, if a is incident to l then inc_p_l a l*)
    and inc_p_pl :: "point \<Rightarrow> plane \<Rightarrow> bool" (* Given point a and plane P, if a is incident to P then inc_p_pl a P*)
    and inc_l_pl :: "line \<Rightarrow> plane \<Rightarrow> bool" (* Given line l and plane P, if l is incident to P then inc_l_pl l P *)
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

(* If points a, b, and c are incident to some line l, then \<open>colinear a b c\<close>. *)
definition colinear :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "colinear a b c \<equiv> \<exists> l :: line. inc_p_l a l \<and> inc_p_l b l \<and> inc_p_l c l"

(* If points a, b, c, and d are incident to some plane P, then \<open>coplanar a b c d\<close>. *)
definition coplanar :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "coplanar a b c d \<equiv> \<exists> P :: plane. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P \<and> inc_p_pl d P"

subsection \<open>Three Non-Collinear Points and Four Non-Coplanar Points\<close>

subsection \<open>Lines and Planes\<close>

(* \<open>line a b\<close> is line that is defined by two points a and b. (Use under assumption: a \<noteq> b!) *)
definition line :: "point \<Rightarrow> point \<Rightarrow> line" where
  "line a b \<equiv> THE l :: line. inc_p_l a l \<and> inc_p_l b l"

(* \<open>palne a b c\<close> is plane that is defined by three points a, b, and c. (Use under assumption: a \<noteq> b \<and> b \<noteq> c \<and> c \<noteq> a!) *)
definition plane :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> plane" where
  "plane a b c \<equiv> THE P :: plane. inc_p_pl a P \<and> inc_p_pl b P \<and> inc_p_pl c P"

subsection \<open>Fundamental Existence Theorems\<close>

end

subsection \<open>Intersections of Lines and Planes\<close>

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

(* \<open>half_line a b\<close> is set of all points between a and b and all points c such that b is between a and c, including a and b. *)
definition half_line :: "point \<Rightarrow> point \<Rightarrow> point set" where
  "half_line a b = {c. c = a \<or> c = b \<or> bet a c b \<or> bet a b c}"

(* \<open>half_lines_origin a\<close> is set of all half-lines with origin a. *)
definition half_lines_origin :: "point \<Rightarrow> point set set" where
  "half_lines_origin a = {p. \<forall> b :: point. p = half_line a b}"

end

section \<open>Axioms of Congruence\<close>

locale GeometryCongruence = GeometryOrder +
    fixes cong :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" (* Given points a b c d, if [a, b] is congruent to [c, d] then \<open>cong a b c d\<close>.*)
  assumes ax_cng_1: "\<forall> a b c :: point. cong a a b c \<longrightarrow> b = c"
      and ax_cng_2: "\<forall> a b :: point. cong a b b a"
      and ax_cng_3: "\<forall> a b c d e f :: point. cong a b c d \<and> cong a b e f \<longrightarrow> cong c d e f"
      and ax_cng_4: "\<forall> a b a' b' :: point. \<forall> c \<in> open_segment a b. \<forall> c' \<in> open_segment a' b'. cong a c a' c' \<and> cong b c b' c' \<longrightarrow> cong a b a' b'"
      and ax_cng_5: "\<forall> a b c :: point. \<forall> p \<in> half_lines_origin c. a \<noteq> b \<longrightarrow> (\<exists>! d \<in> p. cong a b c d)"      
      (* nedostaje ax_cng_6 *)
      and ax_cng_7: "\<forall> a b c a' b' c' :: point. \<forall> d \<in> half_line b c. \<forall> d' \<in> half_line b' c'. \<not> colinear a b c \<and> \<not> colinear a' b' c' \<and> cong a b a' b' \<and> cong b c b' c' \<and> cong c a c' a' \<and> cong b d b' d' \<longrightarrow> cong a d a' d'"
begin

end

section \<open>Axioms of Continuity\<close>

end