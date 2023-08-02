theory GeoCongruence
  imports Main GeoOrder
begin


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
  assumes "p \<in> half_lines_origin c" "a \<noteq> b"
  shows "\<exists>! d. d \<in> line_points p \<and> cng a b c d"
  sorry


(* mi16069_Svetozar_Ikovic_FORMULACIJA *)
theorem t10_3:
  assumes
    "a \<noteq> b" "b \<noteq> c" "c \<noteq> a"
    "a \<in> line_points l" "b \<in> line_points l" "c \<in> line_points l"
    "ap \<in> line_points lp" "bp \<in> line_points lp"
    "cng a b ap bp"
  shows "\<exists>! cp.
    cng a c ap cp
\<and>   cng b c bp cp
\<and>   cp \<in> line_points lp
\<and>   (bet a b c \<longleftrightarrow> bet ap bp cp)
\<and>   (bet b c a \<longleftrightarrow> bet bp cp ap)
\<and>   (bet c a b \<longleftrightarrow> bet cp ap bp)
"
  sorry


(* mi16069_Svetozar_Ikovic_FORMULACIJA *)
definition cng_3 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "cng_3 a1 a2 a3 a1p a2p a3p \<equiv> (cng a1 a2 a1p a2p) \<and> (cng a2 a3 a2p a3p) \<and> (cng a3 a1 a3p a1p)"


(* mi16069_Svetozar_Ikovic_FORMULACIJA *)
definition cng_4 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "cng_4 a1 a2 a3 a4 a1p a2p a3p a4p \<equiv>
  (cng a1 a2 a1p a2p)
\<and> (cng a1 a3 a1p a3p)
\<and> (cng a1 a4 a1p a4p)
\<and> (cng a2 a3 a2p a3p)
\<and> (cng a2 a4 a2p a4p)
\<and> (cng a3 a4 a3p a4p)
"


(* mi16069_Svetozar_Ikovic_FORMULACIJA *)
definition cng_n :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "cng_n a b \<equiv>
  (length a = length b) \<and> (
    \<forall> i < length a. \<forall> j < length a.
    cng (a ! i) (a ! j) (b ! i) (b ! j)
  )
"


(* mi16069_Svetozar_Ikovic_FORMULACIJA *)
definition podudarni :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "podudarni a b \<equiv> cng_n a b"


(* mi16987_Mihajlo_Zivkovic_FORMULACIJA *)
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


(* mi16987_Mihajlo_Zivkovic_FORMULACIJA *)
theorem t10_5:
  assumes "\<not> coplanar a b c d"
    and "cng_4 a b c d a' b' c' d'"
  shows "\<exists>! x'.  cng_n [a, b, c, d, x] [a', b', c', d', x']
        \<and> ((same_side_pl (plane a b c) x d \<and> same_side_pl (plane b c d) x a \<and> same_side_pl (plane c d a) x b \<and> same_side_pl (plane d a b) x c) 
                        \<longleftrightarrow> (same_side_pl (plane a' b' c') x' d' \<and> same_side_pl (plane b' c' d') x' a' \<and> same_side_pl (plane c' d' a') x' b' \<and> same_side_pl (plane d' a' b') x' c'))"
  sorry

(* mi16987_Mihajlo_Zivkovic_FORMULACIJA *)
definition inj :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
"inj f \<equiv> (\<forall>x1 x2. f x1 = f x2 \<longrightarrow> x1 = x2)"

(* mi16987_Mihajlo_Zivkovic_FORMULACIJA *)
definition surj :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
"surj f \<equiv> (\<forall>y. \<exists>x. f x = y)"

(* mi16987_Mihajlo_Zivkovic_FORMULACIJA *)
definition bij :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
"bij f \<equiv> inj f \<and> surj f
"
(* mi16987_Mihajlo_Zivkovic_FORMULACIJA *)
definition isometry_space :: "('a => 'a) => bool" where
"isometry_space f \<equiv> bij f \<and> (\<forall> a b. cng a b (f a) (f b))"

(* mi16987_Mihajlo_Zivkovic_FORMULACIJA *)
definition isometry_line :: "('a => 'a) => bool" where
"isometry_line f \<equiv> bij f \<and> (\<forall> a b. cng a b (f a) (f b) \<and> colinear_set {a ,b, (f a), (f b)})"

(* mi16987_Mihajlo_Zivkovic_FORMULACIJA *)
definition isometry_plane :: "('a => 'a) => bool" where
"isometry_plane f \<equiv> bij f \<and> (\<forall> a b. cng a b (f a) (f b) \<and> coplanar_set {a, b, (f a), (f b)})"

end


end