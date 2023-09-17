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

end




(*mi19218_Luka_Bura_FORMULACIJA *)
definition image_of_line :: "('a => 'a) => ('a => bool) => ('a => bool)" where
"image_of_line f l a = (\<exists> b. l b \<and> f b = a)"

(*mi19218_Luka_Bura_FORMULACIJA *)
theorem t10_7a: 
  assumes "isometry_line J I"
  shows "\<forall> a. inc_p_l a I \<longrightarrow> inc_p_l (J a) (image_of_line J I)"
  sorry

(*mi19218_Luka_Bura_FORMULACIJA *)
definition image_of_half_line :: "('a => 'a) => ('a => bool) => ('a => bool)" where
"image_of_half_line f hl a = (\<exists> b. hl b \<and> f b = a)"

(*mi19218_Luka_Bura_FORMULACIJA *)
theorem t10_7b: 
  assumes "isometry_line J I"
    and "origin \<in> I" and "half_lines_origin origin = hl"
  shows "\<forall> P. P \<in> hl \<longrightarrow> J(P) \<in> Collect (image_of_half_line J (\<lambda>x. x \<in> hl)) \<and> J(origin) = origin"
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









end