theory mi16196_Sanja_Mijatovic

imports Main Complex_Main

begin

text ‹

Link: https://www.imo-official.org/problems/IMO2020SL.pdf
Algebra A3

Suppose that a, b, c, d are positive real numbers satisfying (a+c) * (b+d) = a*c + b*d.
Find the smallest possible value of a/b + b/c + c/d + d/a.

Answer: The smallest possible value is 8.

›

section ‹Prvi seminarski›

(* S = a/b + b/c + c/d + d/a
Potrebno je da pokazemo da je S ≥ 8
 *)
lemma task1:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  assumes "(a + c) * (b + d) = a*c + b*d"
  shows "a/b + b/c + c/d + d/a ≥ 8"
  using assms
  sorry

(* Kada dokazemo da je S ≥ 8, potrebno je da odredimo a, b, c i d,
   takve da je a/b + b/c + c/d + d/a = 8 i time pokazemo da je 8 najmanja vrednost. *)
lemma task2:
  fixes a b c d :: real
  shows "∃ a b c d. a/b + b/c + c/d + d/a = 8 ∧ (a + c) * (b + d) = a*c + b*d ∧
  a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0"
  sorry


section ‹Drugi seminarski (Solution 1)›

lemma AM_GM_inequality:
  fixes x y :: real
  assumes "x > 0" "y > 0" 
  shows "x + y ≥ 2 * sqrt (x*y)"
  using assms
  by (metis less_eq_real_def mult.assoc real_sqrt_mult real_sqrt_pow2 sum_squares_bound)
  
lemma AM_GM_inequality1:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  shows "a/b + c/d ≥ 2 * sqrt ((a*c)/(b*d)) "
  using assms
  by (metis divide_pos_pos AM_GM_inequality times_divide_times_eq)

lemma AM_GM_inequality2:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  shows "b/c + d/a ≥ 2 * sqrt ((b*d)/(a*c)) "
  using assms
  by (metis AM_GM_inequality1 mult.commute)

lemma p1:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  shows "(a/b + c/d) + (b/c + d/a) ≥ 2 * sqrt ((a*c)/(b*d)) +  2 * sqrt ((b*d)/(a*c)) "
  using assms
  by (smt (verit, del_insts) AM_GM_inequality1 AM_GM_inequality2)

lemma p2:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  shows "2 * sqrt ((a*c)/(b*d)) +  2 * sqrt ((b*d)/(a*c)) = 2 * (a*c + b*d) / sqrt (a*b*c*d)"
proof-
  have "2 * sqrt ((a*c)/(b*d)) +  2 * sqrt ((b*d)/(a*c)) = 2 * (sqrt ((a*c)/(b*d)) +  sqrt ((b*d)/(a*c)))"
    by simp
  also have "… = 2 * (sqrt (a*c) * sqrt (a*c)  / sqrt (a*b*c*d) + sqrt (b*d) * sqrt (b*d)  / sqrt (a*b*c*d)) "
    using assms
    using real_sqrt_divide real_sqrt_mult by fastforce
  also have "… =  2 * ((sqrt (a*c) * sqrt (a*c)  + sqrt (b*d) * sqrt (b*d))  / sqrt (a*b*c*d))"
    by (simp add: add_divide_distrib)
  also have "… = 2 * (a*c + b*d)  / sqrt (a*b*c*d)"
    using assms
    by simp
  finally show ?thesis
    by simp
qed

lemma p3:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  assumes "(a + c) * (b + d) = a*c + b*d"
  shows "2 * (a*c + b*d) / sqrt (a*b*c*d) = 2 * (a+c)*(b+d) / sqrt (a*b*c*d) "
  using assms
  by (simp add: distrib_right)

(* Nejednakost trougla *)
lemma AM_GM_inequality3:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  shows "(a+c) * (b+d) ≥ 2 * sqrt (a*c) *  2 * sqrt (b*d)"
  using assms
  by (smt (verit, ccfv_SIG) combine_common_factor distrib_left AM_GM_inequality mult_le_0_iff mult_mono' mult_nonneg_nonpos2 real_sqrt_gt_0_iff zero_le_mult_iff)


lemma p4:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  shows "2 * (a+c)*(b+d) / sqrt (a*b*c*d) ≥ 2 * (2 * sqrt (a*c) * 2 * sqrt (b*d)) / sqrt (a*b*c*d)"
proof-
  have "2 * (a+c)*(b+d) / sqrt (a*b*c*d) = 2* ((a+c)*(b+d)) / sqrt (a*b*c*d)"
    using assms
    by auto
  also have "… ≥ 2 * ( 2 * sqrt (a*c) *  2 * sqrt (b*d)) / sqrt (a*b*c*d)"
    using assms
    by (smt (verit) divide_right_mono AM_GM_inequality3 real_sqrt_ge_zero zero_le_mult_iff)
  finally show ?thesis
    by simp
qed


(* Gore navedene nejednakosti prelaze u jednakosti kada je a=c i b=d. *)

lemma p5:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  assumes "a = c" "b = d"
  shows "2 * (2 * sqrt (a*c) * 2 * sqrt (b*d)) / sqrt (a*b*c*d) = 8"
proof-
  have "2 * (2 * sqrt (a*c) * 2 * sqrt (b*d)) / sqrt (a*b*c*d) = 8 * ( sqrt (a*c) * sqrt (b*d))  / sqrt (a*b*c*d)"
    by simp
  also have "… = 8 * (sqrt (c*c) * sqrt (d*d)) / sqrt (c*c*d*d)"
    using assms
    by simp
  also have "… = 8 * (c * d) / (c*d)"
    using assms
    by (simp add: real_sqrt_mult)
  also have "… = 8"
    using assms
    by simp
  finally show ?thesis
    by simp
qed


(* Dokaz da je S = a/b + b/c + c/d + d/a ≥ 8 *)
lemma task1_dokaz:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  assumes "(a + c) * (b + d) = a*c + b*d"
  shows "a/b + b/c + c/d + d/a ≥ 8"
proof-
  have "a/b + b/c + c/d + d/a = (a/b + c/d) + (b/c + d/a)"
    by simp
  then have "a/b + b/c + c/d + d/a  ≥ 2 * sqrt ((a*c)/(b*d)) +  2 * sqrt ((b*d)/(a*c))"
    using assms
    using p1
    by metis
  then have " a/b + b/c + c/d + d/a ≥ 2 * (a*c + b*d) / sqrt (a*b*c*d)"
    using assms
    using p2
    by simp
  then have "a/b + b/c + c/d + d/a ≥ 2 * (a+c)*(b+d) / sqrt (a*b*c*d)"
    using assms
    using p3
    by simp
  then have "a/b + b/c + c/d + d/a  ≥ 2 * (2 * sqrt (a*c) * 2 * sqrt (b*d)) / sqrt (a*b*c*d)"
    using assms
    using p4
    by fastforce
  then have "a/b + b/c + c/d + d/a ≥ 8"
    using assms
    using p5
    by (simp add: real_sqrt_mult)
  then show ?thesis
    by auto
qed


(*
Kada je a = c i b = d, tada se i izraz (a + c) * (b + d) = a*c + b*d iz postavke zadatka
transformise u kvadratnu jednacinu oblika a^2 - 4ab + b^2 = 0.
 *)

lemma kvadratna_jednacina:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  assumes "(a + c) * (b + d) = a*c + b*d"
  assumes "a = c" "b = d"
  shows "4 * a * b = a*a + b*b"
  using assms
  by simp

(* Jednacina ima resenja kada je a/b = 2 + sqrt 3 i  a/b = 2 - sqrt 3  *)

lemma resenje_kvadratne_1:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  assumes "(a + c) * (b + d) = a*c + b*d"
  assumes "a = c" "b = d"
  assumes "a = b * (2 + sqrt 3)"
  shows "4 * a * b = a*a + b*b"
  using assms
  using kvadratna_jednacina by blast

lemma resenje_kvadratne_2:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  assumes "(a + c) * (b + d) = a*c + b*d"
  assumes "a = c" "b = d"
  assumes "a = b * (2 - sqrt 3)"
  shows "4 * a * b = a*a + b*b"
  using assms
  using kvadratna_jednacina by blast

(*Primer kada  S ima vrednost 8 je kada je a = c = 1 i b = d = 2 + sqrt 3.
Tada je ispunjeno da je a/b = 2 - sqrt 3 
*)
lemma task2_dokaz:
  fixes a b c d :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  assumes "(a + c) * (b + d) = a*c + b*d"
  assumes "a = c" "b = d"
  assumes "a=1" "b=2+sqrt 3"
  shows "a/b + b/c + c/d + d/a = 8"
proof-
  have "a/b + b/c + c/d + d/a = 1/(2+ sqrt 3) + (2+ sqrt 3) / 1 + 1 / (2+ sqrt 3) + (2+ sqrt 3) / 1"
    using assms
    by simp
  also have "… = 2 / (2 + sqrt 3) + 4 + 2 * sqrt 3"
    by auto
  also have "… = 4  + 2 / (2 + sqrt 3) + 2 * sqrt 3"
    by simp
  also have "… = 4  + 2 / (2 + sqrt 3) + 2 * sqrt 3 * (2 + sqrt 3) / (2 + sqrt 3) "
    using assms(2) assms(9) by auto
  also have "… = 4 + (2 +  2 * sqrt 3 * (2 + sqrt 3)) / (2 + sqrt 3)"
    by (simp add: add_divide_distrib)
  also have "… = 4 + (2 + 2 * sqrt 3 * 2 + 2 * sqrt 3 * sqrt 3) / (2 + sqrt 3)"
    by (simp add: distrib_left)
  also have "… = 4 + (2 + 4 * sqrt 3 + 2 * 3) / (2 + sqrt 3)"
    by simp
  also have "… = 4 + (8 + 4 * sqrt 3) / (2 + sqrt 3)"
    by simp
  also have "… = 4 + 4 * (2 + sqrt 3) / (2 + sqrt 3)"
    by simp
  also have "… = 4 + 4 * 1"
    by (metis assms(2) assms(9) less_irrefl mult.right_neutral nonzero_mult_div_cancel_left times_divide_eq_right)
  finally show ?thesis
    by auto
qed

(* Kako je (a + c) * (b + d) = a*c + b*d ≥ 8 i postoji S = (a + c) * (b + d) = a*c + b*d = 8
sledi da je najmaja vrednost ovog izraza upravo 8. *)

