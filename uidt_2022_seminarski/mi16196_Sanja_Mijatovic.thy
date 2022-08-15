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
