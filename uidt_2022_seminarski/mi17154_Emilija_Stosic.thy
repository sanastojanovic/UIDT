theory mi17154_Emilija_Stosic

imports Complex_Main "HOL.Real"

begin

text \<open>
Link: https://www.imo-official.org/problems/IMO2008SL.pdf
Algebra A5
Let a, b, c, d be positive real numbers such that
abcd = 1 and a + b + c + d > a/b + b/c + c/d + d/a.
Prove that a + b + c + d < b/a + c/b + d/c + a/d.
\<close>

(*Prvi deo*)

lemma seminarski1:
  fixes a b c d :: real
  assumes "a>0" "b>0" "c>0" "d>0" 
  assumes "a*b*c*d=1" 
  assumes "a + b + c + d > a/b + b/c + c/d + d/a"
  shows "a + b + c + d < b/a + c/b + d/c + a/d"
  sorry

(*Drugi deo*)

lemma pomocna_1_1:
  fixes a b :: real
  assumes "a>0" "b>0"
  shows "1/2*(a+b) \<ge> root 2 (a*b)"
proof - 
  have "0 \<le> (root 2 a - root 2 b)^2"
    by simp
  also have "... = (root 2 a - root 2 b)*(root 2 a - root 2 b)"
    by (simp add: power2_eq_square)
  also have "... = (root 2 a)*(root 2 a) - (root 2 a)*(root 2 b)
     - (root 2 b)*(root 2 a) + (root 2 b)*(root 2 b)"
    by (smt (verit, best) mult_diff_mult)
  also have "... = (root 2 a)*(root 2 a) - 2*(root 2 a)*(root 2 b)
      + (root 2 b)*(root 2 b)"
    by auto
  also have "... = (root 2 (a^2)) - 2*(root 2 a)*(root 2 b) + (root 2 (b^2))"
    using sqrt_def by auto
  also have "... = a - 2*(root 2 a)*(root 2 b) + b"
    using assms(1) assms(2) pos2 real_root_pow_pos real_root_power by presburger
  finally show ?thesis
    using arith_geo_mean_sqrt assms(1) assms(2) sqrt_def by auto
qed

lemma pomocna_1_2:
  fixes a b c d :: real
  assumes "a>0" "b>0" "c>0" "d>0"
  shows "2*root 2 ((2*root 2 (a*b))*(2*root 2 (c*d))) = 4*root 4 (a*b*c*d)"
proof - 
  have "2*root 2 ((2*root 2 (a*b))*(2*root 2 (c*d))) = 2*root 2 (2*root 2 (a*b) * 2*root 2 (c*d))"
   by simp
  also have "... = 2*root 2 ((2^2) * (root 2 (a*b) * root 2 (c*d)))"
    by simp
  also have "... = 2*root 2 (2^2) * root 2 (root 2 (a*b)*root 2 (c*d))"
    by (simp add: real_root_mult)
  also have "... = 4*root 2 (root 2 (a*b)*root 2 (c*d))"
    by simp
  also have "... = 4*root 2 (root 2 (a*b*c*d))"
    by (simp add: real_root_mult)
  also have "... = 4*root 4 (a*b*c*d)"
    by (metis num_double numeral_times_numeral real_root_mult_exp)
  finally show ?thesis
    by auto
qed
  
(* a + b \<ge> 2*root 2 (a*b) = p  (pomocna_1_1)
   c + d \<ge> 2*root 2 (c*d) = q
   p + q \<ge> 2*root 2 (p*q) = 2*root 2 ((2*root 2 (a*b))*(2*root 2 (c*d)))
   a + b + c + d \<ge> p + q  = 2*root 2 ((2*root 2 (a*b))*(2*root 2 (c*d)))
                          = 4*root 2 (root 2 (a*b*c*d))
                          = 4*root 4 (a*b*c*d) (pomocna_1_2)
   a + b + c + d \<ge> 4 * root 4 (a*b*c*d)
   1/4*(a + b + c + d) \<ge> root 4 (a*b*c*d)
*)

lemma pomocna1:
  fixes a b c d :: real
  assumes "a>0" "b>0" "c>0" "d>0"
  shows "root 4 (a*b*c*d) \<le> 1/4*(a+b+c+d)"
proof -
  have "1/2*(a+b) \<ge> root 2 (a*b)"
    using assms(1) assms(2) pomocna_1_1 by blast
  have "1/2*(c+d) \<ge> root 2 (c*d)"
    using assms(3) assms(4) pomocna_1_1 by blast
  have "1/2*(a+b+c+d) \<ge> root 2 (a*b) + root 2 (c*d)"
    using \<open>root 2 (a * b) \<le> 1 / 2 * (a + b)\<close> \<open>root 2 (c * d) \<le> 1 / 2 * (c + d)\<close> by auto
  have "a+b+c+d \<ge> 2*root 2 (a*b) + 2*root 2 (c*d)"
    by (smt (z3) \<open>root 2 (a * b) \<le> 1 / 2 * (a + b)\<close> arith_geo_mean_sqrt assms(3) assms(4) combine_common_factor field_sum_of_halves mult_cancel_right1 sqrt_def)
  have "1/2*((2*root 2 (a*b)) + (2*root 2 (c*d))) \<ge> root 2 ((2*root 2 (a*b))*(2*root 2 (c*d)))"
    by (smt (verit) assms(1) assms(2) assms(3) assms(4) mult_eq_0_iff mult_nonneg_nonneg pomocna_1_1 pos2 real_root_eq_0_iff real_root_pos_pos_le)
  have "(2*root 2 (a*b)) + (2*root 2 (c*d)) \<ge> 2*root 2 ((2*root 2 (a*b))*(2*root 2 (c*d)))"
    using \<open>root 2 (2 * root 2 (a * b) * (2 * root 2 (c * d))) \<le> 1 / 2 * (2 * root 2 (a * b) + 2 * root 2 (c * d))\<close> by force
  have "2*root 2 ((2*root 2 (a*b))*(2*root 2 (c*d))) = 4*root 4 (a*b*c*d)"
    using assms(1) assms(2) assms(3) assms(4) pomocna_1_2 by auto
  have "a+b+c+d \<ge> 4*root 4 (a*b*c*d)"
    using \<open>2 * root 2 (2 * root 2 (a * b) * (2 * root 2 (c * d))) = 4 * root 4 (a * b * c * d)\<close> \<open>2 * root 2 (2 * root 2 (a * b) * (2 * root 2 (c * d))) \<le> 2 * root 2 (a * b) + 2 * root 2 (c * d)\<close> \<open>2 * root 2 (a * b) + 2 * root 2 (c * d) \<le> a + b + c + d\<close> by linarith
  have "1/4*(a+b+c+d) \<ge> root 4 (a*b*c*d)"
    using \<open>4 * root 4 (a * b * c * d) \<le> a + b + c + d\<close> by auto
  show ?thesis
    using \<open>root 4 (a * b * c * d) \<le> 1 / 4 * (a + b + c + d)\<close> by blast
qed

lemma nejednakost_a:
  fixes a b c d :: real
  assumes "a>0" "b>0" "c>0" "d>0" 
  assumes "a*b*c*d=1"
  shows "a \<le> 1/4*((a/b) + (a/b) + (b/c) + (a/d))"
proof -
  have "a = root 4 (a*a*a*a)"
    using assms
    by (smt (verit) assms(1) power4_eq_xxxx real_root_power_cancel zero_less_numeral)
  also have "... = root 4 ((a*a*a*a)/1)"
    using assms
    by simp
  also have "... = root 4 ((a*a*a*a) / (a*b*c*d))"
    by (simp add: assms(5))
  also have "... = root 4 ((a/a)*(a/b)*(a/c)*(a/d))"
    by simp
  also have "... = root 4 (b/b * a/b * a/c * a/d)"
    using assms
    by auto
  also have "... = root 4 (a/b * (b*a)/(b*c) * a/d)"
    using assms
    by simp
  also have "... = root 4 ((a/b) * (a/b) * (b/c) * (a/d))"
    using assms
    by simp
  finally show ?thesis
    using assms
    by (smt (verit) pomocna1 divide_pos_pos)
qed

lemma nejednakost_b:
  fixes a b c d :: real
  assumes "a>0" "b>0" "c>0" "d>0" 
  assumes "a*b*c*d=1"
  shows "b \<le> 1/4*((b/c) + (b/c) + (c/d) + (b/a))"
proof - 
  have "b = root 4 (b*b*b*b)"
    using assms
    by (smt (verit) assms(2) power4_eq_xxxx real_root_power_cancel zero_less_numeral)
  also have "... = root 4 ((b*b*b*b) / (a*b*c*d))"
    by (simp add: assms(5))
  also have "... = root 4 (b/a * b/b * b/c * b/d)"
    by simp
  also have "... = root 4 (b/a * c/c * b/c * b/d)"
    by simp
  also have "... = root 4 (b/a * (c*b)/(c*d) * b/c)"
    by simp
  also have "... = root 4 ((b/c) * (b/c) * (c/d) * (b/a))"
    by simp
  finally show ?thesis
    using assms
    by (smt (verit) pomocna1 divide_pos_pos)
qed

lemma nejednakost_c:
  fixes a b c d :: real
  assumes "a>0" "b>0" "c>0" "d>0" 
  assumes"a*b*c*d=1"
  shows "c \<le> 1/4*((c/d) + (c/d) + (d/a) + (c/b))"
proof - 
  have "c = root 4 (c*c*c*c)"
    using assms
    by (smt (verit) assms(2) power4_eq_xxxx real_root_power_cancel zero_less_numeral)
  also have "... = root 4 ((c*c*c*c) / (a*b*c*d))"
    by (simp add: assms(5))
  also have "... = root 4 (c/a * c/b * c/c * c/d)"
    by simp
  also have "... = root 4 (c/d * c/a * d/d * c/b)"
    by simp
  also have "... = root 4 (c/d * (c*d)/(a*d) * c/b)"
    by simp
  also have "... = root 4 ((c/d) * (c/d) * (d/a) * (c/b))"
    by simp
  finally show ?thesis
    using assms
   by (smt (verit) pomocna1 divide_pos_pos)
qed

lemma nejednakost_d:
  fixes a b c d :: real
  assumes "a>0" "b>0" "c>0" "d>0" 
  assumes "a*b*c*d=1"
  shows "d \<le> 1/4*((d/a) + (d/a) + (a/b) + (d/c))"
proof - 
  have "d = root 4 (d*d*d*d)"
    using assms
    by (smt (verit) assms(2) power4_eq_xxxx real_root_power_cancel zero_less_numeral)
  also have "... = root 4 ((d*d*d*d) / (a*b*c*d))"
    by (simp add: assms(5))
  also have "... = root 4 (d/a * d/b * d/c * d/d)"
    by simp
  also have "... = root 4 (d/a * d/b * d/c * a/a)"
    by simp
  also have "... = root 4 (d/a * (d*a)/(b*a) * d/c)"
    using assms
    by (simp add: mult.assoc)
  also have "... = root 4 ((d/a) * (d/a) * (a/b) * (d/c))"
    using assms
    by auto
  finally show ?thesis
    using assms
    by (smt (verit) pomocna1 divide_pos_pos)
qed

   
lemma suma_manje:
  fixes a b c d :: real
  assumes  "a>0" "b>0" "c>0" "d>0" 
  shows "1/4*(a/b + a/b + b/c + a/d) + 1/4*(b/c + b/c + c/d + b/a) +
    1/4*(c/d + c/d + d/a + c/b) + 1/4*(d/a + d/a + a/b + d/c) =
    3/4*(a/b + b/c + c/d + d/a) + 1/4*(b/a + c/b + d/c + a/d)"
proof - 
  have "1/4*(a/b + a/b + b/c + a/d) + 1/4*(b/c + b/c + c/d + b/a) +
    1/4*(c/d + c/d + d/a + c/b) + 1/4*(d/a + d/a + a/b + d/c) = 
    1/4*(2*(a/b) + b/c + a/d) + 1/4*(2*(b/c) + c/d + b/a) + 
    1/4*(2*(c/d) + d/a + c/b) + 1/4*(2*(d/a) + a/b + d/c)"
    using assms
    by auto
  also have  "... = 1/2*(a/b)+1/4*(b/c)+1/4*(a/d) + 1/4*(2*(b/c) + c/d + b/a) +
     1/4*(2*(c/d) + d/a + c/b) + 1/4*(2*(d/a) + a/b + d/c)"
    by auto
  also have "... = 1/2*(a/b)+1/4*(b/c)+1/4*(a/d) + 1/2*(b/c)+1/4*(c/d)+1/4*(b/a) + 
      1/4*(2*(c/d) + d/a + c/b) + 1/4*(2*(d/a) + a/b + d/c)"
    by (auto simp add:algebra_simps)
  also have "... = 1/2*(a/b)+1/4*(b/c)+1/4*(a/d) + 1/2*(b/c)+1/4*(c/d)+1/4*(b/a) +
     1/2*(c/d)+1/4*(d/a)+1/4*(c/b) + 1/4*(2*(d/a) + a/b + d/c)"
    by (auto simp add:algebra_simps)
  also have "... = 1/2*(a/b)+1/4*(b/c)+1/4*(a/d) + 1/2*(b/c)+1/4*(c/d)+1/4*(b/a) +
     1/2*(c/d)+1/4*(d/a)+1/4*(c/b) + 1/2*(d/a)+1/4*(a/b)+1/4*(d/c)"
    by (auto simp add:algebra_simps)
  also have "... = 1/2*(a/b)+1/4*(a/b)+1/4*(a/d) + 1/2*(b/c)+1/4*(b/c)+1/4*(b/a) +
       1/2*(c/d)+1/4*(c/d)+1/4*(c/b) + 1/2*(d/a)+1/4*(d/a)+1/4*(d/c)"
    by auto
  also have "... = 3/4*(a/b)+1/4*(a/d) + 3/4*(b/c)+1/4*(b/a) + 
      3/4*(c/d)+1/4*(c/b) + 3/4*(d/a)+1/4*(d/c)"
    by auto
  also have "... = 3/4*(a/b)+3/4*(b/c)+3/4*(c/d)+3/4*(d/a) + 
      1/4*(a/d)+1/4*(b/a)+1/4*(c/b)+1/4*(d/c)"
    by auto
  also have "... = 3/4*(a/b + b/c + c/d + d/a) 
     + 1/4*(a/d)+1/4*(b/a)+1/4*(c/b)+1/4*(d/c)"
    by auto
  also have "... = 3/4*(a/b + b/c + c/d + d/a) + 
     1/4*(a/d + b/a + c/b + d/c)"
    by auto
  finally show ?thesis
    by auto
qed

lemma cetvrtine:
  fixes a  :: real
  assumes "a = 1"
  shows "a = 1/4+3/4"
  by (simp add: assms)


lemma glavna:
  fixes a b c d :: real
  assumes "a>0" "b>0" "c>0" "d>0"
  assumes "a*b*c*d = 1"
  assumes "a + b + c + d > a/b + b/c + c/d + d/a"
  shows "a + b + c + d < b/a + c/b + d/c + a/d"
proof - 
  have "a \<le> 1/4*((a/b) + (a/b) + (b/c) + (a/d))"
    using assms(1) assms(2) assms(3) assms(4) assms(5) nejednakost_a by auto
  have "b \<le> 1/4*((b/c) + (b/c) + (c/d) + (b/a))" 
    using assms(1) assms(2) assms(3) assms(4) assms(5) nejednakost_b by presburger
  have "c \<le> 1/4*((c/d) + (c/d) + (d/a) + (c/b))"
    using assms(1) assms(2) assms(3) assms(4) assms(5) nejednakost_c by auto
  have "d \<le> 1/4*((d/a) + (d/a) + (a/b) + (d/c))"
    using assms(1) assms(2) assms(3) assms(4) assms(5) nejednakost_d by auto
  have "1/4*(a/b + a/b + b/c + a/d) + 1/4*(b/c + b/c + c/d + b/a) +
    1/4*(c/d + c/d + d/a + c/b) + 1/4*(d/a + d/a + a/b + d/c) =
    3/4*(a/b + b/c + c/d + d/a) + 1/4*(b/a + c/b + d/c + a/d)"
    using assms(1) assms(2) assms(3) assms(4) suma_manje by presburger
  have "a+b+c+d \<le> 3/4*(a/b + b/c + c/d + d/a) + 1/4*(b/a + c/b + d/c + a/d)"
    using \<open>1 / 4 * (a / b + a / b + b / c + a / d) + 1 / 4 * (b / c + b / c + c / d + b / a) + 1 / 4 * (c / d + c / d + d / a + c / b) + 1 / 4 * (d / a + d / a + a / b + d / c) = 3 / 4 * (a / b + b / c + c / d + d / a) + 1 / 4 * (b / a + c / b + d / c + a / d)\<close> \<open>a \<le> 1 / 4 * (a / b + a / b + b / c + a / d)\<close> \<open>b \<le> 1 / 4 * (b / c + b / c + c / d + b / a)\<close> \<open>c \<le> 1 / 4 * (c / d + c / d + d / a + c / b)\<close> \<open>d \<le> 1 / 4 * (d / a + d / a + a / b + d / c)\<close> by linarith
  have "3/4*(a+b+c+d)+1/4*(a+b+c+d) \<le> 3/4*(a/b + b/c + c/d + d/a) + 1/4*(b/a + c/b + d/c + a/d)"
    by (smt (verit, ccfv_SIG) \<open>a + b + c + d \<le> 3 / 4 * (a / b + b / c + c / d + d / a) + 1 / 4 * (b / a + c / b + d / c + a / d)\<close> cetvrtine combine_common_factor mult_cancel_right1)
  have "3/4*(a+b+c+d) \<ge>  3/4*(a/b + b/c + c/d + d/a)"
    using assms(6) by auto
  have "1/4*(a+b+c+d) \<le> 1/4*(b/a + c/b + d/c + a/d)"
    using assms
    using \<open>3 / 4 * (a + b + c + d) + 1 / 4 * (a + b + c + d) \<le> 3 / 4 * (a / b + b / c + c / d + d / a) + 1 / 4 * (b / a + c / b + d / c + a / d)\<close> \<open>3 / 4 * (a / b + b / c + c / d + d / a) \<le> 3 / 4 * (a + b + c + d)\<close> by linarith
  have "a+b+c+d \<le> b/a + c/b + d/c + a/d"
    using assms
    by (smt (verit, ccfv_SIG) \<open>1 / 4 * (a + b + c + d) \<le> 1 / 4 * (b / a + c / b + d / c + a / d)\<close> cetvrtine divide_eq_1_iff divide_le_eq_1_pos mult_strict_left_mono)   
  show ?thesis
    using assms
    by (smt (verit, ccfv_SIG) \<open>3 / 4 * (a + b + c + d) + 1 / 4 * (a + b + c + d) \<le> 3 / 4 * (a / b + b / c + c / d + d / a) + 1 / 4 * (b / a + c / b + d / c + a / d)\<close> assms(6) divide_le_0_iff mult_strict_left_mono)
qed

end