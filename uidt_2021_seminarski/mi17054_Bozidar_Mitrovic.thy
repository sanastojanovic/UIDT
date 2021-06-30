theory mi17054_Bozidar_Mitrovic
  imports Complex_Main "HOL.Real"
  
begin

(* 
Let a, b, c, d be positive real numbers such that
a*b*c*d = 1 and a + b + c + d > a / b + b / c + c / d + d / a

Prove that a + b + c + d < b / a + c / b + d / c + a / d
*)


lemma argme2:
  fixes a b :: real
  assumes "a \<ge> 0" "b \<ge> 0"
  shows "a + b \<ge>  2 * root 2 (a *b)"
proof(-) 
  have "0 \<le> (sqrt a - sqrt b)^2"
    by auto
  also have "... = (sqrt a - sqrt b)*(sqrt a - sqrt b)"
    by (simp add: power2_eq_square)
  also have "... = sqrt a * (sqrt a - sqrt b) - sqrt b * (sqrt a - sqrt b)"
    by (auto simp:left_diff_distrib) 
  also have "... = (sqrt a * sqrt a - sqrt a * sqrt b) - sqrt b * (sqrt a - sqrt b)"
    by (metis left_diff_distrib mult.commute)
  also have  "... = (a - sqrt a * sqrt b) - sqrt b * (sqrt a - sqrt b)"
    using assms(1) 
    by auto
  also have  "... = a - sqrt a * sqrt b - sqrt b * (sqrt a - sqrt b)"
    by auto
  also have "... = a - sqrt a * sqrt b - sqrt b * sqrt a + sqrt b * sqrt b"
    by (simp add: right_diff_distrib')
  also have "... = a - sqrt a * sqrt b - sqrt b * sqrt a + b"
    using assms(2) 
    by auto
  also have "... = a - sqrt a * sqrt b - sqrt a * sqrt b + b"
    by (auto simp:mult.commute)
  also have "... = a - 2 * sqrt a * sqrt b + b"
    by auto
  finally show ?thesis
    by (smt (verit) \<open>(sqrt a - sqrt b) * (sqrt a - sqrt b) = sqrt a * (sqrt a - sqrt b) - sqrt b * (sqrt a - sqrt b)\<close> \<open>(sqrt a - sqrt b)\<^sup>2 = (sqrt a - sqrt b) * (sqrt a - sqrt b)\<close> \<open>0 \<le> (sqrt a - sqrt b)\<^sup>2\<close> \<open>a - sqrt a * sqrt b - sqrt a * sqrt b + b = a - 2 * sqrt a * sqrt b + b\<close> \<open>sqrt a * (sqrt a - sqrt b) - sqrt b * (sqrt a - sqrt b) = sqrt a * sqrt a - sqrt a * sqrt b - sqrt b * (sqrt a - sqrt b)\<close> \<open>sqrt a * sqrt a - sqrt a * sqrt b - sqrt b * (sqrt a - sqrt b) = a - sqrt a * sqrt b - sqrt b * (sqrt a - sqrt b)\<close> real_sqrt_mult sqrt_def)
qed


lemma root2_eq_sqrt:
  assumes "x \<ge> 0"
  shows "root 2 (x * y) = sqrt (x * y)"
  using sqrt_def by auto


lemma transform_root_2_2:
  shows "root 2 (root 2 (x)) = root 4 (x)"
  by (metis num_double numeral_times_numeral real_root_mult_exp)


lemma argme_4_helper_lemma:
  fixes a b c d :: real
  assumes "a \<ge> 0" "b \<ge> 0" "c \<ge> 0" "d \<ge> 0"
  shows "2 * root 2 ((2 * root 2 (a * b)) *  (2 * root 2 (c * d))) = 4 * root 4 (a * b * c * d)"
proof(-)
  have "2 * root 2 ((2 * root 2 (a * b)) *  (2 * root 2 (c * d))) = 2 * root 2 (2 * root 2 (a * b) *  2 * root 2 (c * d))"
    by (simp add:algebra_simps)
  also have "... = 2 * root 2 ((2^2) * (root 2 (a * b) * root 2 (c * d)) )" 
    by (simp add:algebra_simps)
  also have "... = 2 * sqrt ((2^2) * (root 2 (a * b) * root 2 (c * d)))"
    by (simp add: root2_eq_sqrt)
  also have "... = 2 * 2 * sqrt((root 2 (a * b) * root 2 (c * d)))"
    by (simp add: real_sqrt_mult)
  also have "... = 4 * sqrt((root 2 (a * b) * root 2 (c * d)))"
    by simp
  also have "... = 4 * root 2 ((root 2 (a * b) * root 2 (c * d))) "
    using sqrt_def by presburger
  also have "... = 4 * root 2 (root 2 (a * b) * root 2 (c * d))"
    by simp
  show ?thesis
    by (metis calculation mult.assoc real_root_mult transform_root_2_2)
qed


lemma argme4:
  fixes a b c d ::real
  assumes "a \<ge> 0" "b \<ge>0" "c \<ge> 0" "d\<ge>0"
  shows "a + b + c + d \<ge> 4 * root 4 (a*b*c*d)"
  using assms
proof(-)
  have "a + b \<ge> 2 * root 2 (a * b)"
    using assms
    by (auto simp:argme2)
  also have "c + d \<ge> 2 * root 2 (c * d)"
    using assms
    by (auto simp:argme2)
  hence  "a + b + c + d \<ge> 2 * root 2 (a * b) + 2 * root 2 (c * d)" 
    using calculation by linarith
  have "(2 * root 2 (a * b)) + (2 * root 2 (c * d)) \<ge> 2 * root 2 ((2 * root 2 (a * b)) *  (2 * root 2 (c * d)))"
    using assms
    by (smt (verit) argme2 mult_nonneg_nonneg real_root_pos_pos_le)
  show ?thesis
    using \<open>2 * root 2 (2 * root 2 (a * b) * (2 * root 2 (c * d))) \<le> 2 * root 2 (a * b) + 2 * root 2 (c * d)\<close> \<open>2 * root 2 (a * b) + 2 * root 2 (c * d) \<le> a + b + c + d\<close> argme_4_helper_lemma assms(1) assms(2) assms(3) assms(4) by auto
qed



lemma glavnalema:
  fixes a b c d :: real
  assumes  "a>0" "b>0" "c>0" "d>0" "a * b * c * d = 1" "a + b + c + d > a / b + b / c + c / d + d / a"
  shows "a + b + c + d < b /a + c / b + d / c + a / d"
  oops

end