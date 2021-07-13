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
  shows "root 4 (a*b*c*d) \<le> 1/4 * (a + b + c + d)"
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


lemma main_proof_helper_lemma:
  fixes a b c d :: real
  assumes  "a>0" "b>0" "c>0" "d>0" "a * b * c * d = 1"
  shows "a \<le>  1/4 * ((a/b) + (a/b) + (b/c) + (a/d))"
proof-
  have "a = root 4 (a^4)"
    using assms
    by (simp add:real_root_power_cancel)
  also have "... = root 4 (a^4 / 1)"
    by simp
  also have "... = root 4 (a^4 / (a*b*c*d))"
    using \<open>a*b*c*d=1\<close>
    by simp
  also have "... = root 4 ((a*a*a*a) / (a*b*c*d))"
    by (simp add: power4_eq_xxxx)
  also have "... = root 4 (a/a * a/b * a/c * a/d)"
    by simp
  also have "... = root 4 (b/b * a/b * a/c * a/d)"
    by simp
  also have "... = root 4 ((a/b) * (a/b) * (b/c) * (a/d))"
    by simp
  finally show ?thesis
    using assms
    by (smt (verit) argme4 divide_pos_pos)
qed


lemma calc_help_lemma:
  fixes a b c d :: real
  assumes  "a>0" "b>0" "c>0" "d>0"                                                                                                                                        
  shows "((a/b) + (a/b) + (b/c) + (a/d))/4 + ((b/c) + (b/c) + (c/d) + (b/a)) / 4 + ( (c/d) + (c/d) + (d/a) + (c/b)) / 4 + ((d/a) + (d/a) + (a/b) + (d/c)) / 4 =  (3 * a/b + 3 * b/c + 3 * c/d + 3 * d/a) / 4 +  (b/a + c/b + d/c + a/d)/ 4"
proof-
  have "1/4*((a/b) + (a/b) + (b/c) + (a/d)) + 1/4 * ((b/c) + (b/c) + (c/d) + (b/a)) + 1/4 * ( (c/d) + (c/d) + (d/a) + (c/b)) + 1/4 * ((d/a) + (d/a) + (a/b) + (d/c)) = 1/4*(2 * (a/b) + (b/c) + (a/d)) + 1/4 * (2 * (b/c) + (c/d) + (b/a)) + 1/4 * (2 * (c/d) + (d/a) + (c/b)) + 1/4 * (2 * (d/a) + (a/b) + (d/c))"
    by auto
  also have "... = 1/2 * (a/b) + 1/4 * (b/c) + 1/4 * (a/d) + 1/4 * (2 * (b/c) + (c/d) + (b/a)) + 1/4 * (2 * (c/d) + (d/a) + (c/b)) + 1/4 * (2 * (d/a) + (a/b) + (d/c))"
    by auto
  also have "... = 1/2 * (a/b) + 1/4 * (b/c) + 1/4 * (a/d) + 1/2 * (b/c) +1/4 * (c/d) + 1/4 * (b/a) + 1/4 * (2 * (c/d) + (d/a) + (c/b)) + 1/4 * (2 * (d/a) + (a/b) + (d/c))"
    by (auto simp add:algebra_simps)
  also have "... = 1/2 * (a/b) + 1/4 * (b/c) + 1/4 * (a/d) + 1/2 * (b/c) +1/4 * (c/d) + 1/4 * (b/a) + 1/2 * (c/d) + 1/4 * (d/a) + 1/4 * (c/b) + 1/4 * (2 * (d/a) + (a/b) + (d/c))"
    by (auto simp add:algebra_simps)
  also have "... = 1/2 * (a/b) + 1/4 * (b/c) + 1/4 * (a/d) + 1/2 * (b/c) +1/4 * (c/d) + 1/4 * (b/a) + 1/2 * (c/d) + 1/4 * (d/a) + 1/4 * (c/b) + 1/2 * (d/a) + 1/4 * (a/b) + 1/4 * (d/c)"
   by (auto simp add:algebra_simps)
  also have "... = 1/2 * (a/b) + 1/4 * (a/b) + 1/4 * (a/d) + 1/2 * (b/c) +1/4 * (c/d) + 1/4 * (b/a) + 1/2 * (c/d) + 1/4 * (d/a) + 1/4 * (c/b) + 1/2 * (d/a) + 1/4 * (b/c) + 1/4 * (d/c)"
    by auto
  also have "... = 3/4 * (a/b) + 1/4 * (a/d) + 1/2 * (b/c) + 1/4 * (c/d) + 1/4 * (b/a) + 1/2 * (c/d) + 1/4 * (d/a) + 1/4 * (c/b) + 1/2 * (d/a) + 1/4 * (b/c) + 1/4 * (d/c)"
    by auto
  also have "... = 3/4 * (a/b) + 1/4 * (b/c) + 1/2 * (b/c) + 1/4 * (c/d) + 1/4 * (b/a) + 1/2 * (c/d) + 1/4 * (d/a) + 1/4 * (c/b) + 1/2 * (d/a) + 1/4 * (a/d) + 1/4 * (d/c)"
    by auto
  also have "... = 3/4 * (a/b) + 3/4 * (b/c) + 1/4 * (c/d) + 1/4 * (b/a) + 1/2 * (c/d) + 1/4 * (d/a) + 1/4 * (c/b) + 1/2 * (d/a) + 1/4 * (a/d) + 1/4 * (d/c)"
    by auto
  also have "... = 3/4 * (a/b) + 3/4 * (b/c) + 1/4 * (c/d) + 1/2 * (c/d) + 1/4 * (b/a) + 1/4 * (d/a) + 1/4 * (c/b) + 1/2 * (d/a) + 1/4 * (a/d) + 1/4 * (d/c)"
    by auto
  also have "... = 3/4 * (a/b) + 3/4 * (b/c) + 3/4 * (c/d) + 1/4 * (b/a) + 1/4 * (d/a) + 1/4 * (c/b) + 1/2 * (d/a) + 1/4 * (a/d) + 1/4 * (d/c)"
    by auto
  also have "... = 3/4 * (a/b) + 3/4 * (b/c) + 3/4 * (c/d) + 1/4 * (b/a) + 1/4 * (d/a) + 1/2 * (d/a)  + 1/4 * (c/b) + 1/4 * (a/d) + 1/4 * (d/c)"
    by auto
  also have "... = 3/4 * (a/b) + 3/4 * (b/c) + 3/4 * (c/d) + 1/4 * (b/a) + 3/4 * (d/a)   + 1/4 * (c/b) + 1/4 * (a/d) + 1/4 * (d/c)"
    by auto
  also have "... = 3/4 * (a/b) + 3/4 * (b/c) + 3/4 * (c/d) + 3/4 * (d/a) + 1/4 * (b/a) +  1/4 * (c/b) + 1/4 * (a/d) + 1/4 * (d/c)"
    by auto
  also have "... = 3/4 * ( a/b + b/c + c/d + d/a ) + 1/4 * (b/a) +  1/4 * (c/b) + 1/4 * (a/d) + 1/4 * (d/c)"
    by auto
  also have "... = 3/4 * ( a/b + b/c + c/d + d/a ) + 1/4 * (b/a + c/b + a/d + d/c)"
    by auto
  finally show ?thesis
    by auto
qed


lemma glavnalema:
  fixes a b c d :: real
  assumes  "a>0" "b>0" "c>0" "d>0" "a * b * c * d = 1" "a + b + c + d > a / b + b / c + c / d + d / a"
  shows "a + b + c + d < b /a + c / b + d / c + a / d"
  using [[show_types]]
proof-
  have "a \<le> 1/4 * ((a/b) + (a/b) + (b/c) + (a/d))"
    using assms
    using main_proof_helper_lemma 
    by auto
  have "b \<le> 1/4 * ((b/c) + (b/c) + (c/d) + (b/a))"
    using assms
    using main_proof_helper_lemma[of b c d a]
    by (metis mult.assoc mult.commute)
  have "c \<le> 1/4 * ( (c/d) + (c/d) + (d/a) + (c/b))"
    using assms
    using main_proof_helper_lemma[of c d a b]
    by (metis mult.assoc mult.commute)
  have "d \<le> 1/4 * ((d/a) + (d/a) + (a/b) + (d/c))"
    using assms
    using main_proof_helper_lemma[of d a b c]
    by (metis mult.assoc mult.commute)
  have "a + b + c + d \<le> 1/4 * ((a/b) + (a/b) + (b/c) + (a/d)) + 1/4 * ((b/c) + (b/c) + (c/d) + (b/a)) + 1/4 * ( (c/d) + (c/d) + (d/a) + (c/b)) + 1/4 * ((d/a) + (d/a) + (a/b) + (d/c))"
    using \<open>a \<le> 1 / 4 * (a / b + a / b + b / c + a / d)\<close> \<open>b \<le> 1 / 4 * (b / c + b / c + c / d + b / a)\<close> \<open>c \<le> 1 / 4 * (c / d + c / d + d / a + c / b)\<close> \<open>d \<le> 1 / 4 * (d / a + d / a + a / b + d / c)\<close> by linarith
  also have  "... = (3 * (a/b) + 3 * b/c + 3 * c/d + 3 * d/a) / 4 +  (b/a + c/b + d/c + a/d)/ 4"
    using assms(1) assms(2) assms(3) assms(4)
    using calc_help_lemma
    by auto
  
  

end

(*
  have "... = 1/2 * (a/b) + 1/4 * (b/c) + 1/4*(a/d) +  1/2 * (b/c) + 1/4 * (c/d) + 1/4*(b/a) + 1/2 *(c/d) + 1/4 *d/a + 1/4 * (c/b) + 1/2*(d/a) + 1/4 *(a/b) + 1/4*(d/c)"
    sledgehammer
*)