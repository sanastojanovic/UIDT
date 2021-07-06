theory mi17130_Aleksa_Kojadinovic
  imports Main HOL.Real "HOL-ex.Sqrt"

begin

text \<open>
Link: https://www.imo-official.org/problems/IMO2006SL.pdf
A5. Neka su a b i c stranice trougla. Pokazati:
sqrt (b + c - a) / (sqrt b + sqrt c - sqrt a) + sqrt (c + a - b) / (sqrt c + sqrt a - sqrt b) + sqrt (a + b - c) / (sqrt a + sqrt b - sqrt c) <= 3
\<close>

definition sides_of_triangle :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
"sides_of_triangle a b c \<longleftrightarrow> (a < b + c) \<and> (b < a + c) \<and> (c < a + b) \<and> a > 0 \<and> b > 0 \<and> c > 0"

definition triang_ineq :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
"triang_ineq p q r \<longleftrightarrow> p + q > r"

lemma DenPositive:
  fixes p q r :: "real"
  assumes "p > 0" "q > 0" "r > 0"
  assumes "triang_ineq p q r"
  shows "sqrt p + sqrt q - sqrt r > 0"
  using assms
  unfolding triang_ineq_def
proof-
  have "p + q > r"
    using assms(4) triang_ineq_def by auto
  from this have "sqrt p + sqrt q > sqrt r"
    by (smt (z3) assms(1) assms(2) real_sqrt_less_mono sqrt_add_le_add_sqrt)
  from this show ?thesis
    by simp
qed

lemma FirstTransform:
  fixes a b c :: "real"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "triang_ineq a b c" "triang_ineq a c b" "triang_ineq b c a"
  assumes "x = sqrt b + sqrt c - sqrt a"
  assumes "y = sqrt c + sqrt a - sqrt b"
  assumes "z = sqrt a + sqrt b - sqrt c"
  shows "b + c - a = x^2 - (x-y)*(x-z)/2"
  using assms
  unfolding triang_ineq_def
  sorry
  
find_theorems "(_ + _)^2"

lemma UtilSubLemma:
  fixes u :: "real"
  assumes "u > -1/2"
  shows "sqrt (1 + 2*u) \<le> 1 + u"
  using assms
proof-

  have "1 + u > 0"
    using assms
    by auto

  have "sqrt (1 + 2*u) \<le> sqrt (1 + 2*u + u^2)"
    by simp
  also have "... = sqrt ((1 + u)^2)" 
    by (simp add: Power.comm_semiring_1_class.power2_sum)
  also have "... = 1+u"
    using `1 + u > 0` by simp
  finally show ?thesis .
qed

thm "Rings.ring_class.right_diff_distrib"

find_theorems "(_ + _)*_ = _ * _ + _ * _"

lemma TrinSquareMinus:
  fixes p q r :: "real"
  assumes "p > 0" "q > 0" "r > 0"
  shows "(sqrt p + sqrt q - sqrt r)^2 = p + q + r + 2*sqrt(p*q) - 2*sqrt(p*r) - 2*sqrt(q*r)"
proof-
  have "(sqrt p + sqrt q - sqrt r)^2 = (sqrt p + sqrt q - sqrt r)*(sqrt p + sqrt q - sqrt r)"
    by (simp add: power2_eq_square)
  also have "... = (sqrt p + sqrt q - sqrt r)*sqrt p + (sqrt p + sqrt q - sqrt r)*(sqrt q - sqrt r)"
    by (metis add_diff_eq distrib_right mult.commute)
  also have "... = sqrt p * sqrt p + sqrt q * sqrt p - sqrt r * sqrt p + (sqrt p + sqrt q - sqrt r)*(sqrt q - sqrt r)"
    by (metis diff_diff_eq2 left_diff_distrib')
  also have "... = sqrt p * sqrt p + sqrt q * sqrt p - sqrt r * sqrt p + (sqrt p + sqrt q - sqrt r)*sqrt q - (sqrt p + sqrt q - sqrt r)*sqrt r"
    using right_diff_distrib by auto
  also have "... = sqrt p * sqrt p + sqrt q * sqrt p - sqrt r * sqrt p + sqrt p * sqrt q + sqrt q * sqrt q - sqrt r * sqrt q - (sqrt p + sqrt q - sqrt r)*sqrt r"
    by (simp add: distrib_right left_diff_distrib)
  also have "... = sqrt p * sqrt p + sqrt q * sqrt p - sqrt r * sqrt p + sqrt p * sqrt q + sqrt q * sqrt q - sqrt r * sqrt q - sqrt p * sqrt r - sqrt q * sqrt r + sqrt r * sqrt r"
    by (simp add: distrib_right left_diff_distrib)  
  also have "... = p + sqrt p * sqrt q - sqrt p * sqrt r + sqrt p * sqrt q + q - sqrt q * sqrt r - sqrt p * sqrt r - sqrt q * sqrt r + r"
    using assms
    using power2_eq_square
    using mult.commute
    by auto
  also have "... = p + sqrt (p*q) - sqrt (p*r) + sqrt (p*q) + q - sqrt(q*r) - sqrt(p*r) - sqrt(q*r) + r"
    using NthRoot.real_sqrt_mult
    by auto
  also have "... = p + q + r + 2*sqrt(p*q) - 2*sqrt(p*r) - 2*sqrt(q*r)"
    by simp
  finally show ?thesis .
qed

find_theorems "(_ * _) / (_ * _)"

lemma MultIneqSame:
  fixes a b :: real
  assumes "n > 0"
  shows "a < b \<longleftrightarrow> n*a < n*b"
  using assms
  by simp

lemma SubIneqSame:
  fixes a b n :: "real"
  shows "a < b \<longleftrightarrow> a - n < b - n"
  by simp
  
  


lemma FirstSubViable:
  fixes a b c :: "real"
  assumes "triang_ineq a b c" "triang_ineq a c b" "triang_ineq b c a"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "x = sqrt b + sqrt c - sqrt a"
  assumes "y = sqrt c + sqrt a - sqrt b"
  assumes "z = sqrt a + sqrt b - sqrt c"
  assumes "x > 0" "y > 0" "z > 0"
  shows "-(x-y)*(x-z)/(4*x^2) > -1/2"
  unfolding triang_ineq_def
proof-
  have "x ^ 2 > 0" 
    using assms(10) by auto

  have "x*z > 0"
    using assms by simp
  have "y*x > 0"
    using assms by simp
  have "y*z > 0"
    using assms by simp

  have "?thesis \<longleftrightarrow> (x-y)*(x-z)/(4*x^2) < 1/2"
    by linarith
  also have "... \<longleftrightarrow> 4*((x-y)*(x-z)/(4*x^2)) < 4*(1/2)" 
    using MultIneqSame
    by linarith
  also have "... \<longleftrightarrow> (x-y)*(x-z)/(x^2) < 2"
    by simp
  also have "... \<longleftrightarrow> (x^2)*((x-y)*(x-z)/(x^2)) < x^2*(2)"
    using MultIneqSame
    by (meson \<open>0 < x\<^sup>2\<close>)
  also have "... \<longleftrightarrow> (x-y)*(x-z) < (x^2)*2"
    using \<open>0 < x\<^sup>2\<close> by auto
  also have "... \<longleftrightarrow> (sqrt b + sqrt c - sqrt a - (sqrt c +  sqrt a - sqrt b))*(sqrt b + sqrt c - sqrt a - (sqrt a + sqrt b - sqrt c)) < 2*x^2"
    using assms
    by auto
  also have "... \<longleftrightarrow> (sqrt b + sqrt c - sqrt a - sqrt c - sqrt a + sqrt b)*(sqrt b + sqrt c - sqrt a - sqrt a - sqrt b + sqrt c) < 2*x^2"
    by simp
  also have "... \<longleftrightarrow> (2*(sqrt b) - 2*sqrt(a))*(2*(sqrt c) - 2*(sqrt a)) < 2*x^2"
    by simp
  also have "... \<longleftrightarrow> 4*(sqrt b - sqrt a)*(sqrt c - sqrt a) < 2*x^2"
    by (metis (mono_tags, hide_lams) mult.commute mult.left_commute mult_numeral_left_semiring_numeral num_double right_diff_distrib')
  also have "... \<longleftrightarrow> 2*(sqrt b - sqrt a)*(sqrt c - sqrt a) < x^2"
    by linarith
  also have "... \<longleftrightarrow> 2*(sqrt b * (sqrt c - sqrt a) - sqrt a *(sqrt c - sqrt a)) < x^2"
    by (simp add: ab_semigroup_mult_class.mult_ac(1) left_diff_distrib')
  also have "... \<longleftrightarrow> 2*(sqrt b * sqrt c - sqrt b * sqrt a - sqrt a * (sqrt c - sqrt a)) < x^2"
    by (smt (verit, del_insts) distrib_left)
  also have "... \<longleftrightarrow> 2*(sqrt b * sqrt c - sqrt b * sqrt a - sqrt a * sqrt c + sqrt a * sqrt a) < x^2"
    find_theorems "_ * (_ - _)"
    apply (subst Rings.ring_class.right_diff_distrib)
    back
    by auto
  also have "... \<longleftrightarrow> 2*(sqrt (b*c) - sqrt (b*a) - sqrt (a*c) + a) < x^2"
    using `x > 0`
    using NthRoot.real_sqrt_mult
    using assms(4) by force
  also have "... \<longleftrightarrow> 2*(sqrt (b*c) - sqrt (b*a) - sqrt (a*c) + a) < (sqrt b + sqrt c - sqrt a)^2"
    using assms
    by auto
  also have "... \<longleftrightarrow> 2*(sqrt (b*c) - sqrt (b*a) - sqrt (a*c) + a) < b + c + a + 2*sqrt(b*c) - 2*sqrt(b*a) - 2*sqrt(c*a)"
    using TrinSquareMinus
    by (metis assms(4) assms(5) assms(6))
  also have "... \<longleftrightarrow> 2*sqrt(b*c) - 2*sqrt(b*a) - 2*sqrt(a*c) + 2*a < b + c + a + 2*sqrt(b*c) - 2*sqrt(b*a) - 2*sqrt(c*a)"
    by simp
  also have "... \<longleftrightarrow> a < b + c"
    by (simp add: mult.commute)
  also have "... \<longleftrightarrow> True"
    using assms
    unfolding triang_ineq_def
    by simp
  finally show ?thesis 
    by simp
qed


lemma SecondSubViable:
  fixes a b c :: "real"
  assumes "triang_ineq a b c" "triang_ineq a c b" "triang_ineq b c a"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "x = sqrt b + sqrt c - sqrt a"
  assumes "y = sqrt c + sqrt a - sqrt b"
  assumes "z = sqrt a + sqrt b - sqrt c"
  assumes "x > 0" "y > 0" "z > 0"
  shows "-(z-x)*(z-y)/(4*z^2) > -1/2"
  unfolding triang_ineq_def
proof-
  have "z ^ 2 > 0" 
    using assms(12) by auto

  have "x*z > 0"
    using assms by simp
  have "y*x > 0"
    using assms by simp
  have "y*z > 0"
    using assms by simp

  have "?thesis \<longleftrightarrow> (z-x)*(z-y)/(4*z^2) < 1/2"
    by linarith
  also have "... \<longleftrightarrow> 4*((z-x)*(z-y)/(4*z^2)) < 4*(1/2)" 
    using MultIneqSame
    by linarith
  also have "... \<longleftrightarrow> (z-x)*(z-y)/(z^2) < 2"
    by simp
  also have "... \<longleftrightarrow> (z^2)*((z-x)*(z-y)/(z^2)) < z^2*(2)"
    using MultIneqSame
    by (meson \<open>0 < z^2\<close>)
  also have "... \<longleftrightarrow> (z-x)*(z-y) < (z^2)*2"
    using \<open>0 < z^2\<close> by auto
  also have "... \<longleftrightarrow> (sqrt a + sqrt b - sqrt c - (sqrt b +  sqrt c - sqrt a))*(sqrt a + sqrt b - sqrt c - (sqrt c + sqrt a - sqrt b)) < 2*z^2"
    using assms
    by auto
  also have "... \<longleftrightarrow> (sqrt a + sqrt b - sqrt c - sqrt b - sqrt c + sqrt a)*(sqrt a + sqrt b - sqrt c - sqrt c - sqrt a + sqrt b) < 2*z^2"
    by simp
  also have "... \<longleftrightarrow> (2*(sqrt a) - 2*sqrt(c))*(2*(sqrt b) - 2*(sqrt c)) < 2*z^2"
    by simp
  also have "... \<longleftrightarrow> 4*(sqrt a - sqrt c)*(sqrt b - sqrt c) < 2*z^2"
    by (metis (mono_tags, hide_lams) mult.commute mult.left_commute mult_numeral_left_semiring_numeral num_double right_diff_distrib')
  also have "... \<longleftrightarrow> 2*(sqrt a - sqrt c)*(sqrt b - sqrt c) < z^2"
    by linarith
  also have "... \<longleftrightarrow> 2*(sqrt a * (sqrt b - sqrt c) - sqrt c *(sqrt b - sqrt c)) < z^2"
    by (simp add: ab_semigroup_mult_class.mult_ac(1) left_diff_distrib')
  also have "... \<longleftrightarrow> 2*(sqrt a * sqrt b - sqrt a * sqrt c - sqrt c * (sqrt b - sqrt c)) < z^2"
    by (smt (verit, del_insts) distrib_left)
  also have "... \<longleftrightarrow> 2*(sqrt a * sqrt b - sqrt a * sqrt c - sqrt c * sqrt b + sqrt c * sqrt c) < z^2"
    find_theorems "_ * (_ - _)"
    apply (subst Rings.ring_class.right_diff_distrib)
    back
    by auto
  also have "... \<longleftrightarrow> 2*(sqrt (a*b) - sqrt (a*c) - sqrt (c*b) + c) < z^2"
    using NthRoot.real_sqrt_mult
    using assms(6) by force
  also have "... \<longleftrightarrow> 2*(sqrt (a*b) - sqrt (a*c) - sqrt (c*b) + c) < (sqrt a + sqrt b - sqrt c)^2"
    using assms
    by auto
  also have "... \<longleftrightarrow> 2*(sqrt (a*b) - sqrt (a*c) - sqrt (c*b) + c) < a + b +  c + 2*sqrt(a*b) - 2*sqrt(a*c) - 2*sqrt(b*c)"
    using TrinSquareMinus
    using assms(4) assms(5) assms(6) by presburger
  also have "... \<longleftrightarrow> 2*sqrt(a*b) - 2*sqrt(a*c) - 2*sqrt(c*b) + 2*c < a + b +  c + 2*sqrt(a*b) - 2*sqrt(a*c) - 2*sqrt(b*c)"
    by simp
  also have "... \<longleftrightarrow> c < a + b"
    by (simp add: mult.commute)
  also have "... \<longleftrightarrow> True"
    using assms
    unfolding triang_ineq_def
    by simp
  finally show ?thesis 
    by simp
qed


lemma ThirdSubViable:
  fixes a b c :: "real"
  assumes "triang_ineq a b c" "triang_ineq a c b" "triang_ineq b c a"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "x = sqrt b + sqrt c - sqrt a"
  assumes "y = sqrt c + sqrt a - sqrt b"
  assumes "z = sqrt a + sqrt b - sqrt c"
  assumes "x > 0" "y > 0" "z > 0"
  shows "-(y-z)*(y-x)/(4*y^2) > -1/2"
  unfolding triang_ineq_def
proof-
  have "y ^ 2 > 0" 
    using assms(11) by auto

  have "x*z > 0"
    using assms by simp
  have "y*x > 0"
    using assms by simp
  have "y*z > 0"
    using assms by simp

  have "?thesis \<longleftrightarrow> (y-z)*(y-x)/(4*y^2) < 1/2"
    by linarith
  also have "... \<longleftrightarrow> 4*((y-z)*(y-x)/(4*y^2)) < 4*(1/2)" 
    using MultIneqSame
    by linarith
  also have "... \<longleftrightarrow> (y-z)*(y-x)/(y^2) < 2"
    by simp
  also have "... \<longleftrightarrow> (y^2)*((y-z)*(y-x)/(y^2)) < y^2*(2)"
    using MultIneqSame
    by (meson \<open>0 < y^2\<close>)
  also have "... \<longleftrightarrow> (y-z)*(y-x) < (y^2)*2"
    using \<open>0 < y^2\<close> by auto
  also have "... \<longleftrightarrow> (sqrt c + sqrt a - sqrt b - (sqrt a +  sqrt b - sqrt c))*(sqrt c + sqrt a - sqrt b - (sqrt b + sqrt c - sqrt a)) < 2*y^2"
    using assms
    by auto
  also have "... \<longleftrightarrow> (sqrt c + sqrt a - sqrt b - sqrt a - sqrt b + sqrt c)*(sqrt c + sqrt a - sqrt b - sqrt b - sqrt c + sqrt a) < 2*y^2"
    by simp
  also have "... \<longleftrightarrow> (2*(sqrt c) - 2*sqrt(b))*(2*(sqrt a) - 2*(sqrt b)) < 2*y^2"
    by simp
  also have "... \<longleftrightarrow> 4*(sqrt c - sqrt b)*(sqrt a - sqrt b) < 2*y^2"
    by (metis (mono_tags, hide_lams) mult.commute mult.left_commute mult_numeral_left_semiring_numeral num_double right_diff_distrib')
  also have "... \<longleftrightarrow> 2*(sqrt c - sqrt b)*(sqrt a - sqrt b) < y^2"
    by linarith
  also have "... \<longleftrightarrow> 2*(sqrt c * (sqrt a - sqrt b) - sqrt b *(sqrt a - sqrt b)) < y^2"
    by (simp add: ab_semigroup_mult_class.mult_ac(1) left_diff_distrib')
  also have "... \<longleftrightarrow> 2*(sqrt c * sqrt a - sqrt c * sqrt b - sqrt b * (sqrt a - sqrt b)) < y^2"
    by (smt (verit, del_insts) distrib_left)
  also have "... \<longleftrightarrow> 2*(sqrt c * sqrt a - sqrt c * sqrt b - sqrt b * sqrt a + sqrt b * sqrt b) < y^2"
    find_theorems "_ * (_ - _)"
    apply (subst Rings.ring_class.right_diff_distrib)
    back
    by auto
  also have "... \<longleftrightarrow> 2*(sqrt (c*a) - sqrt (c*b) - sqrt (b*a) + b) < y^2"
    using NthRoot.real_sqrt_mult
    using assms(5) by auto
  also have "... \<longleftrightarrow> 2*(sqrt (c*a) - sqrt (c*b) - sqrt (b*a) + b) < (sqrt c + sqrt a - sqrt b)^2"
    using assms
    by auto
  also have "... \<longleftrightarrow> 2*(sqrt (c*a) - sqrt (c*b) - sqrt (b*a) + b) < c + a + b + 2*sqrt(c*a) - 2*sqrt(c*b) - 2*sqrt(a*b)"
    using TrinSquareMinus
    using assms(4) assms(5) assms(6) by presburger
  also have "... \<longleftrightarrow> 2*sqrt(c*a) - 2*sqrt(c*b) - 2*sqrt(b*a) + 2*b < c + a + b + 2*sqrt(c*a) - 2*sqrt(c*b) - 2*sqrt(a*b)"
    by simp
  also have "... \<longleftrightarrow> b < c + a"
    by (simp add: mult.commute)
  also have "... \<longleftrightarrow> True"
    using assms
    unfolding triang_ineq_def
    by simp
  finally show ?thesis 
    by simp
qed












lemma MainProblem:
  fixes a b c :: "real"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "triang_ineq a b c" "triang_ineq a c b" "triang_ineq b c a"
  shows "sqrt(b + c - a) / (sqrt b + sqrt c - sqrt a)
        + sqrt (c + a - b) / (sqrt c + sqrt a - sqrt b)
        + sqrt(a + b - c)/(sqrt a + sqrt b - sqrt c) 
        \<le> (3::real)" (is "?e1/?x + ?e2/?y + ?e3/?z \<le> (3::real)")
  using assms
  unfolding triang_ineq_def
  
proof-
  have "?x > 0"
    using assms
    using DenPositive by blast
  have "?y > 0"
    using assms
    using DenPositive by fastforce
  have "?z > 0"
    using assms
    using DenPositive by auto

  have "?e1/?x = sqrt (1 + 2* (-(?x-?y)*(?x-?z) / (4*?x^2)))"
    sorry
  have "?e2/?y = sqrt (1 - (?z-?x)*(?z-?y) / (2*?z^2))"
    sorry
  have "?e3/?z = sqrt (1 - (?y-?z)*(?y-?z) / (2*?y^2))"
    sorry

  have "-(?x-?y)*(?x-?z)/(2*?x^2) = -2*(?x-?y)*(?x-?z)/(4*?x^2)"
    by (simp only: NthRoot.real_divide_square_eq)
  

  have "-(?x-?y)*(?x-?z)/(4*?x^2) > -1/2"
    using assms
    using FirstSubViable \<open>0 < sqrt a + sqrt b - sqrt c\<close> \<open>0 < sqrt b + sqrt c - sqrt a\<close> \<open>0 < sqrt c + sqrt a - sqrt b\<close> by blast

  from this have "?e1/?x \<le> 1 + (-(?x-?y)*(?x-?z)/(4*?x^2))"
    thm UtilSubLemma
    using UtilSubLemma
    using \<open>sqrt (b + c - a) / (sqrt b + sqrt c - sqrt a) = sqrt (1 + 2 * (- (sqrt b + sqrt c - sqrt a - (sqrt c + sqrt a - sqrt b)) * (sqrt b + sqrt c - sqrt a - (sqrt a + sqrt b - sqrt c)) / (4 * (sqrt b + sqrt c - sqrt a)\<^sup>2)))\<close> by presburger

    
    






    
    
  
qed
  
  

end