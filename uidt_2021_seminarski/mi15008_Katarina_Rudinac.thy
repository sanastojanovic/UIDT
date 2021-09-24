theory mi15008_Katarina_Rudinac
  imports  HOL.Real "HOL-ex.Sqrt" Complex_Main
begin

text \<open>
https://www.imo-official.org/problems/IMO2009SL.pdf  A4

"Let a, b, c be positive real numbers such that
a*b + b*c + c*a \<le> 3*a*b*c. Prove that:
sqrt ((a^2+b^2)/(a+b)) + sqrt ((b^2+c^2)/(b+c))+ sqrt ((c^2+a^2)/(c+a)) + 3
\<le> (sqrt 2) * (sqrt (a+b) + sqrt (b+c) + sqrt (c+a))

\<close>

declare [[quick_and_dirty=true]]
(*
find_theorems "_*(_+_)"
find_theorems "sqrt _*_"
thm "NthRoot.real_root_mult"
find_theorems "_"
find_theorems "_*(_/_)"
thm "Fields.field_class.times_divide_times_eq"
value "(1::real)/2*2"
value "(2::real)+2/2"
find_theorems "_"
*)

lemma help_1:
  fixes a b :: real
  assumes "a>0" "b>0"
  shows "2*sqrt((a*b)/(a+b))*sqrt(1/2*(2+(a^2+b^2)/(a*b)))
= sqrt 2 * sqrt (a+b)"
proof-
  have "2*sqrt((a*b)/(a+b))*sqrt(1/2*(2+(a^2+b^2)/(a*b)))
       =2*sqrt((a*b)/(a+b))*sqrt(1/2*2+1/2*(a^2+b^2)/(a*b))"
     by (auto simp add: field_simps) 
  also have "\<dots>=2*sqrt((a*b)/(a+b))*sqrt(2/2+1/2*(a^2+b^2)/(a*b))"
    by auto
  also have "\<dots>=2*sqrt((a*b)/(a+b))*sqrt(1+1/2*(a^2+b^2)/(a*b))"
    by auto
  also have "\<dots>=2*sqrt((a*b)/(a+b))*sqrt(1+(1*(a^2+b^2))/(2*(a*b)))"
    by auto
  also have "\<dots>=2*sqrt((a*b)/(a+b))*sqrt(1+(a^2+b^2)/(2*(a*b)))"
    by auto
  also have "\<dots>=2*sqrt((a*b)/(a+b))*sqrt((2*a*b)/(2*a*b)+(a^2+b^2)/(2*(a*b)))"
    by auto
  also have "\<dots>=2*sqrt((a*b)/(a+b))*sqrt((2*a*b+a^2+b^2)/(2*(a*b)))"
     by (auto simp add: field_simps)
  also have "\<dots>=2*sqrt((a*b)/(a+b))*sqrt((2*a*b+a*a+b*b)/(2*(a*b)))"
     by (auto simp add: field_simps power2_eq_square)
   also have "\<dots>=2*sqrt((a*b)/(a+b))*sqrt(((a+b)*(a+b))/(2*(a*b)))"
     by (auto simp add: field_simps)
   also have "\<dots>=2*sqrt(((a*b)/(a+b))*((a+b)*(a+b)/(2*(a*b))))"
      by (metis mult.assoc real_sqrt_mult)
   also have "\<dots>=2*sqrt((a*b)*((a+b)*(a+b))/((a+b)*(2*(a*b))))" 
     by (simp add: Fields.field_class.times_divide_times_eq nonzero_eq_divide_eq)
   also have "\<dots>=2*sqrt((a*b)*(a+b)*(a+b)/((a+b)*2*(a*b)))"
    by auto
   also have "\<dots>=2*sqrt((a*b)*(a+b)/(2*(a*b)))"
      by (simp add: mult.assoc)
   also have "\<dots>=2*sqrt((a+b)/(2))"
     using assms  by (simp add: mult.assoc)
   also have "\<dots>=sqrt 4 *sqrt((a+b)/(2))"
    by auto
   also have "\<dots>=sqrt(4*(a+b)/(2))"
     by (metis real_sqrt_mult times_divide_eq_right)
   also have "\<dots>=sqrt(2*(a+b))"
    by auto
   also have "\<dots>=sqrt 2 * sqrt (a+b)"
     using real_sqrt_mult by blast
   finally
   show ?thesis
     .
qed




lemma QM_AM_case_2:
  fixes x y :: real
  assumes "x>0" "y>0"
  shows "sqrt((x+y)/2) \<ge> (1/2 * (sqrt x + sqrt y))"
proof-
  have "(sqrt x - sqrt y)^2 \<ge> 0" by auto
  from this have "x + y - 2*sqrt (x*y) \<ge> 0"
    using assms
    by (smt (z3) arith_geo_mean_sqrt field_sum_of_halves)
  then have "(x+y)/2 - sqrt (x*y) \<ge> 0" by auto
  then have "(x+y)/2 \<ge> sqrt (x*y)" by auto
  then have "x+y \<ge> (x+y)/2 + sqrt (x*y)" 
    by (smt (verit, best) field_sum_of_halves)
  then have "(x+y)/2 \<ge> 1/2 * ( (x+y)/2 + sqrt (x*y))"  
    by (simp add: mult_2_right)
  then have "(x+y)/2 \<ge> 1/4 * (x+y +2* sqrt (x*y))"  
    using \<open>sqrt (x * y) \<le> (x + y) / 2\<close> by force
  then have "(x+y)/2 \<ge> 1/4 * ((sqrt x)*(sqrt x) + (sqrt y)*(sqrt y) +2* sqrt (x*y))"  
    using assms
    by auto
  then have "(x+y)/2 \<ge> 1/4 * ((sqrt x)*(sqrt x) + (sqrt y)*(sqrt y) +2* sqrt (x)*sqrt(y))"
    using assms
    by (auto simp add: NthRoot.real_sqrt_mult)
  then have "(x+y)/2 \<ge> 1/4 * ((sqrt x)^2 + (sqrt y)^2 +2* sqrt (x)*sqrt(y))"
    using assms 
    by auto
  then have "(x+y)/2 \<ge> 1/4 * (sqrt x + sqrt y)*(sqrt x + sqrt y)"
    using assms
    using Power.comm_semiring_1_class.power2_sum
    by (metis mult.assoc power2_eq_square)
  then have "(x+y)/2 \<ge> 1/2^2 * (sqrt x + sqrt y)*(sqrt x + sqrt y)"
    by force
  then have "(x+y)/2 \<ge> 1/2^2 * (sqrt x + sqrt y)^2"
    by (simp add: mult.assoc power2_eq_square)
  then have "(x+y)/2 \<ge> (1/2 * (sqrt x + sqrt y))^2"
    by (metis power_mult_distrib power_one_over)
  then show "sqrt((x+y)/2) \<ge> (1/2 * (sqrt x + sqrt y))"
    using real_le_rsqrt by presburger

qed



lemma OM_AM_applied_help:
  fixes a b :: real
  assumes "a>0" "b>0"
  shows "0 \<le> (a\<^sup>2 + b\<^sup>2) / (a * b)"
  using assms(1) assms(2) by auto

lemma QM_AM_applied:
  fixes a b :: real
  assumes "a>0" "b>0"
  shows "1/2*(sqrt 2 + sqrt ((a^2+b^2)/(a*b)))
\<le>sqrt(1/2*(2+((a^2+b^2)/(a*b))))"
  using QM_AM_case_2[of "sqrt 2" "sqrt ((a^2+b^2)/(a*b))"]
  using NthRoot.real_sqrt_pow2_iff[symmetric, of "2"]
  using NthRoot.real_sqrt_pow2_iff[symmetric, of "((a\<^sup>2 + b\<^sup>2) / (a * b))"]
  using OM_AM_applied_help
proof -
have f1: "\<not> 0 \<le> (a\<^sup>2 + b\<^sup>2) / a / b \<or> (sqrt ((a\<^sup>2 + b\<^sup>2) / a / b))\<^sup>2 = (a\<^sup>2 + b\<^sup>2) / a / b"
  using divide_divide_eq_left by auto
  have f2: "\<And>r ra. \<not> (0::real) < r \<or> \<not> 0 < ra \<or> 0 \<le> (ra\<^sup>2 + r\<^sup>2) / ra / r"
    by (metis (no_types) OM_AM_applied_help divide_divide_eq_left)
  have f3: "\<And>r ra. (r::real) \<noteq> 0 \<or> (ra::real) / 0 = 0"
    by simp
    have f4: "(a\<^sup>2 + b\<^sup>2) / a / b \<noteq> 0 \<or> (0::nat) < 2"
      by linarith
  have f5: "(a\<^sup>2 + b\<^sup>2) / a / b \<noteq> 0 \<or> sqrt ((a\<^sup>2 + b\<^sup>2) / a / b) = 0"
    using f2 f1 by (metis (no_types) assms(1) assms(2) power_eq_0_iff)
  have f6: "(a\<^sup>2 + b\<^sup>2) / a / b \<noteq> 0 \<or> 0 \<le> (a\<^sup>2 + b\<^sup>2) / a / b"
    by linarith
  have f7: "(a\<^sup>2 + b\<^sup>2) / a / b \<noteq> 0 \<or> \<not> 0 \<le> (a\<^sup>2 + b\<^sup>2) / a / b \<or> (a\<^sup>2 + b\<^sup>2) / a / b = 0\<^sup>2"
    using f5 by (smt (z3) real_sqrt_pow2_iff)
  have f8: "\<And>r. \<not> 0 \<le> r \<or> sqrt (sqrt r) = 0 \<or> 0 < sqrt r"
    using real_sqrt_ge_0_iff by force
  have "(0::real) \<le> 2"
    by linarith
  moreover
  { assume "0 < sqrt 2 \<and> \<not> (0::real) \<le> 0"
    have "0 < sqrt 2 \<and> sqrt (sqrt ((a\<^sup>2 + b\<^sup>2) / a / b)) \<noteq> 0"
      using assms(1) assms(2) by force }
  ultimately have "0 < sqrt 2 \<and> sqrt (sqrt ((a\<^sup>2 + b\<^sup>2) / a / b)) \<noteq> 0"
    using f8 f7 f6 f5 f4 f3 f2 f1 assms(1) assms(2) divide_divide_eq_left divide_divide_eq_right mult_eq_0_iff power2_less_eq_zero_iff power_eq_0_iff real_sqrt_eq_iff real_sqrt_ge_0_iff real_sqrt_pow2_iff sum_power2_eq_zero_iff zero_less_power2 by force
  then have "0 \<le> (a\<^sup>2 + b\<^sup>2) / a / b \<and> 0 < sqrt 2 \<and> 0 < sqrt ((a\<^sup>2 + b\<^sup>2) / a / b)"
    using f8 f2 by (metis (full_types) assms(1) assms(2))
  then show ?thesis
    using QM_AM_case_2 divide_divide_eq_right by force
qed

lemma QM_AM_applied_with_mul:
  fixes a b :: real
  assumes "a>0" "b>0" 
  shows "2*sqrt((a*b)/(a+b))*1/2*(sqrt 2 + sqrt ((a^2+b^2)/(a*b)))
\<le>2*sqrt((a*b)/(a+b))*sqrt(1/2*(2+((a^2+b^2)/(a*b))))"
proof-
  have  "1/2*(sqrt 2 + sqrt ((a^2+b^2)/(a*b)))
\<le>sqrt(1/2*(2+((a^2+b^2)/(a*b))))" 
    apply (rule QM_AM_applied)
    using assms(1) 
     apply simp
    using assms(2)
    apply simp
    done
  from this show 
    "2*sqrt((a*b)/(a+b))*1/2*(sqrt 2 + sqrt ((a^2+b^2)/(a*b)))
  \<le>2*sqrt((a*b)/(a+b))*sqrt(1/2*(2+((a^2+b^2)/(a*b))))"
    using assms
    by (auto simp add: Numeral_Simprocs.nat_mult_le_cancel1)
  qed
(*
  find_theorems "_*_\<le>_*_"
*)
lemma help_2:
  fixes a b :: real
  assumes "a>0" "b>0"
  shows "2*sqrt(a*b/(a+b))*1/2*(sqrt 2 + sqrt ((a^2+b^2)/(a*b))) 
= sqrt ((2*a*b)/(a+b)) + sqrt ((a^2+b^2)/(a+b))"
proof-
  have "2*sqrt(a*b/(a+b))*1/2*(sqrt 2 + sqrt ((a^2+b^2)/(a*b))) 
= sqrt(a*b/(a+b))*(sqrt 2 + sqrt ((a^2+b^2)/(a*b)))"
     by auto
  also have "\<dots>= sqrt(a*b/(a+b))*sqrt 2+sqrt(a*b/(a+b))*sqrt ((a^2+b^2)/(a*b))"
     by (auto simp add: field_simps)
  also have "\<dots>= sqrt(a*b/(a+b)*2)+sqrt(a*b/(a+b))*sqrt ((a^2+b^2)/(a*b))"
    using real_sqrt_mult by presburger
  also have "\<dots>= sqrt(2*a*b/(a+b))+sqrt(a*b/(a+b))*sqrt((a^2+b^2)/(a*b))"
    by auto
  also have "\<dots>= sqrt(2*a*b/(a+b))+sqrt((a*b/(a+b))*((a^2+b^2)/(a*b)))"
    using real_sqrt_mult by presburger
  also have "\<dots>= sqrt(2*a*b/(a+b))+sqrt(a*b*(a^2+b^2)/((a+b)*(a*b)))"
     by simp
  also have "\<dots>= sqrt(2*a*b/(a+b))+sqrt((a^2+b^2)/(a+b))"
    using assms by auto
  finally
  show ?thesis
    .
qed


lemma first_part:
  fixes a b :: real
  assumes "a>0" "b>0"
  shows "sqrt ((2*a*b)/(a+b)) + sqrt ((a^2+b^2)/(a+b))
\<le> sqrt 2 * sqrt (a+b)"
proof-
  have "sqrt ((2*a*b)/(a+b)) + sqrt ((a^2+b^2)/(a+b))
= 2*sqrt(a*b/(a+b))*1/2*(sqrt 2 + sqrt ((a^2+b^2)/(a*b)))"
    using assms
    using field_sum_of_halves help_2 by fastforce
  also have "\<dots>\<le>2*sqrt((a*b)/(a+b))*sqrt(1/2*(2+(a^2+b^2)/(a*b)))"
    using assms
    by (rule QM_AM_applied_with_mul)
  also have "\<dots>=sqrt 2 * sqrt (a+b)"
    using help_1
    using assms(1) assms(2) by presburger
  finally
  show ?thesis
    .
qed
(*
find_theorems "_/_=1"
find_theorems "_/_"
*)




lemma second_part:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  assumes "a*b + b*c + c*a \<le> 3*a*b*c"
  shows "3 \<le>sqrt((2*a*b)/(a+b))+sqrt((2*b*c)/(b+c))+sqrt((2*c*a)/(c+a))"
proof-
  have "(3::real) = 3* 1"
    by auto
  also have "\<dots>=3*sqrt 1" 
    by auto
  also have "\<dots>=3*sqrt((a*b+b*c+c*a)/(a*b+b*c+c*a))"
    using assms
    apply (auto simp add: Fields.division_ring_class.divide_self)
    by (smt (z3) mult_pos_pos)
  also have "\<dots>\<le> 3* sqrt(( 3*a*b*c)/(a*b+b*c+c*a))"
    using assms
    by (smt (verit, best) less_divide_eq_1_pos mult_pos_pos real_sqrt_gt_1_iff)
  also have "\<dots>\<le> 3* sqrt(2/2*(3*a*b*c)/(a*b+b*c+c*a))"
    using assms
    by simp
  also have "\<dots>= 3* sqrt(2*(3*a*b*c)/(2*(a*b+b*c+c*a)))"
    using assms
    by (metis divide_divide_eq_left mult.commute times_divide_eq_right)
  also have "\<dots>= 3* sqrt(2*(3*a*b*c)/(2*a*b+2*b*c+2*c*a))"
    by force
  also have "\<dots>= 3* sqrt(2*(3*a*b*c)/(a*b + a*b + b*c + b*c + c*a + c*a))"
    by (simp add: assms(2) assms(3) assms(4))
  also have "\<dots>= 3* sqrt(3*(2*a*b*c)/(a*b + a*b + b*c + b*c + c*a + c*a))"
    by simp
  also have "\<dots>= 3* sqrt(3/((a*b + a*b + b*c + b*c + c*a + c*a)/(2*a*b*c)))"
    by simp
  also have "\<dots>= 3* sqrt(3/(((c*a+c*b)+(a*b+a*c)+(b*c+b*a))/(2*a*b*c)))"
    by simp
  also have "\<dots>= 3* sqrt(3/((c*a+c*b)/(2*a*b*c)+(a*b+a*c)/(2*a*b*c)+(b*c+b*a)/(2*a*b*c)))"
    by (simp add: add_divide_distrib)
  also have "\<dots>= 3* sqrt(3/((c*(a+b))/(2*a*b*c)+(a*(b+c))/(2*a*b*c)+(b*(c+a))/(2*a*b*c)))"
    by (simp add: distrib_left)
  also have "\<dots>= 3* sqrt(3/((c*(a+b))/(c*(2*a*b))+(a*(b+c))/(a*(2*b*c))+(b*(c+a))/(b*(2*a*c))))"
    by auto
  also have "\<dots>= 3* sqrt(3/((a+b)/(2*a*b)+(b+c)/(2*b*c)+(c+a)/(2*a*c)))"
    using assms(1) assms(2) assms(3) by force
  also have "\<dots>= 3* sqrt(3/(sqrt((a+b)/(2*a*b))^2
                            +sqrt((b+c)/(2*b*c))^2
                            +sqrt((c+a)/(2*a*c))^2))"
    using assms(1) assms(2) assms(3) by fastforce
  also have "\<dots>\<le>sqrt((2*a*b)/(a+b))+sqrt((2*b*c)/(b+c))+sqrt((2*c*a)/(c+a))"
    sorry
  finally
  show ?thesis
    .
qed



lemma A4_2009:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  assumes "a*b + b*c + c*a \<le> 3*a*b*c"
  shows 
"sqrt ((a^2+b^2)/(a+b)) + sqrt ((b^2+c^2)/(b+c))
+ sqrt  ((c^2+a^2)/(c+a)) + 3
\<le> (sqrt 2) * (sqrt (a+b) + sqrt (b+c) + sqrt (c+a))
"
proof-
  have "sqrt ((a^2+b^2)/(a+b)) + sqrt ((b^2+c^2)/(b+c))
+ sqrt  ((c^2+a^2)/(c+a)) + 3 
\<le> sqrt 2*sqrt (a+b) + sqrt 2*sqrt (b+c) + sqrt 2*sqrt (c+a)
- sqrt ((2*a*b)/(a+b)) - sqrt ((2*b*c)/(b+c)) - sqrt ((2*c*a)/(c+a)) + 3
"
    using assms
    by (smt (verit, best) first_part)
  also have "\<dots>= (sqrt 2) * (sqrt (a+b) + sqrt (b+c) + sqrt (c+a))
- (sqrt ((2*a*b)/(a+b)) + sqrt ((2*b*c)/(b+c)) + sqrt ((2*c*a)/(c+a))) + 3
"
    by (simp add: distrib_left)
  also have "\<dots>\<le> (sqrt 2) * (sqrt (a+b) + sqrt (b+c) + sqrt (c+a))-3 + 3"
    using assms
    using second_part
    by fastforce
  also have "\<dots>\<le> (sqrt 2) * (sqrt (a+b) + sqrt (b+c) + sqrt (c+a))"
    by auto
    finally
    show ?thesis
      .
qed





end