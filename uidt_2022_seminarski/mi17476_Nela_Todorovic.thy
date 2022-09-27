theory mi17476_Nela_Todorovic
  imports Complex_Main
begin


text \<open>

https://www.imo-official.org/problems/IMO2009SL.pdf
Algebra A4 problem

\<close> 


(*    Pomocna lema koja transformise proizvod u drugi oblik
       pokazuje:  \<surd>2\<surd>(a+b) = 2*\<surd>(ab/(a+b)) * \<surd>\<onehalf>(2+ (a\<^sup>2+b\<^sup>2)/ab)      *)
lemma pomocna [simp]:
  fixes a b  :: real
  assumes "a > 0" "b > 0"
  shows "sqrt(2) * sqrt(a + b) =   2 * sqrt(a*b/(a+b))* sqrt(1/2* (2 + (a^2+b^2)/(a*b)))"
proof-
  have "(a + b)^2 = a^2 + 2*a*b + b^2"
    by (simp add: power2_sum)
  then have "(a + b)^2 = (a*b)*(a^2/(a*b)) + (a*b)*2 + (a*b)*(b^2/(a*b))"
    using assms(1) assms(2) by force
  then have "(a + b)^2 = (a*b) * (a^2/(a*b) + 2 + b^2/(a*b))"
    by (simp add: distrib_left)
  then have "(a + b) = (a*b)/(a+b) * (a^2/(a*b) + 2 + b^2/(a*b))"
    by (smt (verit, best) assms(1) assms(2) nonzero_mult_div_cancel_left power2_eq_square times_divide_eq_left)
  then have "sqrt(a+b) = sqrt((a*b)/(a+b) * (a^2/(a*b) + 2 + b^2/(a*b)))"
    by presburger
  then have "sqrt(a+b) = sqrt((a*b)/(a+b)) * sqrt( (a^2/(a*b) + 2 + b^2/(a*b)))"
    by (metis real_root_mult sqrt_def)
  then have "sqrt(2) * sqrt(a+b) = sqrt(2)* sqrt((a*b)/(a+b)) * sqrt( (a^2/(a*b) + 2 + b^2/(a*b)))"
    by simp 
  then have  "sqrt(2)*sqrt(a+b) = 2/sqrt(2)* sqrt(a*b/(a+b)) * sqrt((a^2/(a*b) + 2 + b^2/(a*b)))"
    using real_div_sqrt by force
  then have "sqrt(2)*sqrt(a+b) = 2*sqrt(a*b/(a+b)) * sqrt(1/2)*sqrt((a^2/(a*b) + 2 + b^2/(a*b)))"
    by (simp add: mult.commute real_sqrt_divide)
  then have "sqrt(2)*sqrt(a+b) = 2*sqrt(a*b/(a+b)) * sqrt(1/2*(a^2/(a*b) + 2 + b^2/(a*b)))"
    by (metis mult.assoc real_sqrt_mult)
  then show ?thesis
    by (simp add: add_divide_distrib)
qed


(* KA  nejednakost za dva broja -- K \<ge> A *)
lemma KA2 [simp]:
  fixes x y :: real
  assumes "x \<ge> 0" "y \<ge> 0"
  shows "sqrt(1/2*(x^2 + y^2)) \<ge> 1/2* (x + y)"
proof-
  have "(x - y)^2 \<ge> 0"
    by auto
  then have "x^2 - 2*x*y + y^2 \<ge> 0"
    by (smt (verit, best) sum_squares_bound)
  then have "x^2 + y^2 \<ge> 2*x*y"
    by auto
  then have "x^2 + y^2 + x^2 + y^2  \<ge> 2*x*y + x^2 + y^2"
    by auto
  then have "2 * (x^2 + y^2) \<ge> (x + y)^2"
    by (simp add: power2_sum)
  then have "1/2 * (x^2 + y^2) \<ge> 1/4 * (x + y)^2"
    by auto
  then have "1/2 * (x^2 + y^2) \<ge> (1/2 * (x+y))^2"
    by (simp add: power_divide)
  then have "sqrt(1/2 * (x^2 + y^2)) \<ge> sqrt((1/2 * (x+y))^2)"
    using real_sqrt_le_mono by blast
  then show ?thesis
    by auto
qed

(* KA nejednakost za dva broja pomnozena sa istim brojem -- zK \<ge> zA *)
lemma KA2_mult [simp]:
  fixes x y z:: real
  assumes "x \<ge> 0" "y \<ge> 0" "z > 0"
  shows "z*sqrt(1/2*(x^2 + y^2)) \<ge>z* 1/2* (x + y)"
  using KA2 assms(1) assms(2) assms(3) by force


lemma prvi_deo:
  fixes a b :: real
  assumes "a > 0" "b > 0"
  shows "sqrt(2) * sqrt(a+b) \<ge> sqrt(2*a*b/(a+b)) + sqrt((a^2+b^2)/(a+b))"
proof-
  have 1: "0 \<le> sqrt(2)"
    by auto
  have 2: "0 \<le> sqrt((a^2+b^2)/(a*b))"
    using assms
    by auto
  have 3: "0 \<le> 2*sqrt(a*b/(a+b))"
    using assms
    by auto
  have 10:  "sqrt(2) * sqrt(a+b) = 2 * sqrt(a*b/(a+b)) * sqrt(1/2*(2+(a^2+b^2)/(a*b)))"
    using assms(1) assms(2) pomocna by blast
  then  have 11: "2 * sqrt(a*b/(a+b)) * sqrt(1/2*(2+(a^2+b^2)/(a*b))) \<ge> 2 * sqrt(a*b/(a+b)) *1/2* (sqrt(2)+sqrt((a^2+b^2)/(a*b)))"
    using assms 1 2 3 KA2_mult[where x = "sqrt(2)" and y = "sqrt((a^2+b^2)/(a*b))" and z = "2*sqrt(a*b/(a+b))"]
    by auto
  then have "2 * sqrt(a*b/(a+b)) *1/2* (sqrt(2)+sqrt((a^2+b^2)/(a*b))) = sqrt(a*b/(a+b)) * (sqrt(2)+sqrt((a^2+b^2)/(a*b)))"
    by auto
  then have  "2 * sqrt(a*b/(a+b)) *1/2* (sqrt(2)+sqrt((a^2+b^2)/(a*b))) =  sqrt(2) * sqrt(a*b/(a+b)) +  sqrt(a*b/(a+b)) *sqrt((a^2+b^2)/(a*b)) "
    by (simp add: distrib_left)
  then have "2 * sqrt(a*b/(a+b)) *1/2* (sqrt(2)+sqrt((a^2+b^2)/(a*b))) =  sqrt(2*a*b/(a+b)) + sqrt(a*b)/sqrt(a+b) *sqrt(a^2+b^2)/sqrt(a*b)"
    by (simp add: real_sqrt_divide real_sqrt_mult)
  then have "2 * sqrt(a*b/(a+b)) *1/2* (sqrt(2)+sqrt((a^2+b^2)/(a*b))) = sqrt(2*a*b/(a+b)) + sqrt((a^2+b^2)/(a+b))"
    using "10" real_sqrt_divide by force
  then show ?thesis
  using "10" "11" by presburger
qed


lemma drugi_deo [simp]:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  shows "sqrt(2*a*b/(a+b)) + sqrt(2*b*c/(b+c)) + sqrt(2*c*a/(c+a)) \<ge> 3"
  sorry

lemma glavna:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a*b + b*c + c*a \<le> 3 * a*b*c"
  shows "sqrt((a^2 + b^2)/(a + b)) + sqrt((b^2 + c^2)/(b + c)) + sqrt((c^2 + a^2)/(c + a)) + 3
         \<le> sqrt(2) * (sqrt(a + b) + sqrt(b + c) + sqrt(c + a))" 
proof-
  have "sqrt((a^2 + b^2)/(a + b)) + sqrt(2*a*b/(a+b))
      + sqrt((b^2 + c^2)/(b + c)) + sqrt(2*b*c/(b+c))
      + sqrt((c^2 + a^2)/(c + a)) + sqrt(2*c*a/(c+a)) \<le>  sqrt(2)*sqrt(a + b) +  sqrt(2)*sqrt(b + c) +  sqrt(2)*sqrt(c + a)"
    by (smt (verit) assms(1) assms(2) assms(3) prvi_deo)
  then have "sqrt((a^2 + b^2)/(a + b)) + sqrt(2*a*b/(a+b))
      + sqrt((b^2 + c^2)/(b + c)) + sqrt(2*b*c/(b+c))
      + sqrt((c^2 + a^2)/(c + a)) + sqrt(2*c*a/(c+a)) \<le>  sqrt(2)* (sqrt(a + b) + sqrt(b + c) + sqrt(c + a))"
    by (simp add: distrib_left)
  then show ?thesis
    by (smt (verit, del_insts) assms(1) assms(2) assms(3) drugi_deo)
  qed
  
end
