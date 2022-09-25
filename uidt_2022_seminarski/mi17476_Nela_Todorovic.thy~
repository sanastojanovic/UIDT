theory mi17476_Nela_Todorovic
imports Complex_Main
begin

text \<open>

https://www.imo-official.org/problems/IMO2009SL.pdf
Algebra A4 problem

\<close> 


(*    Pomocna lema koja transformise proizvod u drugi oblik
       pokazuje:  \<surd>2\<surd>(a+b) = 2*\<surd>(ab/(a+b)) * \<surd>\<onehalf>(2+ (a\<^sup>2+b\<^sup>2)/ab)      *)
lemma pomocna:
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


lemma glavna:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a*b + b*c + c*a \<le> 3 * a*b*c"
  shows "sqrt((a^2 + b^2)/(a + b)) + sqrt((b^2 + c^2)/(b + c)) + sqrt((c^2 + a^2)/(c + a)) + 3
         \<le> sqrt(2) * (sqrt(a + b) + sqrt(b + c) + sqrt(c + a))" 
  sorry



end