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


(* pomocna AG nejednakost za kubove tri broja -- A \<ge> G*)
lemma AG3_pomocna [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "(x^3 + y^3 + z^3) / 3 \<ge> x * y * z"
proof-
  have 1: "x* (x^2 + y^2 + z^2 - x*y - y*z - z*x) = x^3 + x*y^2 + x*z^2 - x^2*y - x*y*z - x^2*z "
    by (simp add: power2_eq_square power3_eq_cube right_diff_distrib' ring_class.ring_distribs(1))
  have 2: "y* (x^2 + y^2 + z^2 - x*y - y*z - z*x) = y*x^2 + y^3 + y*z^2 - y^2*x - y^2*z - x*y*z"
    by (simp add: distrib_left power2_eq_square power3_eq_cube right_diff_distrib)
  have 3:  "z* (x^2 + y^2 + z^2 - x*y - y*z - z*x) = z*x^2 + z*y^2 + z^3 - x*y*z - z^2*y - z^2*x"
    by (smt (verit, ccfv_threshold) diff_diff_eq2 mult.commute mult.left_commute power2_eq_square power3_eq_cube right_diff_distrib)
  then have "(x+y+z)*(x^2 + y^2 + z^2 - x*y - y*z - z*x) = x* (x^2 + y^2 + z^2 - x*y - y*z - z*x) + y* (x^2 + y^2 + z^2 - x*y - y*z - z*x) + z* (x^2 + y^2 + z^2 - x*y - y*z - z*x)"
    by (simp add: ring_class.ring_distribs(2))
  then have "(x+y+z)*(x^2 + y^2 + z^2 - x*y - y*z - z*x) =  x^3 + x*y^2 + x*z^2 - x^2*y - x*y*z - x^2*z + y*x^2 + y^3 + y*z^2 - y^2*x - y^2*z - x*y*z + z*x^2 + z*y^2 + z^3 - x*y*z - z^2*y - z^2*x"
    by (simp add: "1" "2" "3") 
  then have 10: "(x+y+z)*(x^2 + y^2 + z^2 - x*y - y*z - z*x) = x^3 + y^3 + z^3 - 3*x*y*z"
    by auto
  then have "(x+y+z)*(x^2 + y^2 + z^2 - x*y - y*z - z*x) = 1/2 * (x+y+z) * 2* (x^2 + y^2 + z^2 - x*y - y*z - z*x) "
    by (simp add: mult_2_right)
  then have "(x+y+z)*(x^2 + y^2 + z^2 - x*y - y*z - z*x) = 1/2 * (x+y+z) * (2*x^2 + 2*y^2 + 2*z^2 - 2*x*y - 2*y*z - 2*z*x)"
    by auto
  then have "(x+y+z)*(x^2 + y^2 + z^2 - x*y - y*z - z*x) = 1/2 * (x+y+z) * ((x^2 - 2*x*y + y^2) + (y^2 - 2*y*z + z^2) + (z^2 - 2*z*x + x^2))"
    by auto
  then have 11: "(x+y+z)*(x^2 + y^2 + z^2 - x*y - y*z - z*x) = 1/2 * (x+y+z) * ((x-y)^2 + (y-z)^2 + (z-x)^2)"
    by (simp add: power2_diff)
  then have "1/2 * (x+y+z) * ((x-y)^2 + (y-z)^2 + (z-x)^2) \<ge> 0" 
    using assms
    by auto
  then have " x^3 + y^3 + z^3 - 3*x*y*z \<ge> 0"
    using assms
    using "10" "11" by presburger
  then show ?thesis
    by auto
qed

(* AG nejednakost za tri broja -- A \<ge> G *)
lemma AG3 [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "(x + y + z) / 3 \<ge> root 3 (x*y*z) "
proof-
  have "(x + y + z) = (root 3 x)^3 + (root 3 y)^3 + (root 3 z)^3"
    using assms
    by force
  then show ?thesis
    by (metis AG3_pomocna assms(1) assms(2) assms(3) real_root_gt_0_iff real_root_mult zero_less_numeral)
qed

(* GH nejednakost za tri broja -- G \<ge> H *)
lemma GH3 [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "root 3 (x * y * z) \<ge>  3 / (1 /x + 1 /y + 1 /z)"
proof-
  have 1: "x*y*z = root 3 (x * y * z)^3"
    by (simp add: assms(1) assms(2) assms(3) real_root_pow_pos)
  then have "x*y*z = root 3 ((x * y * z) * (x * y * z)^2)"
    by (metis power2_eq_square power3_eq_cube power_commuting_commutes real_root_mult)
  then have "x*y*z = root 3 (x*y*z) * root 3 (x^2*y^2*z^2)"
    by (metis power_mult_distrib real_root_mult)
  then have "root 3 (x*y*z) = x*y*z / (root 3 (x^2*y^2*z^2))"
    by (metis "1" eq_divide_eq mult_eq_0_iff power_eq_0_iff)
  then have "(root 3 (x*y * y*z * z*x)) \<le> (x*y + y*z + z*x)/3"
    by (metis (full_types) AG3 assms(1) assms(2) assms(3) mult.assoc zero_less_mult_iff)  
  then have "1 / (root 3 (x*y * y*z * z*x)) \<ge> 1 / ((x*y + y*z + z*x)/3)"
    by (meson assms(1) assms(2) assms(3) frac_le le_numeral_extra(4) mult_pos_pos real_root_gt_zero zero_less_numeral zero_less_one_class.zero_le_one)
  then have "x*y*z / (root 3 (x*y * y*z * z*x)) \<ge> x*y*z / ((x*y + y*z + z*x)/3)"
    using assms
    by (smt (verit, ccfv_SIG) \<open>root 3 (x * y * y * z * z * x) \<le> (x * y + y * z + z * x) / 3\<close> frac_le mult_pos_pos real_root_gt_zero zero_less_numeral)
  then have "x*y*z / ((x*y + y*z + z*x)/3) = 3 * x*y*z / (x*y + y*z + z*x)"
    by simp
  then have "3 * x*y*z / (x*y + y*z + z*x) = 3 * x*y*z / ((x*y*z/z + x*y*z/y + x*y*z/x))"
    by force
  then have "3 * x*y*z / (x*y + y*z + z*x) = 3 * x*y*z / ((x*y*z*(1/z) + x*y*z*(1/y) + x*y*z*(1/x)))"
    by simp
  then have "3 * x*y*z / ((x*y*z/z + x*y*z/y + x*y*z/x)) =  3 * x*y*z / ((x*y*z) * (1/x + 1/y + 1/z))"
    by (simp add: distrib_left)
  then have "3 * x*y*z / ((x*y*z/z + x*y*z/y + x*y*z/x)) = 3 * (x*y*z) * 1/(x*y*z) * 1/(1/x + 1/y + 1/z)"
    by force
  then have "3 * x*y*z / ((x*y*z/z + x*y*z/y + x*y*z/x)) = 3 * (x*y*z)/(x*y*z) * 1/(1/x + 1/y + 1/z)"
    by force
  then have "3 * (x*y*z)/(x*y*z) * 1/(1/x + 1/y + 1/z) = 3 * 1/(1/x + 1/y + 1/z)"
    using assms(1) assms(2) assms(3) by auto
  then have "3 * (x*y*z)/(x*y*z) * 1/(1/x + 1/y + 1/z) = 3 / (1/x + 1/y + 1/z)"
    by auto
  then have "3 / (1/x + 1/y + 1/z) = (x*y*z)/((x*y + y*z + z*x)/3)"
    using \<open>3 * x * y * z / (x * y * z / z + x * y * z / y + x * y * z / x) = 3 * (x * y * z) / (x * y * z) * 1 / (1 / x + 1 / y + 1 / z)\<close> \<open>3 * x * y * z / (x * y + y * z + z * x) = 3 * x * y * z / (x * y * z / z + x * y * z / y + x * y * z / x)\<close> \<open>x * y * z / ((x * y + y * z + z * x) / 3) = 3 * x * y * z / (x * y + y * z + z * x)\<close> by presburger
  then have "3 / (1/x + 1/y + 1/z) \<le> x*y*z / (root 3 (x*y * y*z * z*x))"
    using \<open>x * y * z / ((x * y + y * z + z * x) / 3) \<le> x * y * z / root 3 (x * y * y * z * z * x)\<close> by presburger
  then show ?thesis
    by (metis (mono_tags, opaque_lifting) \<open>root 3 (x * y * z) = x * y * z / root 3 (x\<^sup>2 * y\<^sup>2 * z\<^sup>2)\<close> mult.commute mult.left_commute power2_eq_square)
qed

(* AH nejednakost za tri broja -- A \<ge> H na osnovu tranzitivnosti prethodne dve teoreme *)
lemma AH3 [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "(x + y + z) / 3 \<ge>  3 / (1 /x + 1 /y + 1 /z)"
proof-
  have "(x + y + z) / 3 \<ge>  root 3 (x*y*z)"
    using AG3 assms(1) assms(2) assms(3) by auto
  then have "(x + y + z) / 3 \<ge>  3 / (1 /x + 1 /y + 1 /z)"
    by (smt (verit, del_insts) GH3 assms(1) assms(2) assms(3))   
  then show ?thesis
    .  
qed

(* lema koja transformise harmonijsku sredinu u drugi oblik za koji vazi da je manji od nje*)
lemma pomocna2 [simp]:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "3 / (1 /x + 1 /y + 1 /z) \<ge> sqrt (3 / (1/x^2 + 1/y^2 + 1/z^2))"
  sorry

lemma drugi_deo [simp]:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a*b + b*c + c*a \<ge> 3*a*b*c"
  shows "sqrt(2*a*b/(a+b)) + sqrt(2*b*c/(b+c)) + sqrt(2*c*a/(c+a)) \<ge> 3"
  sorry


lemma glavna:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" 
  assumes "a*b + b*c + c*a \<le> 3 * a*b*c"
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
