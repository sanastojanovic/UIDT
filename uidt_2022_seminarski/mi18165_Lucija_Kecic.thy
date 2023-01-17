theory mi18165_Lucija_Kecic
  imports Main Complex_Main

begin

(*Let a, b and c be positive real numbers
satisfying min(a+b, b+c, c+a) > √2 and
a^2+b^2+c^2=3
Prove that
a/(b+c-a)^2 + b/(c+a-b)^2+c/(a+b-c)^2≥3/(a*b*c)^2
*)

fun min :: "real ⇒ real ⇒ real ⇒ real" where
  "min a b c =
	(if a≥b | c≥b then b
	else if a≥c | b≥c then c
	else a)"

lemma problem:
  fixes a b c :: "real"
  assumes "a>0" "b>0" "c>0"
  assumes "min(a+b)(b+c)(c+a) > sqrt(2)"
(*ovaj uslov znaci da je svaki zbir > 1/2*)
  assumes "a^2 + b^2 + c^2 = 3"
  shows "a/(b+c-a)^2 + b/(c+a-b)^2 + c/(a+b-c)^2 ≥ 3/(a*b*c)^2"
  using assms
  oops

lemma am_qm_inequality:
  shows "sqrt((a^2 + b^2)/2)≥(a+b)/2"
proof -
  have "(a+b)^2 = a^2 + 2*a*b + b^2"
   (* by sledgehammer*)
	by (simp add: power2_sum)
  then have "(a+b)^2 ≤ 2*(a^2+b^2)"
   (* by sledgehammer*)
	by (smt (verit) sum_squares_bound)
  then have "a+b ≤ sqrt(2*(a^2+b^2))"
   (* by sledgehammer*)
	using real_le_rsqrt by presburger
  then have "a+b ≤ sqrt(2)*sqrt(a^2+b^2)"
	using real_sqrt_mult by metis
  then show "(a+b)/2 ≤ sqrt((a^2+b^2)/2)"
	(*by sledgehammer*)
	by (smt (z3) field_sum_of_halves power2_eq_square real_divide_square_eq real_sqrt_divide real_sqrt_pow2)
qed
   


lemma sq_gt_one:
  fixes b c :: real
  assumes "b>0" "c>0"
  assumes "b+c > sqrt(2)"
  shows "b^2 + c^2 > 1"
proof -
  have "sqrt((b^2+c^2)/2) ≥ (b+c)/2"
	using am_qm_inequality by auto
  then have "sqrt((b^2+c^2)/2) > sqrt(2)/2"
	using assms by simp (*sledgehammer*)
  then have "sqrt(b^2+c^2)> sqrt(2)*sqrt(2)/ 2"
	(*by sledgehammer*)
	by (simp add: pos_less_divide_eq real_sqrt_divide)
  then have "sqrt(b^2+c^2) > 1"
	by auto
  then show "b^2+c^2 > 1"
	by auto
qed

lemma a_lt_sqrt_two:
  fixes a b c :: "real"
  assumes "a>0" "b>0" "c>0"
  assumes "b^2+c^2 > 1"
  assumes "a^2+b^2 > 1"
  assumes "a^2+b^2+c^2=3"
  shows "a<sqrt(2)"
proof -
  have "a^2 = 3-(b^2+c^2)"
	using assms by auto
  then show "a<sqrt(2)"
	using assms (*by sledgehammer*) by (simp add: real_less_rsqrt)
qed

lemma equation_gt_zero:
  fixes a b c :: "real"
  assumes "a<sqrt(2)"
  assumes "sqrt(2)<b+c"
  shows "b+c-a > 0"
  using assms by auto

(* HOLDER:
x1^(p+1)/y1^p + ... + xn^(p+1)/yn^p ≥ (x1+...+xn)^(p+1)/(y1+...+yn)^p
u nasem slucaju p=2, n=3
*)

lemma holders_inequality:
  fixes x1 x2 x3 y1 y2 y3 :: "real"
  assumes "x1>0" "x2>0" "x3>0" "y1>0" "y2>0" "y3>0"
  shows "x1^3/y1^2 + x2^3/y2^2 + x3^3/y3^2 ≥ (x1+x2+x3)^3/(y1+y2+y3)^2"
  using assms
  sorry

lemma apply_holder_left_mid:
  fixes a b c :: "real"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a^2 + b^2 + c^2 = 3"
  shows  "((a^2)^3) / (a^5 * (b + c - a)^2) + ((b^2)^3) / (b^5 * (a + c - b)^2)  + ((c^2)^3) / (c^5 * (a + b - c)^2) ≥ (a^2 + b^2 + c^2)^3 / (sqrt(a^5) * (b + c - a) + sqrt(b^5) * (a + c - b) + sqrt(c^5) * (a + b - c))^2"
  using assms
  sorry

lemma fraction_multiplication:
  fixes x y :: "real"
  shows "x/y = (x^2)^3/(x^5*y)"
  by (smt (verit, ccfv_SIG) divide_eq_0_iff divide_pos_pos eval_nat_numeral(3) frac_eq_eq mult.assoc mult_eq_0_iff num_double numeral_times_numeral power2_eq_square power_Suc power_odd_eq)

lemma apply_holder_left:
  fixes a b c :: "real"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a^2 + b^2 + c^2 = 3"
  shows "a/(b+c-a)^2+b/(a+c-b)^2+c/(a+b-c)^2 ≥ 27/(sqrt(a^5)*(b+c-a)+sqrt(b^5)*(a+c-b)+sqrt(c^5)*(a+b-c))^2"
proof -
  have fraca: "a/(b+c-a)^2 = ((a^2)^3)/(a^5*(b+c-a)^2)"
	using fraction_multiplication by auto
  have fracb: "b/(a+c-b)^2 = ((b^2)^3)/(b^5*(a+c-b)^2)"
	using fraction_multiplication by auto
  have fracc: "c/(a+b-c)^2 = ((c^2)^3)/(c^5*(a+b-c)^2)"
	using fraction_multiplication by auto
  from fraca fracb fracc have eq1: "a/(b+c-a)^2+b/(a+c-b)^2+c/(a+b-c)^2 = ((a^2)^3)/(a^5*(b+c-a)^2)+((b^2)^3)/(b^5*(a+c-b)^2)+((c^2)^3)/(c^5*(a+b-c)^2)"
	by simp
  also have eq2: "((a^2)^3)/(a^5*(b+c-a)^2)+(b^2)^3/(b^5*(a+c-b)^2)+(c^2)^3/(c^5*(a+b-c)^2) ≥ (a^2+b^2+c^2)^3/(sqrt(a^5)*(b+c-a)+sqrt(b^5)*(a+c-b)+sqrt(c^5)*(a+b-c))^2"
	using assms apply_holder_left_mid by metis
  have final: "(a^2+b^2+c^2)^3/(sqrt(a^5)*(b+c-a)+sqrt(b^5)*(c+a-b)+sqrt(c^5)*(a+b-c))^2 = 27/(sqrt(a^5)*(b+c-a)+sqrt(b^5)*(c+a-b)+sqrt(c^5)*(a+b-c))^2"
	using assms by auto
  from eq1 eq2 final show "a/(b+c-a)^2+b/(a+c-b)^2+c/(a+b-c)^2 ≥ 27/(sqrt(a^5)*(b+c-a)+sqrt(b^5)*(a+c-b)+sqrt(c^5)*(a+b-c))^2"
	by (smt (verit, del_insts))
qed

lemma schur:
  fixes a b c :: "real"
  assumes "a>0" "b>0" "c>0"
  assumes "a^2+b^2+c^2 = 3"
  assumes "a ≥ b" "b ≥ c"
  shows "sqrt(a^3)*(a-b)*(a-c)+sqrt(b^3)*(b-a)*(b-c)+sqrt(c^3)*(c-a)*(c-b) ≥ 0"
proof -
  have a1: "a-b ≥ 0"
	using assms by auto
  have a2: "a-c ≥ 0"
	using assms by auto
  have a3: "(a-b)*(a-c) ≥ 0"
	using a1 a2 mult_nonneg_nonneg by blast
  then have "sqrt(a^3)*(a-b)*(a-c) ≥ 0"
	using a1 a2 assms(1) by auto
  have b1: "b-c ≥ 0"
	using assms by auto
  have b2:  "b-a ≤ 0"
	using assms by auto
  have b3: "(b-a)*(b-c) ≤ 0"
	using b1 b2 by (simp add: mult_nonneg_nonpos2)
  then have "sqrt(b^3)*(b-a)*(b-c) ≤ 0"
	using b1 b2 b3 assms(1) by (smt (verit, del_insts) assms(2) mult_nonneg_nonpos2 real_sqrt_le_0_iff zero_less_mult_pos zero_less_power)
  then have "sqrt(b^3)*(-(a-b))*(b-c) ≤ 0"
	by simp
  then have "-sqrt(b^3)*(a-b)*(b-c) ≤ 0"
	by linarith
  have eq1: "sqrt(a^3)*(a-b)*(a-c)+sqrt(b^3)*(b-a)*(b-c) = sqrt(a^3)*(a-b)*(a-c)-sqrt(b^3)*(a-b)*(b-c)"
	by (smt (verit, ccfv_SIG) mult_minus_left mult_minus_right)
  then have eq2: "sqrt(a^3)*(a-b)*(a-c)-sqrt(b^3)*(a-b)*(b-c) = (a-b)*(sqrt(a^3)*(a-c)-sqrt(b^3)*(b-c))"
	by (simp add: mult.commute right_diff_distrib')
  then have eq3: "sqrt(a^3)*(a-b)*(a-c)+sqrt(b^3)*(b-a)*(b-c) = (a-b)*(sqrt(a^3)*(a-c)-sqrt(b^3)*(b-c))"
	using eq1 by presburger
  have "a-c ≥ b-c"
	using assms a2 b2 by auto
  then have "sqrt(a^3)*(a-c) ≥ sqrt(b^3)*(b-c)"
	by (smt (verit, ccfv_SIG) assms(2) b1 mult_strict_mono not_gr_zero power_strict_mono real_sqrt_le_0_iff real_sqrt_less_iff zero_less_power zero_neq_numeral)
  then have ab: "(a-b)*(sqrt(a^3)*(a-c)-sqrt(b^3)*(b-c)) ≥ 0"
	using a1 by auto
  have c1: "c-a ≤ 0"
	using assms by auto
  have c2: "c-b ≤ 0"
	using assms by auto
  have c3: "(c-a)*(c-b) ≥ 0"
	using c1 c2 mult_nonpos_nonpos by blast
  then have c4: "sqrt(c^3)*(c-a)*(c-b) ≥ 0"
	using c1 c2 by (smt (verit, del_insts) assms(3) mult_nonpos_nonpos real_sqrt_le_0_iff zero_less_mult_pos zero_less_power)
  show "sqrt(a^3)*(a-b)*(a-c)+sqrt(b^3)*(b-a)*(b-c)+sqrt(c^3)*(c-a)*(c-b) ≥ 0"
	using assms ab c4 eq3 by auto
qed

lemma h1:
  fixes a b c :: "real"
  assumes "a>0" "b>0" "c>0"
  shows "(a-b)*(a-c) = a^2-a*b-a*c+b*c"
proof -
  have "(a-b)*(a-c) = a*(a-b)-c*(a-b)"
	by (metis left_diff_distrib mult.commute)
  then have "(a-b)*(a-c) = a*a-a*b-a*c+b*c"
	by (smt (verit, del_insts) distrib_right mult.commute)
  then show "(a-b)*(a-c) = a^2-a*b-a*c+b*c"
	by (simp add: power2_eq_square)
qed

lemma h3:
  fixes a :: "real"
  assumes "a>0"
  shows "sqrt(a^3)*a = sqrt(a^5)"
proof -
  have "sqrt(a^3)*a = sqrt(a^3)*sqrt(a)*sqrt(a)"
	using assms by auto
  then have "sqrt(a^3)*a = sqrt(a^3*a)*sqrt(a)"
	using real_sqrt_mult by presburger
  then have "sqrt(a^3)*a = sqrt(a^3*a*a)"
	using real_sqrt_mult by presburger
  then show "sqrt(a^3)*a = sqrt(a^5)"
	by (metis eval_nat_numeral(3) power3_eq_cube power4_eq_xxxx power_Suc2)
qed

lemma h2:
  fixes a b c :: "real"
  assumes "a>0" "b>0" "c>0"
  shows "sqrt(a^3)*(a^2-a*b-a*c+b*c) = a*sqrt(a^5)-b*sqrt(a^5)-c*sqrt(a^5)+a*b*c*sqrt(a)"
proof -
  have a0: "sqrt(a^3)*(a^2-a*b-a*c+b*c) = a^2*sqrt(a^3)-a*b*sqrt(a^3)-a*c*sqrt(a^3)+b*c*sqrt(a^3)"
	by (smt (verit, best) left_diff_distrib mult.commute)
  have a1: "a^2*sqrt(a^3) = a*sqrt(a^5)"
	using assms h3 by (simp add: mult.commute power2_eq_square)
  have a2: "a*b*sqrt(a^3) = b*sqrt(a^5)"
	using assms h3 by (simp add: mult.commute)
  have a3: "b*c*sqrt(a^3) = a*b*c*sqrt(a)"
	using assms by (smt (verit, del_insts) Groups.mult_ac(1) Groups.mult_ac(3) power3_eq_cube real_sqrt_mult_self real_sqrt_power)
  from a1 a2 a3 show "sqrt(a^3)*(a^2-a*b-a*c+b*c) = a*sqrt(a^5)-b*sqrt(a^5)-c*sqrt(a^5)+a*b*c*sqrt(a)"
	by (smt (verit) a0 assms(1) h3 mult.assoc mult.commute)
qed

lemma rewritten_schur:
  fixes a b c :: "real"
  assumes "a>0" "b>0" "c>0"
  assumes "a^2+b^2+c^2 = 3"
  assumes "a ≥ b" "b ≥ c"
  shows "sqrt(a^5)*(b+c-a)+sqrt(b^5)*(c+a-b)+sqrt(c^5)*(a+b-c) ≤ a*b*c*(sqrt(a)+sqrt(b)+sqrt(c))"
proof -
  have schur1: "sqrt(a^3)*(a-b)*(a-c)+sqrt(b^3)*(b-a)*(b-c)+sqrt(c^3)*(c-a)*(c-b) ≥ 0"
	using assms schur by auto
  have a1: "sqrt(a^3)*(a-b)*(a-c) = sqrt(a^3)*(a^2-a*b-a*c+b*c)"
	using assms h1 by auto
  have b1: "sqrt(b^3)*(b-a)*(b-c) = sqrt(b^3)*(b^2-a*b-b*c+a*c)"
	using assms h1 by auto
  have c1: "sqrt(c^3)*(c-a)*(c-b) = sqrt(c^3)*(c^2-a*c-b*c+a*b)"
	using assms h1 by auto
  have a2: "sqrt(a^3)*(a^2-a*b-a*c+b*c) = a*sqrt(a^5)-b*sqrt(a^5)-c*sqrt(a^5)+a*b*c*sqrt(a)"
	using assms h2 by auto
  have b2: "sqrt(b^3)*(b^2-b*a-b*c+a*c) = b*sqrt(b^5)-a*sqrt(b^5)-c*sqrt(b^5)+a*b*c*sqrt(b)"
	using assms h2 by auto
  have c2: "sqrt(c^3)*(c^2-c*a-c*b+a*b) = c*sqrt(c^5)-a*sqrt(c^5)-b*sqrt(c^5)+a*b*c*sqrt(c)"
	using assms h2 by auto
  then have abc1: "sqrt(a^3)*(a-b)*(a-c)+sqrt(b^3)*(b-a)*(b-c)+sqrt(c^3)*(c-a)*(c-b) = a*sqrt(a^5)-b*sqrt(a^5)-c*sqrt(a^5)+a*b*c*sqrt(a)+b*sqrt(b^5)-a*sqrt(b^5)-c*sqrt(b^5)+a*b*c*sqrt(b)+c*sqrt(c^5)-a*sqrt(c^5)-b*sqrt(c^5)+a*b*c*sqrt(c)"
	using assms a2 b2 c2 by (smt (verit) a1 b1 c1 mult.commute)
  then have "a*sqrt(a^5)-b*sqrt(a^5)-c*sqrt(a^5)+a*b*c*sqrt(a)+b*sqrt(b^5)-a*sqrt(b^5)-c*sqrt(b^5)+a*b*c*sqrt(b)+c*sqrt(c^5)-a*sqrt(c^5)-b*sqrt(c^5)+a*b*c*sqrt(c) ≥ 0"
	using schur1 by presburger
  have abc: "a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)) = a*b*c*sqrt(a)+a*b*c*sqrt(b)+a*b*c*sqrt(c)"
	using assms by (smt (verit, best) left_diff_distrib mult.commute)
  have a3: "sqrt(a^5)*(a-b-c) = a*sqrt(a^5)-b*sqrt(a^5)-c*sqrt(a^5)"
	using assms by (smt (verit, best) left_diff_distrib mult.commute)
  have b3: "sqrt(b^5)*(b-a-c) = b*sqrt(b^5)-a*sqrt(b^5)-c*sqrt(b^5)"
	using assms by (smt (verit, best) left_diff_distrib mult.commute)
  have c3: "sqrt(c^5)*(c-a-b) = c*sqrt(c^5)-a*sqrt(c^5)-b*sqrt(c^5)"
	using assms by (smt (verit, best) left_diff_distrib mult.commute)
  then have abc2: "a*sqrt(a^5)-b*sqrt(a^5)-c*sqrt(a^5)+a*b*c*sqrt(a)+b*sqrt(b^5)-a*sqrt(b^5)-c*sqrt(b^5)+a*b*c*sqrt(b)+c*sqrt(c^5)-a*sqrt(c^5)-b*sqrt(c^5)+a*b*c*sqrt(c) = a*b*c*(sqrt(a)+sqrt(b)+sqrt(c))+sqrt(a^5)*(a-b-c)+sqrt(b^5)*(b-a-c)+sqrt(c^5)*(c-a-b)"
	using a3 abc b3 by fastforce
  then have "a*b*c*(sqrt(a)+sqrt(b)+sqrt(c))+sqrt(a^5)*(a-b-c)+sqrt(b^5)*(b-a-c)+sqrt(c^5)*(c-a-b) = a*b*c*(sqrt(a)+sqrt(b)+sqrt(c))-sqrt(a^5)*(b+c-a)-sqrt(b^5)*(a+c-b)-sqrt(c^5)*(a+b-c)"
	by (smt (verit) mult_minus_right)
  then have "a*b*c*(sqrt(a)+sqrt(b)+sqrt(c))-sqrt(a^5)*(b+c-a)-sqrt(b^5)*(a+c-b)-sqrt(c^5)*(a+b-c) ≥ 0"
	using abc1 abc2 schur1 by presburger
  then have "a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)) ≥ sqrt(a^5)*(b+c-a)+sqrt(b^5)*(a+c-b)+sqrt(c^5)*(a+b-c)"
	by linarith
  then show "sqrt(a^5)*(b+c-a)+sqrt(b^5)*(c+a-b)+sqrt(c^5)*(a+b-c) ≤ a*b*c*(sqrt(a)+sqrt(b)+sqrt (c))"
	by (smt (verit))
qed

lemma am_fpm:
  fixes a b c :: "real"
  assumes "a>0" "b>0" "c>0"
  assumes "a^2+b^2+c^2 = 3"
  shows "((sqrt(a)+sqrt(b)+sqrt(c))/3)^4 ≤ (a^2+b^2+c^2)/3"
  sorry

lemma sq_sum_lt_three:
  fixes a b c :: "real"
  assumes "a>0" "b>0" "c>0"
  assumes "a^2+b^2+c^2 = 3"
  shows "sqrt(a)+sqrt(b)+sqrt(c) ≤ 3"
proof -
  have "((sqrt(a)+sqrt(b)+sqrt(c))/3)^4 ≤ (a^2+b^2+c^2)/3"
	using assms am_fpm by auto
  then have "((sqrt(a)+sqrt(b)+sqrt(c))/3)^4 ≤ 1"
	using assms by auto
  then have "(sqrt(a)+sqrt(b)+sqrt(c))/3 ≤ 1"
	by (smt (verit, ccfv_threshold) mult.right_neutral nat_1_add_1 numeral_Bit0 one_le_power power2_eq_square power2_sum power_mult real_sqrt_abs real_sqrt_one)
  then show "sqrt(a)+sqrt(b)+sqrt(c) ≤ 3"
	by simp
qed

lemma left:
  fixes a b c :: "real"
  assumes "a>0" "b>0" "c>0"
  assumes "a^2+b^2+c^2 = 3"
  assumes "a ≥ b" "b ≥ c"
  assumes "sqrt(a^5)*(b+c-a)+sqrt(b^5)*(c+a-b)+sqrt(c^5)*(a+b-c) > 0"
  assumes "a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)) > 0"
  assumes "a+b-c > 0" "b+c-a > 0" "c+a-b > 0"
  shows "a/(b+c-a)^2+b/(a+c-b)^2+c/(a+b-c)^2 ≥ 27/(a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)))^2"
proof -
  have l1: "a/(b+c-a)^2+b/(a+c-b)^2+c/(a+b-c)^2 ≥ 27/(sqrt(a^5)*(b+c-a)+sqrt(b^5)*(a+c-b)+sqrt(c^5)*(a+b-c))^2"
	using assms apply_holder_left by auto
  have "sqrt(a^5)*(b+c-a)+sqrt(b^5)*(c+a-b)+sqrt(c^5)*(a+b-c) ≤ a*b*c*(sqrt(a)+sqrt(b)+sqrt(c))"
	using assms rewritten_schur by auto
  then have "(sqrt(a^5)*(b+c-a)+sqrt(b^5)*(c+a-b)+sqrt(c^5)*(a+b-c))^2 ≤ (a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)))^2"
	using assms by auto
  then have "1/(sqrt(a^5)*(b+c-a)+sqrt(b^5)*(c+a-b)+sqrt(c^5)*(a+b-c))^2 ≥ 1/(a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)))^2"
	using assms rewritten_schur by (smt (verit) frac_le zero_less_power)
  then have l2:  "27/(sqrt(a^5)*(b+c-a)+sqrt(b^5)*(c+a-b)+sqrt(c^5)*(a+b-c))^2 ≥ 27/(a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)))^2"
	by auto
  from l1 l2 show "a/(b+c-a)^2+b/(a+c-b)^2+c/(a+b-c)^2 ≥ 27/(a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)))^2"
	using assms by (smt (verit))
qed

lemma right:
  fixes a b c :: "real"
  assumes "a>0" "b>0" "c>0"
  assumes "a^2+b^2+c^2 = 3"
  assumes "a ≥ b" "b ≥ c"
  assumes "sqrt(a) > 0" "sqrt(b) > 0" "sqrt(c) > 0"
  assumes "sqrt(a)+sqrt(b)+sqrt(c) > 0"
  assumes "a*b*c > 0"
  assumes "a+b-c > 0" "b+c-a > 0" "c+a-b > 0"
  shows "27/(a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)))^2 ≥ 3/(a*b*c)^2"
proof -
  have "sqrt(a)+sqrt(b)+sqrt(c) ≤ 3"
	using assms sq_sum_lt_three by auto
  then have "a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)) ≤ 3*a*b*c"
	using assms by simp
  then have "(a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)))^2 ≤ (3*a*b*c)^2"
	using assms by auto
  then have "(a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)))^2 ≤ 9*(a*b*c)^2"
	using assms by (simp add: power2_eq_square)
  then have "1/(a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)))^2 ≥ 1/(9*(a*b*c)^2)"
	using assms by (simp add: frac_le)
  then have "27/(a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)))^2 ≥ 27/(9*(a*b*c)^2)"
	by auto
  then show "27/(a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)))^2 ≥ 3/(a*b*c)^2"
	by auto
qed

lemma solution:
  fixes a b c :: "real"
  assumes "a>0" "b>0" "c>0"
  assumes "a^2+b^2+c^2 = 3"
  assumes "a ≥ b" "b ≥ c"
  assumes "sqrt(a) > 0" "sqrt(b) > 0" "sqrt(c) > 0"
  assumes "sqrt(a)+sqrt(b)+sqrt(c) > 0"
  assumes "a*b*c > 0"
  assumes "a+b-c > 0" "b+c-a > 0" "c+a-b > 0"
  assumes "sqrt(a^5)*(b+c-a)+sqrt(b^5)*(c+a-b)+sqrt(c^5)*(a+b-c) > 0"
  shows "a/(b+c-a)^2 + b/(c+a-b)^2 + c/(a+b-c)^2 ≥ 3/(a*b*c)^2"
proof -
  have l: "a/(b+c-a)^2+b/(a+c-b)^2+c/(a+b-c)^2 ≥ 27/(a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)))^2"
	using assms left by auto
  have r: "27/(a*b*c*(sqrt(a)+sqrt(b)+sqrt(c)))^2 ≥ 3/(a*b*c)^2"
	using assms right by auto
  from l r show "a/(b+c-a)^2 + b/(c+a-b)^2 + c/(a+b-c)^2 ≥ 3/(a*b*c)^2"
	using assms by (smt (verit))
qed

end
