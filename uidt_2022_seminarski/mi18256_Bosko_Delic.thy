theory mi18256_Bosko_Delic
  imports Complex_Main
begin

text \<open>transformisem levu stranu nejednakosti korenova
      sqrt(a + b - c) - sqrt a = (a + b - c - a) / (sqrt(a + b - c) + sqrt a)\<close>
lemma L_veza_korenova:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt(a + b - c) - sqrt a = (a + b - c - a) / (sqrt(a + b - c) + sqrt a)"
  by (smt (verit, del_insts) assms(1) assms(6) nonzero_mult_div_cancel_left real_sqrt_ge_zero real_sqrt_mult_self square_diff_square_factored)


text \<open>transformisem desnu stranu nejednakosti korenova
      (b - c) / (sqrt b + sqrt c) = sqrt b - sqrt c\<close>
lemma D_veza_korenova:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "(b - c) / (sqrt b + sqrt c) = sqrt b - sqrt c"
  by (smt (verit) assms(2) assms(3) nonzero_mult_div_cancel_left real_sqrt_lt_0_iff real_sqrt_mult_self square_diff_square_factored)


text \<open>pokazujem (a + b - c - a) / (sqrt(a + b - c) + sqrt a) \<le> (b - c) / (sqrt b + sqrt c)
 tj. L_veza_korenova \<le> D_veza_korenova\<close>
lemma nejednakost_korenova:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "(a + b - c - a) / (sqrt(a + b - c) + sqrt a) \<le> (b - c) / (sqrt b + sqrt c)"
  by (smt (verit, ccfv_SIG) assms(3) assms(4) assms(5) frac_le real_sqrt_gt_0_iff real_sqrt_le_mono)


text \<open> povezujem levu i desnu transformisanu stranu u nejednakost
 sqrt(a + b - c) - sqrt a \<le> sqrt b - sqrt c\<close>
lemma veza_korenova:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt(a + b - c) - sqrt a \<le> sqrt b - sqrt c"
  using assms
  using D_veza_korenova L_veza_korenova nejednakost_korenova by force


text \<open>pokazujem da je veza_korenova \<le> 1\<close>
lemma manje_od_jedan:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt (a + b - c) / (sqrt (a) + sqrt (b) - sqrt (c)) \<le> 1"
  using assms
  by (smt (verit) divide_le_eq_1 real_sqrt_gt_0_iff veza_korenova)




text \<open>posto treba da pokazemo da je konacna nejednakost \<le> 3, a upravo smo pokazali da je
 jedan od njenih sabiraka \<le> 1, onda za ostala dva sabirka treba pokazati da su \<le> 2\<close>

text \<open>pomocne teoreme za nejednakost_kvadrata\<close>
lemma kvadrat_binoma_levo:
  fixes a b c d :: real
  shows "(a*c + b*d)^2 = a^2 * c^2 + 2*a*c*b*d + b^2 * d^2"
  by (simp add: power2_sum power_mult_distrib)


lemma kvadrat_binoma_desno:
  fixes a b c d :: real
  shows "a^2 * d^2 - 2*a*d*b*c + b^2 * c^2 = (a*d - b*c)^2"
  by (simp add: power2_diff power_mult_distrib)


text\<open>pokazujem (a^2 + b^2) * (c^2 + d^2) \<ge> (a*c + b*d)^2\<close>
lemma nejednakost_kvadrata:
  fixes a b c d :: real
  shows "(a^2 + b^2) * (c^2 + d^2) - (a*c + b*d)^2 \<ge> 0"
proof -
  have "(a^2 + b^2) * (c^2 + d^2) - (a*c + b*d)^2 = a^2 * c^2 + a^2 * d^2 + b^2 * c^2 + b^2 * d^2
  - (a^2 * c^2 + 2*a*c*b*d + b^2 * d^2)"
    by (simp add: kvadrat_binoma_levo ring_class.ring_distribs(1) ring_class.ring_distribs(2))
  also have "... = a^2 * d^2 + b^2 * c^2 - 2*a*c*b*d" by auto
  also have "... = a^2 * d^2 - 2*a*d*b*c + b^2 * c^2" by auto
  also have "... = (a*d - b*c)^2"
    by (simp add: kvadrat_binoma_desno)
  finally show ?thesis by auto
qed


text \<open>drugi oblik prethodne leme\<close>
lemma nejednakost_kvadrata_dva:
  fixes a b c d :: real
  shows "(a*c + b*d)^2 \<le> (a^2 + b^2) * (c^2 + d^2)"
  using nejednakost_kvadrata by auto


lemma jedan_kroz_kvadrat_koren:
  fixes a :: real
  assumes "a > 0"
  shows "1 / (sqrt a) ^ 2 = 1 / a" 
  using assms by auto


lemma broj_kroz_koren:
  fixes a b :: real
  assumes "a > 0" "b > 0"
  shows "a / b = a / (sqrt b)^2"
  using assms by auto


lemma proizvod_koren:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  shows "a * b / c = a * sqrt(b / c)^2"
  using assms(2) assms(3) by force


text \<open>pokazujem da su preostali sabirci manji od 2\<close>
lemma pom1:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt(c + a - b) / (sqrt c + sqrt a - sqrt b) = sqrt(c + a - b) / sqrt(sqrt c + sqrt a - sqrt b) * (1 / sqrt(sqrt c + sqrt a - sqrt b))"
proof -
  have "sqrt(c + a - b) / (sqrt c + sqrt a - sqrt b) = sqrt(c + a - b) / sqrt(sqrt c + sqrt a - sqrt b)^2"
    by (smt (verit) assms(3) assms(4) broj_kroz_koren real_sqrt_gt_zero real_sqrt_le_iff)
  also have "... = sqrt(c + a - b) / sqrt(sqrt c + sqrt a - sqrt b) * (1 / sqrt(sqrt c + sqrt a - sqrt b))"
    by (simp add: power2_eq_square)
  finally show ?thesis by auto
qed


lemma pom2:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt b + sqrt c > sqrt a"
  using assms
proof -
  have "(sqrt b + sqrt c)^2 = b + 2 * sqrt b * sqrt c + c"
    by (smt (verit) assms(2) assms(3) power2_sum real_sqrt_pow2)
  also have "... > a"
    by (smt (verit, ccfv_SIG) assms(3) assms(5) assms(7) mult_pos_pos real_sqrt_gt_zero)
  finally show ?thesis
    using assms(4) assms(5) assms(7) real_less_lsqrt by auto
qed


lemma pom3:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt(b + c - a) / (sqrt b + sqrt c - sqrt a) = sqrt(b + c - a) / sqrt(sqrt b + sqrt c - sqrt a) * (1 / sqrt(sqrt b + sqrt c - sqrt a))"
proof -
  have "sqrt(b + c - a) / (sqrt b + sqrt c - sqrt a) = sqrt(b + c - a) / sqrt(sqrt b + sqrt c - sqrt a)^2"
    using pom2 by (simp add: assms(4) assms(5) assms(7) broj_kroz_koren)
  also have "... = sqrt(b + c - a) / sqrt(sqrt b + sqrt c - sqrt a) * (1 / sqrt(sqrt b + sqrt c - sqrt a))"
    by (simp add: power2_eq_square)
  finally show ?thesis by auto
qed


lemma pom4:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
    "sqrt a + sqrt b > sqrt c" "sqrt a + sqrt c > sqrt b"
  shows "sqrt(c - a + b) / (sqrt c - sqrt a + sqrt b) + sqrt(c + a - b) / (sqrt c + sqrt a - sqrt b)
   = sqrt(c - a + b) / sqrt(sqrt c - sqrt a + sqrt b) * (1 / sqrt(sqrt c - sqrt a + sqrt b))
   + sqrt(c + a - b) / sqrt(sqrt c + sqrt a - sqrt b) * (1 / sqrt(sqrt c + sqrt a - sqrt b))"
proof -
  have "sqrt(c - a + b) / (sqrt c - sqrt a + sqrt b) = sqrt(c - a + b) / sqrt(sqrt c - sqrt a + sqrt b) * (1 / sqrt(sqrt c - sqrt a + sqrt b))"
    by (smt (verit) assms(4) assms(5) assms(7) pom3)
  also have "sqrt(c + a - b) / (sqrt c + sqrt a - sqrt b) = sqrt(c + a - b) / sqrt(sqrt c + sqrt a - sqrt b) * (1 / sqrt(sqrt c + sqrt a - sqrt b))"
    using assms(4) assms(5) assms(7) pom1 by force
  from this show ?thesis
    using \<open>sqrt (c + a - b) / (sqrt c + sqrt a - sqrt b) = sqrt (c + a - b) / sqrt (sqrt c + sqrt a - sqrt b) * (1 / sqrt (sqrt c + sqrt a - sqrt b))\<close> \<open>sqrt (c - a + b) / (sqrt c - sqrt a + sqrt b) = sqrt (c - a + b) / sqrt (sqrt c - sqrt a + sqrt b) * (1 / sqrt (sqrt c - sqrt a + sqrt b))\<close> by presburger  
qed


lemma pom5:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
    "sqrt a + sqrt b > sqrt c" "sqrt a + sqrt c > sqrt b"
  shows "(sqrt(c + a - b) / (sqrt c + sqrt a - sqrt b) + sqrt(c + b - a) / (sqrt c + sqrt b - sqrt a))^2
  \<le> ((c - a + b) / (sqrt c - sqrt a + sqrt b) + (c + a - b) / (sqrt c + sqrt a - sqrt b)) * (1 / (sqrt c - sqrt a + sqrt b) + 1 / (sqrt c + sqrt a - sqrt b))"
  sorry



lemma pom6:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt a + sqrt b \<ge> 2 * sqrt c"
  by (smt (verit, ccfv_threshold) assms(4) assms(5) real_sqrt_le_mono)

text \<open>dokaz konacne nejednakosti\<close>

lemma final_theorem:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b" (* posto a, b, c stranice trougla *)
  shows "(sqrt(b + c - a)) / (sqrt (b) + sqrt (c) - sqrt (a)) + 
sqrt((c + a - b)) / (sqrt (c) + sqrt (a) - sqrt (b)) +
(sqrt(a + b - c)) / (sqrt (a) + sqrt (b) - sqrt (c)) \<le> 3"
  using assms
  sorry



end