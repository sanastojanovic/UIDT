theory mi18256_Bosko_Delic
  imports Complex_Main
begin

text ‹2006 - A5 Olimpijada
Neka su a, b, c stranice trougla, pokazati da vazi:

sqrt(b + c - a) / (sqrt b + sqrt c - sqrt a) +
sqrt(c + a - b) / (sqrt c + sqrt a - sqrt b) +
sqrt(a + b - c) / (sqrt a + sqrt b - sqrt c) ≤ 3
›


text ‹transformisem levu stranu nejednakosti korenova
      sqrt(a + b - c) - sqrt a = (a + b - c - a) / (sqrt(a + b - c) + sqrt a)›
lemma L_veza_korenova:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a ≥ b" "b ≥ c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt(a + b - c) - sqrt a = (a + b - c - a) / (sqrt(a + b - c) + sqrt a)"
  by (smt (verit, del_insts) assms(1) assms(6) nonzero_mult_div_cancel_left real_sqrt_ge_zero real_sqrt_mult_self square_diff_square_factored)


text ‹transformisem desnu stranu nejednakosti korenova
      (b - c) / (sqrt b + sqrt c) = sqrt b - sqrt c›
lemma D_veza_korenova:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a ≥ b" "b ≥ c" "a + b > c" "b + c > a" "a + c > b"
  shows "(b - c) / (sqrt b + sqrt c) = sqrt b - sqrt c"
  by (smt (verit) assms(2) assms(3) nonzero_mult_div_cancel_left real_sqrt_lt_0_iff real_sqrt_mult_self square_diff_square_factored)


text ‹pokazujem (a + b - c - a) / (sqrt(a + b - c) + sqrt a) ≤ (b - c) / (sqrt b + sqrt c)
 tj. L_veza_korenova ≤ D_veza_korenova›
lemma nejednakost_korenova:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a ≥ b" "b ≥ c" "a + b > c" "b + c > a" "a + c > b"
  shows "(a + b - c - a) / (sqrt(a + b - c) + sqrt a) ≤ (b - c) / (sqrt b + sqrt c)"
  by (smt (verit, ccfv_SIG) assms(3) assms(4) assms(5) frac_le real_sqrt_gt_0_iff real_sqrt_le_mono)


text ‹ povezujem levu i desnu transformisanu stranu u nejednakost
 sqrt(a + b - c) - sqrt a ≤ sqrt b - sqrt c›
lemma veza_korenova:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a ≥ b" "b ≥ c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt(a + b - c) - sqrt a ≤ sqrt b - sqrt c"
  using assms
  using D_veza_korenova L_veza_korenova nejednakost_korenova by force


text ‹pokazujem da je veza_korenova ≤ 1›
lemma manje_od_jedan:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a ≥ b" "b ≥ c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt (a + b - c) / (sqrt (a) + sqrt (b) - sqrt (c)) ≤ 1"
  using assms
  by (smt (verit) divide_le_eq_1 real_sqrt_gt_0_iff veza_korenova)


text ‹posto treba da pokazemo da je konacna nejednakost ≤ 3, a upravo smo pokazali da je
 jedan od njenih sabiraka ≤ 1, onda za ostala dva sabirka treba pokazati da su ≤ 2›

text ‹pomocne teoreme za nejednakost_kvadrata›
lemma kvadrat_binoma_levo:
  fixes a b c d :: real
  shows "(a*c + b*d)^2 = a^2 * c^2 + 2*a*c*b*d + b^2 * d^2"
  by (simp add: power2_sum power_mult_distrib)


lemma kvadrat_binoma_desno:
  fixes a b c d :: real
  shows "a^2 * d^2 - 2*a*d*b*c + b^2 * c^2 = (a*d - b*c)^2"
  by (simp add: power2_diff power_mult_distrib)


text‹pokazujem (a^2 + b^2) * (c^2 + d^2) ≥ (a*c + b*d)^2›
lemma nejednakost_kvadrata:
  fixes a b c d :: real
  shows "(a^2 + b^2) * (c^2 + d^2) - (a*c + b*d)^2 ≥ 0"
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


text ‹drugi oblik prethodne leme›
lemma nejednakost_kvadrata_dva:
  fixes a b c d :: real
  shows "(a*c + b*d)^2 ≤ (a^2 + b^2) * (c^2 + d^2)"
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


text ‹pokazujem da su preostali sabirci manji od 2›
lemma pom1:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a ≥ b" "b ≥ c" "a + b > c" "b + c > a" "a + c > b"
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
  assumes "a > 0" "b > 0" "c > 0" "a ≥ b" "b ≥ c" "a + b > c" "b + c > a" "a + c > b"
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
  assumes "a > 0" "b > 0" "c > 0" "a ≥ b" "b ≥ c" "a + b > c" "b + c > a" "a + c > b"
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
  assumes "a > 0" "b > 0" "c > 0" "a ≥ b" "b ≥ c" "a + b > c" "b + c > a" "a + c > b"
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
    using pom1 pom3 using calculation by presburger
qed


lemma pom5:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a ≥ b" "b ≥ c" "a + b > c" "b + c > a" "a + c > b"
    "sqrt a + sqrt b > sqrt c" "sqrt a + sqrt c > sqrt b"
  shows "(sqrt(c + a - b) / (sqrt c + sqrt a - sqrt b) + sqrt(c + b - a) / (sqrt c + sqrt b - sqrt a))^2 ≤ 2"
  sorry
(*proof -
  have "sqrt(c + a - b) / (sqrt c + sqrt a - sqrt b) + sqrt(c + b - a) / (sqrt c + sqrt b - sqrt a)
  = sqrt(c + a - b) / sqrt(sqrt c + sqrt a - sqrt b) * (1 / sqrt(sqrt c + sqrt a - sqrt b)) + sqrt(c + b - a) / (sqrt c + sqrt b - sqrt a)"
    using assms(4) assms(5) assms(7) pom1 by force
  also have "... = sqrt(c + a - b) / sqrt(sqrt c + sqrt a - sqrt b) * (1 / sqrt(sqrt c + sqrt a - sqrt b))
  + sqrt(c + b - a) / sqrt(sqrt c + sqrt b - sqrt a) * (1 / sqrt(sqrt c + sqrt b - sqrt a))"
    by (smt (verit) add.commute assms(4) assms(5) assms(7) pom3)
  also have "... ≤ ((sqrt(c + a - b) / sqrt(sqrt c + sqrt a - sqrt b))^2 + sqrt(c + b - a) / sqrt(sqrt c + sqrt b - sqrt a))^2 
    * ((1 / sqrt(sqrt c + sqrt a - sqrt b))^2 + (1 / (sqrt(sqrt c + sqrt b - sqrt a)))^2)"
    oops
*)

text ‹dokaz konacne nejednakosti›

lemma final_theorem:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a ≥ b" "b ≥ c" "a + b > c" "b + c > a" "a + c > b" 
    "sqrt a + sqrt b > sqrt c" "sqrt a + sqrt c > sqrt b" "sqrt b + sqrt c > sqrt a"(* posto a, b, c stranice trougla *)
  shows "(sqrt(b + c - a)) / (sqrt (b) + sqrt (c) - sqrt (a)) + 
sqrt((c + a - b)) / (sqrt (c) + sqrt (a) - sqrt (b)) +
(sqrt(a + b - c)) / (sqrt (a) + sqrt (b) - sqrt (c)) ≤ 3"
proof -
  have "sqrt (a + b - c) / (sqrt (a) + sqrt (b) - sqrt (c)) ≤ 1"
    using assms(4) assms(5) assms(7) manje_od_jedan by fastforce
  have "(sqrt(c + a - b) / (sqrt c + sqrt a - sqrt b) + sqrt(c + b - a) / (sqrt c + sqrt b - sqrt a))^2 ≤ 2"
    by (simp add: assms(1) assms(10) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) pom5)
  from this show ?thesis
    by (smt (verit) ‹sqrt (a + b - c) / (sqrt a + sqrt b - sqrt c) ≤ 1› real_le_rsqrt sqrt2_less_2)
qed


end
