text\<open>
  https://imomath.com/srb/zadaci/2017_smo_resenja.pdf 
  Prvi dan, zadatak 1:
  Neka su a, b i c pozitivni realni brojevi za koje vazi a + b + c = 1.
  Treba dokazati navedenu teoremu.
\<close>

theory mi16072_Aleksandra_Niksic
  imports HOL.Real Complex_Main
begin

lemma kvadrat_trinoma:
  fixes a b c :: real
  shows "(a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2*a*b + 2*c*b + 2*a*c"
  by (simp add: field_simps power2_eq_square)

lemma pomocna_lema:
  fixes a b c :: real
  assumes "a + b + c = 1" "a > 0" "b > 0"  "c > 0"
  shows "1 - (a^2 + b^2 + c^2) = 2 * (a*b + b*c + c*a)"
proof-
  have "(a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2*a*b + 2*c*b + 2*a*c"
    using kvadrat_trinoma 
    by auto
  then have "1 = a^2 + b^2 + c^2 + 2*a*b + 2*c*b + 2*a*c"
    using assms 
    by auto
  then have "1 - (a^2 + b^2 + c^2) = 2*a*b + 2*c*b + 2*a*c"
    by auto
  then show ?thesis
    by auto
qed

lemma arit_geo_nejednakost:
  assumes "a > 0" "b > 0"
  shows "sqrt(a * b) \<le> (a + b) / 2"
  using assms
  using arith_geo_mean_sqrt
  by auto

(*naredne dve leme su pomocne za lemu "L_manje_jednako_D" iz dokaza *)
lemma pom_LD_2: 
  fixes a b c :: real
  assumes "a + b + c = 1" "a > 0" "b > 0" "c > 0"
  shows "2*(a + b + c + 1)*(a*b + b*c + c*a) = 
         2*a^2*b + 2*b^2*c + 2*c^2*a + 2*a*b^2 + 2*a*b*c + 2*a*b + 2*a^2*c + 2*a*b*c + 2*a*c + 2*a*b*c + 2*b*c^2 + 2*b*c"
proof-
  have "2*(a + b + c + 1)*(a*b + b*c + c*a) = (2*a + 2*b + 2*c + 2)*(a*b + b*c + c*a)"
    by auto
  also have "... = 2*a*(a*b + b*c + c*a) + 2*b*(a*b + b*c + c*a) + 2*c*(a*b + b*c + c*a) + 2*(a*b + b*c + c*a)"
    proof-
      have "2*a*(a*b + (b*c + a*c)) + 2*b*(a*b + (b*c + a*c)) + 2*c*(a*b + (b*c + a*c)) + 2*(a*b + (b*c + a*c)) = 
            2*((a + b + c + 1)*(a*b + (b*c + a*c)))"
        by (simp add: semiring_normalization_rules(8))
      then show ?thesis
        by (simp add: linordered_field_class.sign_simps(35))
    qed
    also have "... = 2*a*a*b + 2*a*b*c + 2*a*c*a + 2*b*a*b + 2*b*b*c + 2*b*c*a + 2*c*a*b + 2*c*b*c + 2*c*c*a + 2*a*b + 2*b*c + 2*c*a"
      by (simp add: distrib_left)
    also have "... = 2*a^2*b + 2*a*b*c + 2*a^2*c + 2*b^2*a + 2*b^2*c + 2*a*b*c + 2*a*b*c + 2*c^2*b + 2*c^2*a + 2*a*b + 2*b*c + 2*c*a"
      by (simp add: mult.commute power2_eq_square)
    finally show ?thesis
      by auto
qed

thm  semiring_normalization_rules(29)

lemma pom_LD_1:
  fixes a b c :: real
  assumes "a + b + c = 1" "a > 0" "b > 0" "c > 0"
  shows "2*a^2*b + 2*b^2*c + 2*c^2*a + a*b*2*b + a*b*2*c + a*b*2 + a*c*2*a + a*c*2*b + a*c*2 + b*c*2*a + b*c*2*c + b*c*2 = 4*(a*b + a*c + b*c)"
proof-
  have "2*a^2*b + 2*b^2*c + 2*c^2*a + a*b*2*b + a*b*2*c + a*b*2 + a*c*2*a + a*c*2*b + a*c*2 + b*c*2*a + b*c*2*c + b*c*2 = 
        2*a^2*b + 2*b^2*c + 2*c^2*a + 2*a*b^2 + 2*a*b*c + 2*a*b + 2*a^2*c + 2*a*b*c + 2*a*c + 2*a*b*c + 2*b*c^2 + 2*b*c"
    using semiring_normalization_rules(29)
    by (simp add: power2_eq_square)
  also have "... = 2*(a + b + c + 1)*(a*b + b*c + c*a)"
    using pom_LD_2 assms
    by presburger
  also have "... = 2*2*(a*b + b*c + c*a)"
    using assms(1) by simp
  finally show ?thesis by simp
qed
(* lema "L_manje_jednako_D" iz dokaza *)
lemma L_manje_jednako_D:
  fixes a b c :: real
  assumes "a + b + c = 1" "a > 0" "b > 0" "c > 0"
  shows "2*a^2*b + 2*b^2*c + 2*c^2*a +  2*a*b*sqrt((2*b + 1)*(2*c + 1)) + 2*a*c*sqrt((2*a + 1)*(2*b + 1)) + 2*b*c*sqrt((2*a + 1)*(2*c + 1)) 
            \<le> 4*(a*b + a*c + b*c)"
proof-
  have "2*a^2*b + 2*b^2*c + 2*c^2*a + 2*a*b*sqrt((2*b + 1)*(2*c + 1)) + 2*a*c*sqrt((2*a + 1)*(2*b + 1)) + 2*b*c*sqrt((2*a + 1)*(2*c + 1))
            \<le> 2*a^2*b + 2*b^2*c + 2*c^2*a + 2*a*b*(2*b + 2*c + 2)/2 + 2*a*c*sqrt((2*a + 1)*(2*b + 1)) + 2*b*c*sqrt((2*a + 1)*(2*c + 1))"
    using arit_geo_nejednakost [of "2*b + 1" "2*c + 1"] assms
    by simp
  also have "... \<le> 2*a^2*b + 2*b^2*c + 2*c^2*a + 2*a*b*(2*b + 2*c + 2)/2 + 2*a*c*(2*a + 2*b + 2)/2 + 2*b*c*sqrt((2*a + 1)*(2*c + 1))"
    using arit_geo_nejednakost [of "2*a + 1" "2*b + 1"] assms
    by simp
  also have "... \<le> 2*a^2*b + 2*b^2*c + 2*c^2*a + 2*a*b*(2*b + 2*c + 2)/2 + 2*a*c*(2*a + 2*b + 2)/2 + 2*b*c*(2*a + 2*c + 2)/2"
    using arit_geo_nejednakost [of "2*a + 1" "2*c + 1"] assms
    by simp
  also have "... =  2*a^2*b + 2*b^2*c + 2*c^2*a + a*b*(2*b+2*c+2) + a*c*(2*a+2*b+2) + b*c*(2*a+2*c+2)"
    by simp
  also have "... = 2*a^2*b + 2*b^2*c + 2*c^2*a + a*b*2*b + a*b*2*c + a*b*2 + a*c*2*a + a*c*2*b + a*c*2 + b*c*2*a + b*c*2*c + b*c*2"
    by (simp add: distrib_left)
  also have "... = 4*(a*b + a*c + b*c)"
    using pom_LD_1 assms
    by simp
  finally show ?thesis .
qed

lemma kvadrat_trinoma_glavna:
  fixes a b c :: real
  assumes "a + b + c = 1" "a > 0" "b > 0" "c > 0"
  shows "(a*sqrt(2*b + 1) + b*sqrt(2*c + 1) + c*sqrt(2*a + 1)) ^ 2 = 
          2*a^2*b + 2*b^2*c + 2*c^2*a + a^2 + b^2 + c^2 
          + 2*a*b*sqrt((2*b + 1)*(2*c + 1)) + 2*a*c*sqrt((2*a + 1)*(2*b + 1)) + 2*b*c*sqrt((2*a + 1)*(2*c + 1))"  
proof-
  have "(a*sqrt(2*b + 1) + b*sqrt(2*c + 1) + c*sqrt(2*a + 1))^2 = 
        (a*sqrt(2*b + 1) + b*sqrt(2*c + 1) + c*sqrt(2*a + 1)) * (a*sqrt(2*b + 1) + b*sqrt(2*c + 1) + c*sqrt(2*a + 1)) "
    by (simp add: power2_eq_square)
  also have "... = (a*sqrt(2*b + 1)) * (a*sqrt(2*b + 1) + b*sqrt(2*c + 1) + c*sqrt(2*a + 1)) 
                 + (b*sqrt(2*c + 1)) * (a*sqrt(2*b + 1) + b*sqrt(2*c + 1) + c*sqrt(2*a + 1))
                 + (c*sqrt(2*a + 1)) * (a*sqrt(2*b + 1) + b*sqrt(2*c + 1) + c*sqrt(2*a + 1))"
    by (simp add: comm_semiring_class.distrib)
  also have "... = (a*sqrt(2*b + 1) * a*sqrt(2*b + 1) + a*sqrt(2*b + 1)*b*sqrt(2*c + 1) + a*sqrt(2*b + 1)*c*sqrt(2*a + 1))
                 + (b*sqrt(2*c + 1) * a*sqrt(2*b + 1) + b*sqrt(2*c + 1)*b*sqrt(2*c + 1) + b*sqrt(2*c + 1)*c*sqrt(2*a + 1)) 
                 + (c*sqrt(2*a + 1) * a*sqrt(2*b + 1) + c*sqrt(2*a + 1)*b*sqrt(2*c + 1) + c*sqrt(2*a + 1)*c*sqrt(2*a + 1))"
    by (simp add: distrib_left mult.assoc power2_commute right_diff_distrib)
  also have "... = (a*a*(2*b + 1) + a*b*sqrt(2*b + 1)*sqrt(2*c + 1) + a*c*sqrt(2*b + 1)*sqrt(2*a + 1)) 
                 + (b*sqrt(2*c + 1)*a*sqrt(2*b + 1) + b*sqrt(2*c + 1)*b*sqrt(2*c + 1) + b*sqrt(2*c + 1)*c*sqrt(2*a + 1))  
                 + (c*sqrt(2*a + 1)*a*sqrt(2*b + 1) + c*sqrt(2*a + 1)*b*sqrt(2*c + 1) + c*sqrt(2*a + 1)*c*sqrt(2*a + 1))"
    using assms(3) sqrt_def 
    by auto
  also have "... = (a*a*(2*b + 1) + a*b*sqrt(2*b + 1)*sqrt(2*c + 1) + a*c*sqrt(2*b + 1)*sqrt(2*a + 1)) 
                 + (b*sqrt(2*c + 1)*a*sqrt(2*b + 1) + b*b*(2*c + 1) + b*sqrt(2*c + 1)*c*sqrt(2*a + 1))
                 + (c*sqrt(2*a + 1)*a*sqrt(2*b + 1) + c*sqrt(2*a+1)*b*sqrt(2*c + 1) + c*sqrt(2*a + 1)*c*sqrt(2*a + 1))"
    using assms(4) sqrt_def 
    by auto
  also have "... = a*a*(2*b + 1) + a*b*sqrt(2*b + 1)*sqrt(2*c + 1) + a*c*sqrt(2*b + 1)*sqrt(2*a + 1) 
                 + b*sqrt(2*c + 1)*a*sqrt(2*b + 1) + b*b*(2*c + 1) + b*sqrt(2*c + 1)*c*sqrt(2*a + 1)
                 + c*sqrt(2*a + 1)*a*sqrt(2*b + 1) + c*sqrt(2*a + 1)*b*sqrt(2*c + 1) + c*c*(2*a + 1)"
    using assms(2) sqrt_def
    by auto
  also have "... = a^2*(2*b) + a^2 + a*b*sqrt(2*b + 1)*sqrt(2*c + 1) + a*c*sqrt(2*b + 1)*sqrt(2*a + 1)
                 + b*sqrt(2*c + 1)*a*sqrt(2*b + 1) + b^2*(2*c) + b^2 + b*sqrt(2*c + 1)*c*sqrt(2*a + 1)  
                 + c*sqrt(2*a + 1)*a*sqrt(2*b + 1) + c*sqrt(2*a + 1)*b*sqrt(2*c + 1) + c^2*(2*a) + c^2"
    by (simp add: distrib_left semiring_normalization_rules(29))
  also have "... = 2*a^2*b + 2*b^2*c + 2*c^2*a + a^2 + b^2 + c^2  
                 + 2*a*b*sqrt((2*b + 1)*(2*c + 1)) + 2*a*c*sqrt((2*a + 1)*(2*b + 1)) + 2*b*c*sqrt((2*a + 1)*(2*c + 1))"
    using real_sqrt_mult
    by simp
  finally show ?thesis .
qed

lemma koren_pozitivan_glavna:
  fixes a b c :: real
  assumes "a + b + c = 1" "a > 0" "b > 0" "c > 0"
  shows "2 - (a^2 + b^2 + c^2) \<ge> 0"
proof-
  have "(a + b + c)^2 = 1"
    using assms(1)
    by auto
  then have "a^2 + b^2 + c^2 + 2*a*b + 2*b*c + 2*a*c = 1"
    using kvadrat_trinoma
    by (simp add: semiring_normalization_rules(16))
  then have "a^2 + b^2 + c^2 \<le> 1"
    by (smt assms mult_nonneg_nonneg)
  then show ?thesis 
    by auto
qed

(* naredne dve leme se koriste pri dokazu glavne teoreme *)
lemma eq_1:
  fixes a b c :: real
  assumes "a + b + c = 1" "a > 0" "b > 0"  "c > 0"
  shows "(a*sqrt(2*b + 1) + b*sqrt(2*c + 1) + c*sqrt(2*a + 1)) ^ 2 \<le> (sqrt(2 - (a^2 + b^2 + c^2))) ^ 2 \<longleftrightarrow> 
  2*a^2*b + 2*b^2*c + 2*c^2*a + a^2 + b^2 + c^2 + 2*a*b*sqrt((2*b + 1)*(2*c + 1)) + 2*a*c*sqrt((2*a + 1)*(2*b + 1)) + 2*b*c*sqrt((2*a + 1)*(2*c + 1))
              \<le> 2 - (a^2+b^2+c^2)"
proof-
  have "(a*sqrt(2*b + 1) + b*sqrt(2*c + 1) + c*sqrt(2*a + 1)) ^ 2 \<le> (sqrt(2 - (a^2 + b^2 + c^2))) ^ 2 \<longleftrightarrow> 
    2*a^2*b + 2*b^2*c + 2*c^2*a + a^2 + b^2 + c^2 + 2*a*b*sqrt((2*b + 1)*(2*c + 1)) + 2*a*c*sqrt((2*a + 1)*(2*b + 1)) + 2*b*c*sqrt((2*a + 1)*(2*c + 1))
              \<le> (sqrt(2 - (a^2 + b^2 + c^2))) ^ 2"
    using  kvadrat_trinoma_glavna assms 
    by simp
  also have "... \<longleftrightarrow> 2*a^2*b + 2*b^2*c + 2*c^2*a + a^2 + b^2 + c^2 
                     + 2*a*b*sqrt((2*b + 1)*(2*c + 1)) + 2*a*c*sqrt((2*a + 1)*(2*b + 1)) + 2*b*c*sqrt((2*a + 1)*(2*c + 1)) \<le> 2 - (a^2 + b^2 + c^2)"
    using koren_pozitivan_glavna assms 
    by auto
  finally show ?thesis .
qed

lemma eq_2:
  fixes a b c :: real
  assumes "a + b + c = 1" "a > 0" "b > 0" "c > 0"
  shows "2*a^2*b + 2*b^2*c + 2*c^2*a + a^2 + b^2 + c^2 + 
         2*a*b*sqrt((2*b + 1)*(2*c + 1)) + 2*a*c*sqrt((2*a + 1)*(2*b + 1)) + 2*b*c*sqrt((2*a + 1)*(2*c + 1)) \<le> 2 - (a^2 + b^2 + c^2) 
                  \<longleftrightarrow> 
         2*a^2*b + 2*b^2*c + 2*c^2*a + 
         2*a*b*sqrt((2*b + 1)*(2*c + 1)) + 2*a*c*sqrt((2*a + 1)*(2*b + 1)) + 2*b*c*sqrt((2*a + 1)*(2*c + 1)) \<le> 4*(a*b + a*c + b*c)"
  using pomocna_lema
  by (smt assms mult.commute)

theorem glavna_teorema:
 fixes a b c :: real
 assumes "a + b + c = 1" "a > 0" "b > 0"  "c > 0"
 shows "a*sqrt(2*b + 1) + b*sqrt(2*c + 1) + c*sqrt(2*a + 1) \<le> sqrt(2 - (a^2 + b^2 + c^2))" 
proof-
  have "a * sqrt(2*b + 1) + b * sqrt(2*c + 1) + c * sqrt(2*a + 1) \<le>  sqrt(2 - (a^2 + b^2 + c^2)) \<longleftrightarrow> 
       (a * sqrt(2*b + 1) + b * sqrt(2*c + 1) + c * sqrt(2*a + 1)) ^ 2 \<le> (sqrt(2 - (a^2 + b^2 + c^2))) ^ 2"
    using koren_pozitivan_glavna
    by (smt assms mult_nonneg_nonneg power2_le_imp_le real_sqrt_ge_0_iff)
  also have "... \<longleftrightarrow> 2*a^2*b + 2*b^2*c + 2*c^2*a + a^2 + b^2 + c^2 + 
                     2*a*b*sqrt((2*b + 1)*(2*c + 1)) + 2*a*c*sqrt((2*a + 1)*(2*b + 1)) + 2*b*c*sqrt((2*a + 1)*(2*c + 1))
                          \<le> 2 - (a^2 + b^2 + c^2)"
    using eq_1 assms 
    by simp
  also have "... \<longleftrightarrow> 2*a^2*b + 2*b^2*c + 2*c^2*a + 2*a*b*sqrt((2*b + 1)*(2*c + 1)) + 2*a*c*sqrt((2*a + 1)*(2*b + 1)) + 2*b*c*sqrt((2*a + 1)*(2*c + 1)) 
                          \<le> 4*(a*b + a*c + b*c)"
    using eq_2 assms 
    by simp
  finally show ?thesis
    using L_manje_jednako_D assms 
    by simp
qed

end