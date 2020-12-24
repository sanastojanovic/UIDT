(*Zadatak: https://imomath.com/srb/zadaci/RS_2017_republicko_resenja.pdf
  Prvi razred, zadatak 4

  Neka su a, b, c pozitivni brojevi takvi da je a*b*c \<le> 1. 
  Dokazati da je 1/a + 1/b + 1/c \<ge> 1 + 6/(a + b + c)

  Resenje: 
  Zapisujemo nejednakost u obliku: (1/a + 1/b + 1/c)*(a + b + c) \<ge> a + b + c + 6
  
  Na osnovu nejednakosti izmedju aritmeticke i geometrijske sredne:
  1/a + 1/b + 1/c \<ge> 3 / root 3 (a * b * c) \<ge> 3
  i  a + b + c \<ge> 3 * root 3 (a * b * c)
  
  Zbog toga je:
  1/3 * (1/a + 1/b + 1/c)*(a + b + c) \<ge> a + b + c
  i  2/3 * (1/a + 1/b + 1/c)*(a + b + c) \<ge> 2/3 * 3 / root 3(a * b * c)* 3 * root 3 (a * b * c) = 6

  Sabiranjem poslednje dve nejednakosti dobijamo:
  (1/a + 1/b + 1/c)*(a + b + c) \<ge> a + b + c + 6
*)


theory mi16138_Jelisaveta_Smiljanic_2
  imports HOL.Real Complex_Main
begin

lemma pom2: 
  fixes a b c :: real
  assumes "a * b * c \<le> 1" "a > 0" "b > 0"  "c > 0"
  shows "3 / root 3 (a * b * c) \<ge> 3"
  proof-
    have "root 3 (a * b * c) \<le> 1" 
      using assms
      by simp
    then have "1 / root 3 (a * b * c) \<ge> 1"
      using assms
      by simp
    then have "3 / root 3 (a * b * c) \<ge> 3"
      by linarith
    then show ?thesis
      .
  qed

lemma kvadrat_binoma:
  fixes x y :: real
  assumes "x > 0" "y > 0"
  shows "(x - y)^2 = x^2 - 2*x*y + y^2"
proof-
  have "(x - y)^2 = (x - y) * (x - y)"
    using power2_eq_square 
    by auto
  also have "... = (x * x - x * y - y * x + y * y)"
    by (simp add: left_diff_distrib' right_diff_distrib')
  also have "... = x^2 - 2*x*y + y^2"
    by (simp add: power2_eq_square)
  finally show ?thesis
    .
qed

lemma pom_ag_nej_1:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "(x + y + z) * ((x - y)^2 + (y - z)^2 + (z - x)^2) = 
        2 * (x powr 3 + y powr 3 + z powr 3 - 3 * x * y * z)"
proof-
  have "(x + y + z) * ((x - y)^2 + (y - z)^2 + (z - x)^2) = 
        (x + y + z) * (x^2 - 2*x*y + y^2 + y^2 - 2*y*z + z^2 + z^2 - 2*z*x + x^2)"
    by (simp add: assms kvadrat_binoma)
  also have "... = (x + y +z) * (2*x^2 + 2*y^2 + 2*z^2 - 2*x*y - 2*y*z - 2*z*x)"
    by simp
  also have "... = x * (2*x^2 + 2*y^2 + 2*z^2 - 2*x*y - 2*y*z - 2*z*x) + 
                   y * (2*x^2 + 2*y^2 + 2*z^2 - 2*x*y - 2*y*z - 2*z*x) + 
                   z * (2*x^2 + 2*y^2 + 2*z^2 - 2*x*y - 2*y*z - 2*z*x)"
    by (simp add: semiring_normalization_rules(1))
  also have "... = x*2*x^2 + x*2*y^2 + x*2*z^2 - x*2*x*y - x*2*y*z - x*2*z*x +
                   y*2*x^2 + y*2*y^2 + y*2*z^2 - y*2*x*y - y*2*y*z - y*2*z*x + 
                   z*2*x^2 + z*2*y^2 + z*2*z^2 - z*2*x*y - z*2*y*z - z*2*z*x"
    by (simp add: distrib_left mult.assoc power2_commute right_diff_distrib)
  also have "... = 2 * (x powr 3) + 2 * x*y^2 + 2 * x*z^2 - 2 * x^2*y - 2 * x*y*z - 2 * x^2*z +
                   2 * x^2*y + 2 * (y powr 3) + 2 * y*z^2 - 2 * x*y^2 - 2 * y^2*z - 2 * x*y*z + 
                   2 * x^2*z + 2 * y^2*z + 2 * (z powr 3) - 2 * x*y*z - 2 * y*z^2 - 2 * x*z^2"
    by (simp add: assms power2_eq_square power3_eq_cube)
  also have "... = 2 * (x powr 3 + y powr 3 + z powr 3 - x*y*z - x*y*z - x*y*z)"
    by auto
  finally show ?thesis
    by auto   
qed

lemma pom_ag_nej_2:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "1/2 * (x + y + z) * ((x - y)^2 + (y - z)^2 + (z - x)^2) = 
        x powr 3 + y powr 3 + z powr 3 - 3 * x * y * z"
proof-
  have "1/2 * ( (x + y + z) * ( (x - y)^2 + (y - z)^2 + (z - x)^2)) = 
        1/2 * (2 * (x powr 3 + y powr 3 + z powr 3 - 3 * x * y * z))"
    by (simp add: assms pom_ag_nej_1)
  also have "... = (x powr 3 + y powr 3 + z powr 3 - 3 * x * y * z)"
    by simp
  finally show ?thesis
    by auto
qed

lemma ag_razlika:
  fixes x y z a b c :: real
  assumes "x > 0" "y > 0" "z > 0" "a = root 3 x" "b = root 3 y" "c = root 3 z"
          "a > 0" "b > 0" "c > 0"
  shows "(x + y + z) / 3 - root 3 (x * y * z)  \<ge> 0" 
proof-
  have "(x + y + z) / 3 - root 3 (x * y * z) = (a powr 3 + b powr 3 + c powr 3) / 3 - (a * b * c)"
    using assms
   by (simp add: real_root_mult)
  also have "... = 1/3 * (a powr 3 + b powr 3 + c powr 3 - 3 * a * b * c)"
    by auto
  also have "... = 1/6 * (a + b + c) * ((a - b)^2 + (b - c)^2 + (c - a)^2)"
    using pom_ag_nej_2 assms
    by simp    
  also have "... \<ge> 0"
    using assms
    by auto
  finally show ?thesis
    .
qed

(*Nejednakost izmedju aritmeticke i geometrijske sredne*)
lemma ag_nej_3:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0" 
  shows "root 3 (x * y * z) \<le> (x + y + z) / 3 "
  using assms ag_razlika
  by simp

lemma deljenje_c:
  fixes c :: real
  assumes "c > 0"
  shows "1 / c > 0"
  using assms
  by simp

lemma deljenje_b:
  fixes b :: real
  assumes "b > 0" 
  shows "1 / b > 0"
  using assms
  by simp

lemma deljenje_a:
  fixes a :: real
  assumes "a > 0"
  shows "1 / a > 0"
  using assms
  by simp

(*Prmenjujemo GA nejednakost na 1/a, 1/b i 1/c umesto a, b, c*)
lemma pom1:
  fixes a b c :: real
  assumes "a * b * c \<le> 1" "a > 0" "b > 0"  "c > 0"
  shows "1/a + 1/b + 1/c \<ge> 3 / root 3 (a * b * c)"
proof-
  have "root 3 (1/a * 1/b * 1/c) \<le> (1/a + 1/b + 1/c) / 3"
    using assms ag_nej_3 deljenje_a deljenje_b deljenje_c
    by (metis (no_types, hide_lams) add.commute divide_inverse mult.left_neutral mult.right_neutral times_divide_eq_right)
  then have "root 3 1 /root 3 (a * b * c) \<le> (1/a + 1/b + 1/c) / 3"
    using assms ag_nej_3
    by (simp add: real_root_divide)
  then have "1 / root 3 (a * b * c) \<le> (1/a + 1/b + 1/c) / 3"
    by (simp add: real_root_mult)
  then show "3 / root 3 (a * b * c) \<le> (1/a + 1/b + 1/c)"
    by simp
qed

lemma leva_strana: 
  fixes a b c :: real
  assumes "a * b * c \<le> 1" "a > 0" "b > 0"  "c > 0"
  shows "1/3 * (1/a + 1/b + 1/c) * (a + b + c) \<ge> a + b + c"
proof-
  have "1/a + 1/b + 1/c \<ge> 3 / root 3 (a * b * c)"
    using pom1 assms
    by blast
  also have "... \<ge> 3"
    using pom2 assms calculation 
    by force
  then have "1/a + 1/b + 1/c \<ge> 3"
    by blast
  then have "1/3 * (1/a + 1/b + 1/c) \<ge> 1"
    by simp
  then have "1/3 * (1/a + 1/b + 1/c) * (a + b + c) \<ge> a + b + c"
    by (smt assms le_divide_eq_1_pos nonzero_mult_div_cancel_right)
  then show ?thesis
    .
qed

lemma d_pom:
  fixes a b c :: real
  assumes "a * b * c \<le> 1" "a > 0" "b > 0"  "c > 0"
  shows "(a + b + c) \<ge> 3 * root 3 (a * b * c)"
  proof-
    have "(a + b + c)/3 \<ge> root 3 (a * b * c)"
      using  ag_nej_3 [of "a" "b" "c"] assms
      by blast
    then have "a + b + c \<ge> 3 * root 3 (a * b * c)"
      by auto
    then show ?thesis
      .
  qed

lemma desna_strana: 
  fixes a b c :: real
  assumes "a * b * c \<le> 1" "a > 0" "b > 0"  "c > 0"
  shows "2/3 * (1/a + 1/b + 1/c) * (a + b + c) \<ge> 6"
  proof-
    have "(1/a + 1/b + 1/c) * (a + b + c) \<ge> 
          (1/a + 1/b + 1/c) * (3 * root 3 (a * b * c))"
      using d_pom assms pom1 pom2 
      by fastforce
    then have "... \<ge> (3 / root 3 (a * b * c)) * (3 * root 3 (a * b * c))"
      by (smt assms mult_pos_pos pom1 real_mult_le_cancel_iff1 real_root_gt_0_iff zero_less_numeral)
    then have "... \<ge> 3 / root 3 (a * b * c) * 3 * root 3 (a * b * c)"
      using assms
      by linarith
    then have "(1/a + 1/b + 1/c) * (a + b + c) \<ge> 3 / root 3 (a * b * c) * 3 * root 3 (a * b * c)"
      by blast
    then have "(1/a + 1/b + 1/c) * (a + b + c) \<ge> 9"
      using assms
      by auto
    then show "2/3 * (1/a + 1/b + 1/c) * (a + b + c) \<ge> 6"
      by linarith
  qed

lemma glavna: 
  fixes a b c :: real
  assumes "a * b * c \<le> 1" "a > 0" "b > 0"  "c > 0"
  shows "(1/a + 1/b + 1/c) * (a + b + c) \<ge> a + b + c + 6"
  proof-
    have "(1/a + 1/b + 1/c) * (a + b + c) 
        = (1/3 + 2/3) * ((1/a + 1/b + 1/c) * (a + b + c))"
      by simp
    also have "... = 1/3 * ((1/a + 1/b + 1/c) * (a + b + c)) + 2/3 * ((1/a + 1/b + 1/c) * (a + b + c))"
      using distrib_right
      by blast
    also have "... = 1/3 * (1/a + 1/b + 1/c) * (a + b + c) + 2/3 * (1/a + 1/b + 1/c) * (a + b + c)"
      by linarith
    also have "... \<ge> (a + b + c) + 6"  
      using leva_strana assms desna_strana
      by smt
    finally show ?thesis
      by blast
  qed

theorem
  fixes a b c :: real
  assumes "a * b * c \<le> 1" "a > 0" "b > 0"  "c > 0"
  shows "1/a + 1/b + 1/c \<ge> 1 + 6/(a + b + c)" 
  proof-
    have "1/a + 1/b + 1/c \<ge> 1 + 6/(a + b + c) 
        \<longleftrightarrow> (1/a + 1/b + 1/c) * (a + b + c) \<ge> (1 + 6/(a + b + c)) * (a + b + c)"
      using assms
      by auto
    also have "... \<longleftrightarrow> (1/a + 1/b + 1/c) * (a + b + c) \<ge> (a + b + c) + 6 * (a + b + c) / (a + b + c)"
      by (simp add: distrib_right)
    also have "... \<longleftrightarrow> (1/a + 1/b + 1/c) * (a + b + c) \<ge> (a + b + c) + 6 * ((a + b + c) / (a + b + c))"
      by linarith
    also have "... \<longleftrightarrow> (1/a + 1/b + 1/c) * (a + b + c) \<ge> a + b + c + 6"
      using assms 
      by auto
    finally show ?thesis
      using assms glavna 
      by blast
  qed
end
