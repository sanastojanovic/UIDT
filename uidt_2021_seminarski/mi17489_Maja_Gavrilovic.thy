theory mi17489_Maja_Gavrilovic

imports Main Complex_Main

begin

text\<open> 
IMO 2000, zadatak 2: https://imomath.com/srb/zadaci/2000_mmo.pdf

Neka su a, b i c pozitivni realni brojevi takvi da je a*b*c = 1.
Dokazati da je (a - 1 + 1/b) * (b - 1 + 1/c) * (c - 1 + 1/a) \<le> 1

 \<close>

lemma IMO_2000_zadatak2:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a * b * c = 1"  
  shows "(a - 1 + 1/b) * (b - 1 + 1/c) * (c - 1 + 1/a) \<le> 1"
  using assms
  sorry


lemma nakon_prve_smene:
  fixes a b c x y z :: real
  assumes "a > 0" "b > 0" "c > 0" "a * b * c = 1" "a = x/y" "b = y/z" "c = z/x" "x > 0" "y > 0" "z > 0" "(a - 1 + 1/b) * (b - 1 + 1/c) * (c - 1 + 1/a) \<le> 1"
  shows "(x - y + z) * (y - z + x) * (z - x + y) \<le> x*y*z"
proof-
 have "(x/y - 1 + z/y) * (y/z - 1 + x/z) * (z/x - 1 + y/x) \<le> 1"
   using assms
   by auto
  then have "(x/y - y/y + z/y) * (y/z - z/z + x/z) * (z/x - x/x + y/x) \<le> 1"
    by auto
  then have "(x - y + z)/y * (y - z + x)/z * (z - x + y)/x \<le> 1"
    by (metis (mono_tags, hide_lams)  add.commute add_diff_eq diff_diff_eq2 diff_divide_distrib times_divide_eq_right)
  then have "(x - y + z) * (y - z + x) * (z - x + y) / (x*y*z) \<le> 1"
    by (metis mult.commute times_divide_eq_right times_divide_times_eq)
  then have  "(x - y + z) * (y - z + x) * (z - x + y) \<le> x*y*z"
    by (simp add: assms(8) assms(9) assms(10))
  then show ?thesis
    .
qed



lemma nakon_druge_smene:
  fixes p q r x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
    "(x - y + z) * (y - z + x) * (z - x + y) \<le> x*y*z"
    "p = z - x + y" " r = y - z + x" "q = x - y + z" 
  shows "8 * p * q * r \<le> (p+q) * (q+r) * (r+p)"
  using assms
proof-
  have "q * r * p \<le> x * y *z"
    by (simp add: assms)
  then have "p * q * r \<le> x * y * z"
    by (simp add: mult.commute mult.left_commute)
  then have "8 * p * q * r \<le> 8 * x * y * z"
    by auto
  also have "... = 2 * x * 2 * y * 2 * z"
    by auto
  also have "... = (q+r) * (r+p) * (p+q)"
    by (simp add: assms)
  also have "... = (p+q) * (q+r) * (r+p)"
    by(simp add: mult.commute)
  finally show ?thesis
    by simp
qed


lemma najvise_jedan_negativan:
  fixes x y z p q r :: real
  assumes "x > 0" "y > 0" "z > 0"
  assumes "p = z - x + y" "q = x - y + z" "r = y - z + x"
  shows "(p < 0 \<and> q \<ge> 0 \<and> r \<ge> 0) \<or> 
        (p \<ge> 0 \<and> q < 0 \<and> r \<ge> 0) \<or>
        (p \<ge> 0 \<and> q \<ge> 0 \<and> r < 0) \<or> (p \<ge> 0 \<and> q \<ge> 0 \<and> r \<ge> 0)"
  using assms
  by auto
 
(* Medju brojevima p, q i r najvise jedan je negativan. Ako je npr p < 0 onda je leva strana negativna a desna pozitivna*)

lemma jedan_negativan_resenje:
  fixes p q r x y z :: real
  assumes "x > 0" "y > 0" "z > 0" "p < 0" "q \<ge> 0" "r \<ge> 0"
  assumes "p = z - x + y" "q = x - y + z" "r = y - z + x" 
  shows "(-x + y + z) * (x - y + z) * (x + y - z) < x * y * z"
  using assms
proof-
  have "(-x + y + z) * (x - y + z) * (x + y - z) = p * q * r"
    using assms
    by (smt (verit, ccfv_threshold) diff_add_cancel uminus_add_conv_diff)
  also  have "... \<le> 0"
    using assms
    by (metis less_le_not_le not_less zero_less_mult_iff)
  also have "... < x * y * z"
    by(simp add: assms)
  finally show ?thesis
    by auto
qed

lemma negativno_p:
  fixes p q r x y z :: real
  assumes "q = x - y + z" "p = z - y + x" "r = y - z + x"
  assumes "p < 0" "q \<ge> 0" "r \<ge> 0" "x > 0" "y > 0" "z > 0"
  shows "8 * p * q * r \<le> (p + q) * (q + r) * (r + p)"
  using assms
  by auto

lemma pomocna:
  fixes p q r :: real
  assumes "p \<ge> 0" "q \<ge> 0" "r \<ge> 0"
  shows "2 * sqrt(p * q) * 2 * sqrt(q * r) * 2 * sqrt(r * p) = 8 * p * q * r"
  proof-
    have "2 * sqrt(p * q) * 2 * sqrt(q * r) * 2 * sqrt(r * p) = 8 * sqrt(p * q * q * r * r * p)"
      by (simp add: real_sqrt_mult)
    also have "... = 8 * sqrt(p ^ 2 * q ^ 2 * r ^ 2)"
      by (simp add: power2_eq_square)
    also have "... = 8 * p * q * r"
      by (simp add: assms(1) assms(2) assms(3) real_sqrt_mult)
    finally show ?thesis
      by simp
  qed

lemma svi_nenegativni_resenje:
  fixes p q r :: real
  assumes "p \<ge> 0" "q \<ge> 0" "r \<ge> 0"
  shows "8 * p * q * r \<le> (p+q) * (q+r) * (r+p)"
  using assms
proof-
  have f1:"2 * sqrt(p * q) \<le> p + q"
   using arith_geo_mean_sqrt assms(1) assms(2)
   by force
  have f2: "2 * sqrt(q * r) \<le> q + r"
    using arith_geo_mean_sqrt assms(2) assms(3)
    by force
  have f3: "2 * sqrt(r * p) \<le> r + p"
    using arith_geo_mean_sqrt assms(1) assms(3)
    by force
  have "(2 * sqrt(p * q)) * (2 * sqrt(q * r)) * (2 * sqrt(r * p)) \<le> (p + q) * (q + r) * (r + p)"
    using f1 f2 f3 
    by (metis add_increasing assms(1) assms(2) assms(3) mult_mono real_sqrt_ge_zero zero_le_mult_iff zero_le_numeral) 
  then show "8 * p * q * r \<le> (p + q) * (q + r) * (r + p)"
    using assms pomocna
    by simp
qed

fun resenje :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "resenje a b c = (((a - 1 + 1/b) * (b - 1 + 1/c) * (c - 1 + 1/a) \<le> 1) \<and> a * b * c = 1)"

lemma resenje_nakon_smene:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a * b * c = 1"
  shows "\<exists> x y z :: real. x > 0 \<and> y > 0 \<and> z > 0 \<and> resenje a b c \<longleftrightarrow> resenje (x/y) (y/z) (z/x)"
  using assms
  by auto 

 
end