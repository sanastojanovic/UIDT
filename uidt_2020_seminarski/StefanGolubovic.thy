theory StefanGolubovic
  imports Main Complex_Main
begin
 
lemma postavka_zadatka:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a * b * c = 1"  
  shows "(a - 1 + 1/b) * (b - 1 + 1/c) * (c - 1 + 1/a) \<le> 1"
  using assms
  sorry

fun je_resenje :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "je_resenje a b c = (a * b * c = 1 \<and> (a - 1 + 1/b) * (b - 1 + 1/c) * (c - 1 + 1/a) \<le> 1)"

value "je_resenje 1 1 1"

lemma smena_1:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a * b * c = 1"
  shows "\<exists> x y z :: real. x > 0 \<and> y > 0 \<and> z > 0 \<and> je_resenje a b c \<longleftrightarrow> je_resenje (x/y) (y/z) (z/x)"
  using assms
  by auto 

lemma nejednakost_nakon_smene:
  fixes a b c x y z :: real
  assumes "a > 0" "b > 0" "c > 0" "a * b * c = 1" "a = x/y" "b = y/z" "c = z/x" "x > 0" "y > 0" "z > 0" "(a - 1 + 1/b) * (b - 1 + 1/c) * (c - 1 + 1/a) \<le> 1"
  shows "(x - y + z) / y * (y - z + x) / z * (z - x + y) / x \<le> 1"
  proof-
    have "(x/y - 1 + z/y) * (y/z - 1 + x/z ) * (z/x - 1 + y/x) \<le> 1"
      using assms
      by auto
    then have "(x/y - y/y + z/y) * (y/z - z/z + x/z) * (z/x- x/x + y/x) \<le> 1"
      using assms
      by auto
    from this have "(x - y + z) / y * ( y - z + x) / z * (z - x + y) / x\<le> 1"
      using assms
      by (metis add_divide_distrib diff_divide_distrib times_divide_eq_right)
    then show ?thesis
      by simp
qed

lemma najvise_1_negativan:
  fixes x y z p q r :: real
  assumes "x > 0" "y > 0" "z > 0"
  assumes "p = z - x + y" "q = x - y + z" "r = y - z + x"
  shows "(p \<ge> 0 \<and> q \<ge> 0 \<and> r \<ge> 0) \<or> 
        (p < 0 \<and> q \<ge> 0 \<and> r \<ge> 0) \<or> 
        (p \<ge> 0 \<and> q < 0 \<and> r \<ge> 0) \<or>
        (p \<ge> 0 \<and> q \<ge> 0 \<and> r < 0)"
  using assms
  by smt

lemma pomocna_1:
  fixes a b c x y z :: real
  assumes "a \<ge> 0" "b \<ge> 0" "c \<ge> 0" 
  assumes "2 * a \<le> x" "2 * b \<le> y" "2 * c \<le> z" "x \<ge> 0" "y \<ge> 0" "z \<ge> 0"
  shows "8 * a * b * c \<le> x * y * z"
  using assms
  apply (simp add: algebra_simps)
  apply (simp add: Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(18))
  proof -
  have f2: "\<forall>r. (r::real) * (1 + 1) = r + r"
    using assms(6)
    by simp
  have "0 \<le> c + c"
    using assms(3) by linarith
  then have "(a + a) * ((b + b) * (c + c)) \<le> x * (y * z)"
    using assms f2 by (metis (no_types)Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(7)  add_increasing mult_mono one_add_one zero_le_mult_iff)
  then show "a * b * c * 8 \<le> x * y * z"
    by (simp add: mult.commute mult.left_commute)
qed

text
\<open>
Po lemi najvise_jedan_negativan se vidi da je najvise jedan od p, q, r negativan, sto dalje
implicira da se konacna nejednakost dokazuje u 2 slucaja:
  1. jedan od njih je negativan, bez gubljenja na opstosti neka to bude p, q i r nenegativni
  2. svi su nenegativni

Sledece dve leme, nejednakost_svi_nenegativni i nejednakosti_jedan_negativan, dokazuju 
pomenute slucajeve, redom.
\<close>

lemma nejednakost_jedan_negativan:
  fixes p q r x y z :: real
  assumes "q = x - y + z" "p = z - y + x" "r = y - z + x"
  assumes "p < 0" "q \<ge> 0" "r \<ge> 0"
  shows "8 * p * q * r \<le> (p + q) * (q + r) * (r + p)"
  using assms
  by linarith

lemma nejednakost_svi_nenegativni:
  fixes p q r :: real
  assumes "p \<ge> 0" "q \<ge> 0" "r \<ge> 0"
  shows "8 * p * q * r \<le> (p+q) * (q+r) * (r+p)"
  using assms
proof-
  have "2 * sqrt(p * q) \<ge> 0"
    by (simp add: assms(1) assms(2))
  have "2 * sqrt(q * r) \<ge> 0"
    by (simp add: assms(2) assms(3))
  have "2 * sqrt(r * p) \<ge> 0"
    by (simp add: assms(3) assms(1))
  have "2 * sqrt(p * q) \<le> p + q"
    using arith_geo_mean_sqrt assms(1) assms(2) by fastforce
  then have "2 * sqrt(q * r) \<le> q + r"
    using arith_geo_mean_sqrt assms(2) assms(3) by fastforce
  then have "2 * sqrt(r * p) \<le> r + p"
    using arith_geo_mean_sqrt assms(1) assms(3) by force
  then have "2 * sqrt(p * q) * 2 * sqrt(q * r) * 2 * sqrt(r * p) = 8 * p * q * r"
  proof-
    have "2 * sqrt(p * q) * 2 * sqrt(q * r) * 2 * sqrt(r * p) = 8 * sqrt(p * q * q * r * r * p)"
      by (simp add: real_sqrt_mult)
    also have "... = 8 * sqrt(p ^ 2 * q ^ 2 * r ^ 2)"
      by (simp add: power2_eq_square)
    finally show ?thesis
      by (simp add: assms(1) assms(2) assms(3) real_sqrt_mult)
  qed
  then have "2 * sqrt(p * q) * 2 * sqrt(q * r) * 2 * sqrt(r * p) \<le> (p + q) * (q + r) * (r + p)"
    using `2 * sqrt(p * q) \<ge> 0` `2 * sqrt(q * r) \<ge> 0` `2 * sqrt(r * p) \<ge> 0` 
          `2 * sqrt(p * q) \<le> p + q` `2 * sqrt(q * r) \<le> q + r` `2 * sqrt(r * p) \<le> r + p`
          pomocna_1[of "sqrt(p * q)" "sqrt(q * r)" "sqrt(r * p)" "p + q" "q + r" "r + p" ] assms
    by simp
  then show "8 * p * q * r \<le> (p + q) * (q + r) * (r + p)"
    using `2 * sqrt(p * q) * 2 * sqrt(q * r) * 2 * sqrt(r * p) = 8 * p * q * r`
    by simp
qed

end