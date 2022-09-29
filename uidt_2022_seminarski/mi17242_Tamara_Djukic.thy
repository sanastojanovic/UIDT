theory mi17242_Tamara_Djukic
  imports Main Complex_Main
begin

text\<open>
Link: https://imomath.com/srb/zadaci/RS_2016_republicko_resenja.pdf
Problem: Prvi razred,  zadatak 2.
Neka su a, b, c pozitivni brojevi takvi da je ab + bc + ca = 1.
Dokazati da je 
  sqrt (a + 1/a) + sqrt (b + 1/b) + sqrt (c + 1/c) >= 2*(sqrt a + sqrt b + sqrt c)
\<close>

(*
Resenje:

Primetimo da je
  a + 1/a = a + (a*b + b*c + c*a)/a = a + b + c + (b*c)/a

Odavde je, na osnovu nejednakosti izmedju aritmeticke i geometrijske sredine
  a + 1/a \<ge> b + c + 2*sqrt (b*c) = (sqrt b + sqrt c)^2
pa je
  sqrt (a + 1/a) \<ge> sqrt b + sqrt c
Analogno je i za b i c
  sqrt (b + 1/b) \<ge> sqrt c + sqrt a
  sqrt (c + 1/c) \<ge> sqrt a + sqrt b

Sabiranjem ove tri nejednakosti, dobijamo
  sqrt (a + 1/a) + sqrt (b + 1/b) + sqrt (c + 1/c) \<ge> 2*(sqrt a + sqrt b + sqrt c)
*)

lemma c_plus_1_kroz_c:
  fixes a b c :: real
  assumes "a*b + b*c + c*a = 1" "a>0" "b>0" "c>0"
  shows "c + 1/c = c + (a*b)/c + b + a"
  proof -
    have "c + 1/c = c + (a*b + b*c + c*a)/c"
      using assms(1)
      by auto
    also have "... = c + (a*b + (b*c + c*a))/c"
      by (simp add:is_num_normalize)
    also have "... = c + (a*b)/c + (b*c + c*a)/c"
      by (simp add: add_divide_distrib)
    also have "... = c + (a*b)/c + (b*c)/c + (c*a)/c"
      by (simp add: add_divide_distrib)
    also have "... = c + (a*b)/c + b + a"
      using assms(4)
      by auto
    finally show ?thesis .
  qed

lemma b_plus_1_kroz_b:
  fixes a b c :: real
  assumes "a*b + b*c + c*a = 1" "a>0" "b>0" "c>0"
  shows "b + 1/b = b + a + c + (c*a)/b"
  proof -
    have "b + 1/b = b + (a*b + b*c + c*a)/b"
      using assms(1)
      by auto
    also have "... = b + (a*b + (b*c + c*a))/b"
      by (simp add:is_num_normalize)
    also have "... = b + (a*b)/b + (b*c + c*a)/b"
      by (simp add: add_divide_distrib)
    also have "... = b + (a*b)/b + (b*c)/b + (c*a)/b"
      by (simp add: add_divide_distrib)
    also have "... = b + a + c + (c*a)/b"
      using assms(3)
      by auto
    finally show ?thesis .
  qed

lemma a_plus_1_kroz_a:
  fixes a b c :: real
  assumes "a*b + b*c + c*a = 1" "a>0" "b>0" "c>0"
  shows "a + 1/a = a + b + c + (b*c)/a"
  proof -
    have "a + 1/a = a + (a*b + b*c + c*a)/a"
      using assms(1)
      by auto
    also have "... = a + (a*b + (b*c + c*a))/a"
      by (simp add:is_num_normalize)
    also have "... = a + (a*b)/a + (b*c + c*a)/a"
      by (simp add: add_divide_distrib)
    also have "... = a + (a*b)/a + (b*c)/a + (c*a)/a"
      by (simp add: add_divide_distrib)
    also have "... = a + b + (b*c)/a + c"
      using assms(2)
      by auto
    also have "... = a + b + c + (b*c)/a"
       by auto
    finally show ?thesis .
  qed

lemma deljenje_sa_a:
  fixes a :: real
  assumes "a > 0"
  shows "(a*a + 1)/a = a + 1/a"
  proof -
    have "(a*a + 1)/a = (a*a)/a + 1/a"
      using add_divide_distrib
      by blast
    also have "... = a + 1/a"
      by auto
    finally show ?thesis .
  qed

lemma kvadrat_zbira_korena:
  fixes a b :: real
  assumes "a>0" "b>0"
  shows "a + b + 2*sqrt (a*b) = (sqrt a + sqrt b)^2"
  proof -
    have "a + b + 2*sqrt (a*b) = ((sqrt a)*(sqrt a) + (sqrt b)*(sqrt b) + 2*sqrt (a*b))"
      using assms
      by auto
    also have "... = ((sqrt a)*(sqrt a) + (sqrt b)*(sqrt b) + 2*(sqrt a)*(sqrt b))"
      using real_sqrt_mult
      by fastforce
    also have "... = ((sqrt a)*(sqrt a) + (sqrt b)*(sqrt b) + (sqrt a)*(sqrt b) + (sqrt a)*(sqrt b))"
      by auto
    also have "... = (sqrt a + sqrt b)*(sqrt a + sqrt b)"
      by (simp add: distrib_left ring_class.ring_distribs(2))
    also have "... = (sqrt a + sqrt b)^2"
      by (simp add: power2_eq_square)
    finally show ?thesis .
  qed

lemma pom_nej_c:
  fixes a b c :: real
  assumes "a*b + b*c + c*a = 1" "a>0" "b>0" "c>0"
  shows "c + 1/c \<ge> (sqrt a + sqrt b)^2"
  proof -
    have "(c - sqrt (a*b))^2 \<ge> 0"
      by auto
    then have "c^2 + a*b - 2*c*sqrt (a*b) \<ge> 0"
      using assms(2) assms(3)
      by (smt (verit) power2_diff real_sqrt_pow2 zero_le_mult_iff)
    then have "c^2 + a*b \<ge> 2*c*sqrt (a*b)"
      by auto
    then have "c^2 + a*b + b*c + c*a - b*c - c*a \<ge> 2*c*sqrt (a*b)"
      by auto
    then have "c^2 + a*b + b*c + c*a \<ge> b*c + c*a + 2*c*sqrt (a*b)"
      by auto
    then have "c^2 + 1 \<ge> b*c + c*a + 2*c*sqrt (a*b)"
      using assms
      by auto
    then have "c*c + 1 \<ge> b*c + a*c + 2*sqrt (a*b)*c"
      by (simp add: mult.commute mult.left_commute power2_eq_square)
    then have "(c*c + 1)/c \<ge> (b*c + a*c + 2*sqrt (a*b)*c)/c"
      using assms(4) divide_right_mono
      by fastforce
    then have "c + 1/c \<ge> b + a + 2*sqrt (a*b)"
      using assms(4)
      by (metis deljenje_sa_a distrib_right div_by_1 divide_divide_eq_right divide_self_if less_irrefl)
    then have "c + 1/c \<ge> a + b + 2*sqrt (a*b)"
      by auto
    then have "c + 1/c \<ge> (sqrt a + sqrt b)^2"
      using assms(2) assms(3)
      by (simp add:kvadrat_zbira_korena)
    then show ?thesis .
  qed

lemma pom_nej_b:
  fixes a b c :: real
  assumes "a*b + b*c + c*a = 1" "a>0" "b>0" "c>0"
  shows "b + 1/b \<ge> (sqrt c + sqrt a)^2"
  proof -
    have "(b - sqrt (c*a))^2 \<ge> 0"
      by auto
    then have "b^2 + c*a - 2*b*sqrt (c*a) \<ge> 0"
      using assms(2) assms(4)
      by (smt (verit) mult_nonneg_nonneg power2_diff real_sqrt_pow2)
    then have "b^2 + c*a \<ge> 2*b*sqrt (c*a)"
      by auto
    then have "b^2 + a*b + b*c + c*a - a*b - b*c \<ge> 2*b*sqrt (c*a)"
      by auto
    then have "b^2 + a*b + b*c + c*a \<ge> a*b + b*c + 2*b*sqrt (c*a)"
      by auto
    then have "b^2 + 1 \<ge> a*b + b*c + 2*b*sqrt (c*a)"
      using assms
      by auto
    then have "b*b + 1 \<ge> a*b + c*b + 2*sqrt (c*a)*b"
      by (simp add: mult.commute mult.left_commute power2_eq_square)
    then have "(b*b + 1)/b \<ge> (a*b + c*b + 2*sqrt (a*c)*b)/b"
      using assms(3)
      by (smt (verit, del_insts) divide_right_mono mult.commute)
    then have "b + 1/b \<ge> a + c + 2*sqrt (c*a)"
      using assms
      by (smt (verit, best) kvadrat_zbira_korena pom_nej_c)
    then have "b + 1/b \<ge> c + a + 2*sqrt (c*a)"
      by auto
    then have "b + 1/b \<ge> (sqrt c + sqrt a)^2"
      using assms(2) assms(4)
      by (simp add:kvadrat_zbira_korena)
    then show ?thesis .
  qed

lemma pom_nej_a:
  fixes a b c :: real
  assumes "a*b + b*c + c*a = 1" "a>0" "b>0" "c>0"
  shows "a + 1/a \<ge> (sqrt b + sqrt c)^2"
  proof -
    have "(a - sqrt (b*c))^2 \<ge> 0"
      by auto
    then have "a^2 + b*c - 2*a*sqrt (b*c) \<ge> 0"
      using assms(3) assms(4)
      by (smt (verit, best) mult_nonneg_nonneg power2_diff real_sqrt_pow2)
    then have "a^2 + b*c \<ge> 2*a*sqrt (b*c)"
      by auto
    then have "a^2 + a*b + b*c + c*a - a*b - c*a \<ge> 2*a*sqrt (b*c)"
      by auto
    then have "a^2 + a*b + b*c + c*a \<ge> a*b + c*a + 2*a*sqrt (b*c)"
      by auto
    then have "a^2 + 1 \<ge> a*b + c*a + 2*a*sqrt (b*c)"
      using assms
      by auto
    then have "a*a + 1 \<ge> b*a + c*a + 2*sqrt (b*c)*a"
      by (simp add: mult.commute mult.left_commute power2_eq_square)
    then have "(a*a + 1)/a \<ge> (b*a + c*a + 2*sqrt (b*c)*a)/a"
      using assms(2) divide_right_mono
      by fastforce
    then have "a + 1/a \<ge> b + c + 2*sqrt (b*c)"
      using assms(2)
      by (metis comm_semiring_class.distrib deljenje_sa_a div_by_1 divide_divide_eq_right divide_self_if less_irrefl)
    then have "a + 1/a \<ge> (sqrt b + sqrt c)^2"
      using assms
      by (simp add:kvadrat_zbira_korena)
    then show ?thesis .
  qed

lemma pom_c:
  fixes a b c :: real
  assumes "a*b + b*c + c*a = 1" "a>0" "b>0" "c>0"
  shows "sqrt (c + 1/c) \<ge> sqrt a + sqrt b"
  proof -
    have "c + 1/c \<ge> (sqrt a + sqrt b)^2"
      using assms
      by (simp add:pom_nej_a)
    then have "sqrt (c + 1/c) \<ge> sqrt ((sqrt a + sqrt b)^2)"
      by (simp add: real_le_rsqrt)
    then have "sqrt (c + 1/c) \<ge> (sqrt a + sqrt b)"
      by force
    then show ?thesis .
  qed

lemma pom_b:
  fixes a b c :: real
  assumes "a*b + b*c + c*a = 1" "a>0" "b>0" "c>0"
  shows "sqrt (b + 1/b) \<ge> sqrt c + sqrt a"
  proof -
    have "b + 1/b \<ge> (sqrt c + sqrt a)^2"
      using assms
      by (simp add:pom_nej_a)
    then have "sqrt (b + 1/b) \<ge> sqrt ((sqrt c + sqrt a)^2)"
      by (simp add: real_le_rsqrt)
    then have "sqrt (b + 1/b) \<ge> (sqrt c + sqrt a)"
      by force
    then show ?thesis .
  qed

lemma pom_a:
  fixes a b c :: real
  assumes "a*b + b*c + c*a = 1" "a>0" "b>0" "c>0"
  shows "sqrt (a + 1/a) \<ge> sqrt b + sqrt c"
  proof -
    have "a + 1/a \<ge> (sqrt b + sqrt c)^2"
      using assms
      by (simp add:pom_nej_a)
    then have "sqrt (a + 1/a) \<ge> sqrt ((sqrt b + sqrt c)^2)"
      by (simp add: real_le_rsqrt)
    then have "sqrt (a + 1/a) \<ge> (sqrt b + sqrt c)"
      by force
    then show ?thesis .
  qed

lemma glavna:
  fixes a b c :: real
  assumes "a*b + b*c + c*a = 1" "a>0" "b>0" "c>0"
  shows "sqrt (a + 1/a) + sqrt (b + 1/b) + sqrt (c + 1/c) \<ge> 2*(sqrt a + sqrt b + sqrt c)"
  proof -
    have "sqrt (a + 1/a) \<ge> sqrt b + sqrt c"
      using assms
      by (simp add: pom_a)
    then have "sqrt (a + 1/a) + sqrt (b + 1/b) \<ge> sqrt b + sqrt c + sqrt c + sqrt a"
      using assms
      by (smt (verit, best) pom_b)
    then have "sqrt (a + 1/a) + sqrt (b + 1/b) + sqrt (c + 1/c) \<ge> sqrt b + sqrt c + sqrt c + sqrt a + sqrt a + sqrt b"
      using assms
      by (smt (verit, ccfv_SIG) pom_c)
    then have "sqrt (a + 1/a) + sqrt (b + 1/b) + sqrt (c + 1/c) \<ge> 2*(sqrt a + sqrt b + sqrt c)"
      by auto
    then show ?thesis .
  qed

end