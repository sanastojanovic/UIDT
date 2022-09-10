theory mi17236_Aleksandar_Lisov
  imports Main HOL.Real

begin

text\<open>
Udzbenik: IMO2010SL
Link ka udzbeniku: https://www.imo-official.org/problems/IMO2010SL.pdf
Zadatak: Algebra A2
Strane: 8,9
\<close>

lemma a_minus_b_na_cetvrti:
  fixes a b :: real
  shows "(a-b)^4 = a^4 - 4*a^3*b + 6*a^2*b^2 - 4*a*b^3 + b^4"
proof-
  have "(a-b)^4 = ((a-b)^2)^2" by auto
  also have "... = (a-b)^2 * (a-b)^2" by auto
  also have "... = (a^2 - 2*a*b + b^2) * (a^2 - 2*a*b + b^2)"
    (*sledgehammer*)
    by (simp add: diff_add_eq power2_diff)
  also have "... = a^4 - 2*a^2*a*b + a^2*b^2 - 2*a*b*a^2 + 4*a*b*a*b - 2*a*b*b^2 + b^2*a^2 - 2*b^2*a*b + b^4"
    by (auto simp add: algebra_simps)
  also have "... = a^4 - 2*a^3*b + a^2*b^2 - 2*a^3*b + 4*a^2*b^2 - 2*a*b^3 + a^2*b^2 - 2*b^3*a + b^4"
    (*sledgehammer*)
    by (simp add: power2_eq_square power3_eq_cube)
  also have "... = a^4 - 4*a^3*b + 6*a^2*b^2 - 4*a*b^3 + b^4" by auto
  finally show ?thesis by auto
qed

lemma pomocna:
  fixes a b c d :: real
  assumes "a + b + c + d = 6" 
  assumes "a^2 + b^2 + c^2 + d^2 = 12"
  shows "4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) = -((a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4) + 52"
proof-
  have "4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) = 4*a^3 + 4*b^3 + 4*c^3 + 4*d^3 - a^4 - b^4 - c^4 - d^4" by auto
  also have "... = - (a^4 + b^4 + c^4 + d^4) + 4*a^3 + 4*b^3 + 4*c^3 + 4*d^3" by auto
  also have "... = - ((a-1)^4 + 4*a^3 - 6*a^2 + 4*a - 1 + (b-1)^4 + 4*b^3 - 6*b^2 + 4*b - 1 + (c-1)^4 + 4*c^3 - 6*c^2 + 4*c - 1 + (d-1)^4 + 4*d^3 - 6*d^2 + 4*d - 1) + 4*a^3 + 4*b^3 + 4*c^3 + 4*d^3" by (auto simp add: a_minus_b_na_cetvrti)
  also have "... = - ((a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4 + 4*a^3 + 4*b^3 + 4*c^3 + 4*d^3 - 6*a^2 - 6*b^2 - 6*c^2 - 6*d^2 + 4*a + 4*b + 4*c + 4*d - 4) + 4*(a^3 + b^3 + c^3 + d^3)" by auto
  also have "... = - ((a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4 + 4*(a^3 + b^3 + c^3 + d^3) - 6*(a^2 + b^2 + c^2 + d^2) + 4*(a + b + c + d) - 4) + 4*(a^3 + b^3 + c^3 + d^3)" by auto
  also have "... = - ((a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4 + 4*(a^3 + b^3 + c^3 + d^3) - 6*12 + 4*6 - 4) + 4*(a^3 + b^3 + c^3 + d^3)" using assms by auto
  also have "... = - ((a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4 - 6*12 + 4*6 - 4)" by auto
  finally show ?thesis by auto
qed

lemma razvoj_binoma:
  fixes a :: real
  shows "(a-1)^2 = a^2 - 2*a + 1"
  (*sledgehammer*)
  by (simp add: power2_diff)

lemma pomocna2:
  fixes a b c d :: real
  assumes "a + b + c + d = 6" 
  assumes "a^2 + b^2 + c^2 + d^2 = 12"
  shows "(a-1)^2 + (b-1)^2 + (c-1)^2 + (d-1)^2 = 4"
proof-
  have "(a-1)^2 + (b-1)^2 + (c-1)^2 + (d-1)^2 = (a-1)*(a-1) + (b-1)*(b-1) + (c-1)*(c-1) + (d-1)*(d-1)"
    (*sledgehammer*)
    by (simp add: power2_eq_square)
  also have "... = a*a - a - a + 1 + b*b - b - b + 1 + c*c - c - c + 1 + d*d - d - d + 1"
    (*sledgehammer*)
    by (smt (verit) power2_eq_square razvoj_binoma)
  also have "... = a^2 - 2*a + 1 + b^2 - 2*b + 1 + c^2 - 2*c + 1 + d^2 - 2*d + 1" by (simp add: power2_eq_square)
  also have "... = (a^2 + b^2 + c^2 + d^2) - 2*(a + b + c + d) + 4" by auto
  finally show ?thesis by (auto simp add: assms)
qed

lemma neresiva:
  fixes a b c d :: real
  shows "a^4 + b^4 + c^4 + d^4 \<ge> (a^2 + b^2 + c^2 + d^2)^2 / 4"
  sorry

lemma lm1:
  fixes a b c d :: real
  assumes "(a-1)^2 + (b-1)^2 + (c-1)^2 + (d-1)^2 = 4"
  shows "((a-1)^2 + (b-1)^2 + (c-1)^2 + (d-1)^2)^2 / 4 = 4" using assms by auto

lemma kvadrat_zbira_kvadrata_veci_od_zbira_cetvrtih_stepena:
  fixes a b c d :: real
  shows "(a^2 + b^2 + c^2 + d^2)^2 \<ge> (a^4 + b^4 + c^4 + d^4)"
proof-
  have p1 : "(a^2 + b^2 + c^2 + d^2)^2 = (a^2 + b^2 + c^2 + d^2)*(a^2 + b^2 + c^2 + d^2)" using power2_eq_square by auto
  then have p2 : "... = a^2*a^2 + a^2*b^2 + a^2*c^2 + a^2*d^2 + b^2*a^2 + b^2*b^2 + b^2*c^2 + b^2*d^2 + c^2*a^2 + c^2*b^2 + c^2*c^2 + c^2*d^2 + d^2*a^2 + d^2*b^2 + d^2*c^2 + d^2*d^2" by (auto simp add: algebra_simps)
  then have p3 : "... = a^4 + b^4 + c^4 + d^4 + 2*a^2*b^2 + 2*a^2*c^2 + 2*a^2*d^2 + 2*b^2*c^2 + 2*b^2*d^2 + 2*c^2*d^2" 
    (*sledgehammer*)
    using power_add_numeral ring_class.ring_distribs(1) by auto
  then have "a^4 + b^4 + c^4 + d^4 + 2*a^2*b^2 + 2*a^2*c^2 + 2*a^2*d^2 + 2*b^2*c^2 + 2*b^2*d^2 + 2*c^2*d^2 \<ge> (a^4 + b^4 + c^4 + d^4) " by auto
  then have "(a^2 + b^2 + c^2 + d^2)^2 \<ge> (a^4 + b^4 + c^4 + d^4)" using p1 p2 p3 by auto
  then show ?thesis .
qed

lemma zadatak:
  fixes a b c d :: real
  assumes "a + b + c + d = 6" 
  assumes "a^2 + b^2 + c^2 + d^2 = 12"
  shows "36 \<le> 4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)"
        "4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) \<le> 48"
proof-
  show "36 \<le> 4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)"
  proof-
    have p1 : "4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) = -((a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4) + 52" using assms pomocna by auto
    (* sada treba pokazati da je 36 \<le> -((a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4) + 52 *)
    (* tj (a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4 \<le> 16 *)
    then have p2 : "(a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4 \<le> ((a-1)^2 + (b-1)^2 + (c-1)^2 + (d-1)^2)^2" by (auto simp add: kvadrat_zbira_kvadrata_veci_od_zbira_cetvrtih_stepena)
    have "((a-1)^2 + (b-1)^2 + (c-1)^2 + (d-1)^2)^2 = 16" using assms(1) assms(2) pomocna2 by auto
    then have "(a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4 \<le> 16" using p2 by auto
    then have "36 \<le> 4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)" using p1 by auto
    then show ?thesis .
  qed
next
  show "4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) \<le> 48"
  proof-
    have p1 : "4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) = -((a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4) + 52" using assms pomocna by auto
    (* sada treba pokazati da je -((a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4) + 52 \<le> 48 *)
    (* tj (a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4 \<ge> 4 *)
    have p2 : "(a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4 \<ge> ((a-1)^2 + (b-1)^2 + (c-1)^2 + (d-1)^2)^2 / 4" using neresiva by blast
    then have "((a-1)^2 + (b-1)^2 + (c-1)^2 + (d-1)^2)^2 / 4 = 4"
      using assms(1) assms(2) lm1 pomocna2 by blast
    then have "(a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4 \<ge> 4" using p2 by auto
    then have "4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) \<le> 48" using p1 by auto
    then show ?thesis .
  qed
qed

end
