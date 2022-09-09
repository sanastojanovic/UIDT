theory mi17236_Aleksandar_Lisov
  imports Main HOL.Real

begin

text‹
Udzbenik: IMO2010SL
Link ka udzbeniku: https://www.imo-official.org/problems/IMO2010SL.pdf
Zadatak: Algebra A2
Strane: 8,9
›

section‹Prvi seminarski›

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

lemma :
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

lemma

lemma zadatak:
  fixes a b c d :: real
  assumes "a + b + c + d = 6" 
  assumes "a^2 + b^2 + c^2 + d^2 = 12"
  shows "36 ≤ 4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)"
        "4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ≤ 48"
proof-
  show "36 ≤ 4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)"
  proof-
    have "4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) = -((a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4) + 52" using assms pomocna by auto
    (* sada treba pokazati da je 36 ≤ -((a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4) + 52 *)
    (* tj (a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4 ≤ 16 *)
    sorry
  qed
next
  show "4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ≤ 48"
    sorry
qed

section‹Drugi seminarski›

end
