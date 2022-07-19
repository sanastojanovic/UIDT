theory mi17236_Aleksandar_Lisov
  imports Main HOL.Real

begin

text\<open>
Link ka knjizi: https://www.imo-official.org/problems/IMO2010SL.pdf
Zadatak: Algebra A2
\<close>

section\<open>Prvi seminarski\<close>

lemma zadatak:
  fixes a b c d :: real
  assumes "a + b + c + d = 6" 
  assumes "a^2 + b^2 + c^2 + d^2 = 12"
  shows "36 \<le> 4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)"
        "4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) \<le> 48"
  sorry

section\<open>Drugi seminarski\<close>

end