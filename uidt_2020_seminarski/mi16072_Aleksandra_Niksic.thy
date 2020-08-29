text\<open>
  https://imomath.com/srb/zadaci/2017_smo_resenja.pdf 
  Prvi dan, zadatak 1:
  Neka su a, b i c pozitivni realni brojevi za koje vazi a+b+c = 1.
  Treba dokazati navedenu teoremu.
\<close>

theory mi16072_Aleksandra_Niksic
  imports HOL.Real Complex_Main
begin

lemma pomocna_lema:
  fixes a b c :: real
  assumes "a + b + c = 1" "a > 0" "b > 0"  "c > 0"
  shows "1 - (a^2 + b^2 + c^2) = 2 * (a*b + b*c + c*a)"
  sorry

lemma aritmeticko_geometrijska_nejednakost:
  fixes a b c :: real
  assumes "a > 0" "b > 0"  "c > 0"
  shows "root 2 a*b*c \<le> (a^2 + b^2 + c^2) div 3 "
  sorry

lemma pomocnaAG:
  fixes a b c :: real
  assumes "a > 0" "b > 0"  "c > 0"
  shows "2*a*b * sqrt((2*b + 1) * (2*c + 1)) \<le> a*b * (2*b + 2*c + 2)"
  sorry

theorem 
  fixes a b c :: real
  assumes "a + b + c = 1" "a > 0" "b > 0"  "c > 0"
  shows "sqrt (a * (2*b + 1)) + sqrt(b * (2*c + 1)) + sqrt(c * (2*a + 1)) \<le>
         sqrt(2 - (a^2 + b^2 + c^2))" 
  sorry
end
