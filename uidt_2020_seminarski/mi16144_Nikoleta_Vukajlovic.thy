theory mi16144_Nikoleta_Vukajlovic
  imports Complex_Main
begin

text\<open>
  Prvi dan, zadatak 2 na linku: https://imomath.com/srb/zadaci/1995_mmo.pdf

  Neka su a, b, c pozitivni realni brojevi sa a*b*c= 1. Dokazati nejednakost
  1/(a ^ 3 *(b+c))+1/(3*(a+c))+1/(3*(a+b))\<ge>3/2.
 \<close>

lemma zadatak:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a * b * c = 1"
  shows "1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (a + c)) + 1 / (c ^ 3 * (a + b)) \<ge> 3/2"
  sorry

end