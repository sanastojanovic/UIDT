theory mi16135_Stefan_Golubovic
  imports Complex_Main 
begin

text\<open>
  Prvi dan, zadatak 2 na linku: https://imomath.com/srb/zadaci/2000_mmo.pdf

  Neka su a, b, c pozitivni realni brojevi takvi da je a * b * c = 1. Dokazati da je
  (a - 1 + 1/b) * (b - 1 + 1/c) * (c - 1 + 1/a) \<le> 1.
 \<close>

lemma nejednakost:
  fixes a b c::real
  assumes "a > 0" "b > 0" "c > 0" "a * b * c = 1"
  shows "(a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) \<le> 1"
  sorry
 
end