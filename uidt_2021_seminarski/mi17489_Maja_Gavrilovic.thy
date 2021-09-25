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

end