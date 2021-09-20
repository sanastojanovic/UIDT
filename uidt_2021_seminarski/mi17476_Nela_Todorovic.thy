theory mi17476_Nela_Todorovic
  imports Complex_Main 
begin

text\<open>
IMO 2005, zadatak 3: https://imomath.com/srb/zadaci/2005_mmo.pdf

Neka su x, y i z pozitivni realni brojevi takvi da je x*y*z \<ge> 1. Dokazati da je:
(x^5 - x^2)/(x^5 + y^2 + z^2) + (y^5 - y^2)/(x^2 + y^5 + z^2) + (z^5 - z^2)/(x^2 + y^2 + z^5) >=0

\<close>


lemma seminarski:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0" "x*y*z \<ge> 1"
  shows "(x^5 - x^2)/(x^5 + y^2 + z^2) + (y^5 - y^2)/(x^2 + y^5 + z^2) + (z^5 - z^2)/(x^2 + y^2 + z^5) \<ge> 0"
  ussing assms
  sorry

