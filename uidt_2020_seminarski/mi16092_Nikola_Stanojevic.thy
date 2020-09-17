theory mi16092_Nikola_Stanojevic
  imports Complex_Main 
begin

text\<open>
  Dan 1, zadatak 3 na linku: https://imomath.com/srb/zadaci/2005_mmo.pdf?fbclid=IwAR0mX4Z6RlQIeMVoHAVFrq94rRcz9XrQH4XFwgr7vTFT3TFLBn7BfSU4Iq0

  Neka su x, y i z pozitivni realni brojevi takvi da je x*y*z >= 1.
  Dokazati da je
    (x^5-x^2)/(x^5+y^2+z^2)+(y^5-y^2)/(y^5+z^2+x^2)+(z^5-z^2)/(z^5+x^2+y^2)>=0.
 \<close>

lemma nejednakost:
  fixes x y z::real
  assumes "x > 0" "y > 0" "z > 0" "x * y * z \<ge> 1"
  shows "(x^5 - x^2) / (x^5 + y^2 + z^2) + 
         (y^5 - y^2) / (y^5 + z^2 + x^2) +
         (z^5 - z^2) / (z^5 + x^2 + y^2) \<ge> 0"
  sorry
 
end
