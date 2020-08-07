theory mi16093_Jovanovic_Branislav
  imports Complex_Main
begin

text\<open>
 Prvi zadatak A kategorije cetvrtog razreda sa takmicenja:
 https://imomath.com/srb/zadaci/2016_opstinsko.pdf
 
Tekst zadatka: Neka su a i b prirodni brojevi, pri cemu
 vazi a>b. Dokazati nejednakost:
  
 a^3 + a*(b^2) + b^2 + b \<ge> 2*(a^2)*b + a^2.
 
 \<close>

lemma zadatak:
  fixes a b :: nat
  assumes "a > b"
  shows "a^3 + a*(b^2) + b^2 + b \<ge> 2*(a^2)*b + a^2"
  sorry

end