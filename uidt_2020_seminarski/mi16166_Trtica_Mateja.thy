theory mi16166_Trtica_Mateja
  imports Complex_Main
begin

text \<open>
Zadatak 1, treci razred.
Link: https://imomath.com/srb/zadaci/2014_okruzno.pdf
Tekst zadatka:
Neka su x,y,z realni brojevi takvi da vazi x+y+z=0. Dokazati da vazi nejednakost:

  6*(x^3 + y^3 + z^3)\<le> (x^2 + y^2 + z^2)^3
\<close>


lemma zadatak:
  fixes x y z :: real
  assumes "x + y + z = 0"
  shows "6*(x^3 + y^3 + z^3)\<le> (x^2 + y^2 + z^2)^3"
  sorry
  
end