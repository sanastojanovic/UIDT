theory mi16315_Andjela_Janosevic
  imports Complex_Main
begin

text \<open>
Zadatak 2, drugi razred sa linka: https://imomath.com/srb/zadaci/RS_2016_republicko_resenja.pdf


Neka su x, y, z nenegativni brojevi takvi da je x+y+z = 1.
Dokazati da vazi nejednakost x^3 + y^3 + z^3 + 2*(x*y+y*z+z*x) \<ge> (3::real)/(4::real)
\<close>


lemma zadatak:
  fixes x y z :: real
  assumes "x \<ge> 0" "y \<ge> 0" "z \<ge> 0"  " x + y + z = 1" 
  shows "x^3 + y^3 + z^3 + 2*(x*y+y*z+z*x) \<ge> (3::real)/(4::real)"
  sorry
  
end