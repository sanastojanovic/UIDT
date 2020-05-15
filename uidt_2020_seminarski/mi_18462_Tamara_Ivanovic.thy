theory mi_18462_Tamara_Ivanovic
imports Complex_Main

(* https://imomath.com/srb/zadaci/2011_bmo_resenja.pdf
    Zadatak 2
*)

begin

lemma nejednacina:
  fixes x y z :: real
  assumes "x + y + z = 0"
  shows "(x + (x+2))/(2*x\<^sup>2 +1) +
         (y + (y+2))/(2*y\<^sup>2 +1) +
         (z + (z+2))/(2*z\<^sup>2 +1) \<ge> 0"
         sorry

end