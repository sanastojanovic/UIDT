theory mi_18462_Tamara_Ivanovic
imports Complex_Main "HOL-Library.Multiset"

(*
I seminarski zadatak

 https://imomath.com/srb/zadaci/2011_bmo_resenja.pdf
    Zadatak 2
    Ako su x, y, z realni brojevi takvi da je x+y+z=0, dokazati nejednakost

    (x*(x+2)) / (2*x\<^sup>2 +1) + (y*(y+2)) / (2*y\<^sup>2 +1) + (z*(z+2)) / (2*z\<^sup>2 +1) \<ge> 0
    
    Kada vazi jednakost? Resenje: 
                         Jednakost vazi ako je x = y = z = 0 ili 
                         (x,y,z) = (-1/2, -1/2,1) do na permutaciju
*)

begin

lemma nejednacina:
  fixes x y z :: real
  assumes "x + y + z = 0"
  shows "(x*(x+2)) / (2*x\<^sup>2 +1) +
         (y*(y+2)) / (2*y\<^sup>2 +1) +
         (z*(z+2)) / (2*z\<^sup>2 +1) \<ge> 0"
         sorry
         
lemma resenje_1_jednacina:
fixes x y z :: real
assumes "x = 0" "y = 0" "z = 0"
shows "(x*(x+2)) / (2*x\<^sup>2 +1) +
      (y*(y+2)) / (2*y\<^sup>2 +1) +
      (z*(z+2)) / (2*z\<^sup>2 +1) = 0"
      sorry

lemma resenje_2_jednacina:
fixes x y z :: real
assumes "(x,y,z) = (-1/2, -1/2, 1)
         \<or> (x,y,z) = (-1/2, 1, -1/2)
         \<or> (x,y,z) = (1, -1/2, -1/2)"
shows "(x*(x+2)) / (2*x\<^sup>2 +1) +
      (y*(y+2)) / (2*y\<^sup>2 +1) +
      (z*(z+2)) / (2*z\<^sup>2 +1) = 0"
      sorry
      

(* Resenje gde su permutacije rucno ispisane i sadrzi sve varijante resenja *)
lemma resenja_jednacine_objedinjeno:
fixes x y z :: real
assumes "(x, y, z) = (0,0,0) \<or> (x,y,z) = (-1/2, -1/2, 1)
                             \<or> (x,y,z) = (-1/2, 1, -1/2)
                             \<or> (x,y,z) = (1, -1/2, -1/2)"
shows "(x*(x+2)) / (2*x\<^sup>2 +1) +
      (y*(y+2)) / (2*y\<^sup>2 +1) +
      (z*(z+2)) / (2*z\<^sup>2 +1) = 0"
      sorry
end