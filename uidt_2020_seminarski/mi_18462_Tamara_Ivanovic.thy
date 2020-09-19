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
      oops

      
(* II seminarski zadatak: Raspisivanje dokaza I seminarskog zadatka *)

\<comment> \<open>Ideja resenja: 
  - Pokazati da se pocetna nejednacina moze drugacije zapisati
  - Dokazati da vazi nejednacina (izmenjena) na osnovu Kosi-Svarcove nejednakosti
  - Pokazati da lema vazi iz prethodna dva navedena
\<close>


\<comment> \<open>Neka je, bez gubitka na opstosti |z| = max{|x|,|y|, |z|}\<close>
definition maksimum :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
"maksimum a b c = (if (a > b \<and> a > c) then a 
                    else if b > c then b
                    else c)"

value "maksimum 1 3 2"

(* Kosi-Svarcova nejednakost za R^3 *)
 
\<comment> \<open>Nejednacinu dokazujemo primenom Kosi-Svarcove nejednakosti, te je potrebno i nju uvesti\<close>
\<comment> \<open> S tim sto sqrt(x1^2 + x2^2 + x3^2) * sqrt(y1^2 + y2^2 + y3^2) \<ge> (x1*y1 + x2*y2 + x3*y3)
sam odmah kvadrirala\<close>

\<comment> \<open>Pomocne leme za dokaz Kosi-Svarca\<close>
lemma proizvod_trinoma:
fixes x1 x2 x3 y1 y2 y3 :: real             \<comment> \<open>bez fiksiranja tipa ne radi dokaz\<close>
assumes "x1 > 0" "x2 > 0" "x3 > 0"  "y1 > 0" "y2 > 0" "y3 > 0"
shows "x1\<^sup>2*y1\<^sup>2 + x2\<^sup>2*y2\<^sup>2 + x3\<^sup>2*y3\<^sup>2 + x1\<^sup>2*y2\<^sup>2 + x2\<^sup>2*y1\<^sup>2 + x1\<^sup>2*y3\<^sup>2 + x3\<^sup>2*y1\<^sup>2 + x2\<^sup>2*y3\<^sup>2 + x3\<^sup>2*y2\<^sup>2 = (x1\<^sup>2 + x2\<^sup>2 + x3\<^sup>2) * (y1\<^sup>2 + y2\<^sup>2 + y3\<^sup>2)"
by (simp add:  distrib_left distrib_right)

lemma pomocna_kosi:
  fixes x1 x2 x3 y1 y2 y3 :: real
  assumes "x1 > 0" "x2 > 0" "x3 > 0"  "y1 > 0" "y2 > 0" "y3 > 0"
  shows "x1\<^sup>2*y1\<^sup>2 + x2\<^sup>2*y2\<^sup>2 + x3\<^sup>2*y3\<^sup>2 + 2*x1*y1*x2*y2 +  2*x1*y1*x3*y3 +  2*x2*y2*x3*y3 = (x1*y1 + x2*y2 + x3*y3)\<^sup>2"
proof-
have "(x1*y1 + x2*y2 + x3*y3)\<^sup>2 = (x1*y1 + x2*y2)\<^sup>2 + 2*(x1*y1 + x2*y2)*x3*y3 + (x3*y3)\<^sup>2"    
   \<comment> \<open>find_theorems "(_ + _)^2"\<close> 
    by (simp add:  Power.comm_semiring_1_class.power2_sum)
  also have "... = (x1*y1)\<^sup>2 + 2*(x1*y1)*(x2*y2) + (x2*y2)\<^sup>2 + 2*(x1*y1 + x2*y2)*x3*y3 + (x3*y3)\<^sup>2"
    by (simp add:  Power.comm_semiring_1_class.power2_sum)
  also have "... =  (x1*y1)\<^sup>2 + 2*x1*y1*x2*y2 + (x2*y2)\<^sup>2 + 2*(x1*y1)*(x3*y3) + 2*(x2*y2)*x3*y3 + (x3*y3)\<^sup>2"
    \<comment> \<open>find_theorems "(_ + _) * _"\<close>
    by (simp add: mult.commute ring_class.ring_distribs(1)  Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(8))   
  finally show ?thesis
    using algebra_simps
    by (simp add: power_mult_distrib)
qed

\<comment> \<open>Dokaz Kosi-Svarca\<close>

lemma kosi_svarc:
  fixes x1 x2 x3 y1 y2 y3 :: real
  assumes "x1 > 0" "x2 > 0" "x3 > 0"  "y1 > 0" "y2 > 0" "y3 > 0"
  shows "(x1\<^sup>2 + x2\<^sup>2 + x3\<^sup>2) * (y1\<^sup>2 + y2\<^sup>2 + y3\<^sup>2) \<ge> (x1*y1 + x2*y2 + x3*y3)\<^sup>2"
  proof-
  have "(x1*y2 - x2*y1)\<^sup>2 + (x1*y3 - x3*y1)\<^sup>2 + (x2*y3 - x3*y2)\<^sup>2 \<ge> 0"  \<comment> \<open>\<forall>xi,xj,yi,yj: (xi*yj -xj*yi)^2 \<ge> 0\<close>
    by simp
    then have "(x1*y2)\<^sup>2 - 2*(x1*y2)*(x2*y1) + (x2*y1)\<^sup>2 + 
               (x1*y3)\<^sup>2 - 2*(x1*y3)*(x3*y1) + (x3*y1)\<^sup>2 + 
               (x2*y3)\<^sup>2 - 2*(x2*y3)*(x3*y2) + (x3*y2)\<^sup>2 \<ge> 0" \<comment> \<open>Primena kvadrata binoma na levoj strani\<close>
          (*     sledgehammer
               find_theorems "(_ - _ )\<^sup>2" *)
               by (simp add:Power.comm_ring_1_class.power2_diff)
    then have "(x1*y2)\<^sup>2 + (x2*y1)\<^sup>2 + (x1*y3)\<^sup>2 + (x3*y1)\<^sup>2 + (x2*y3)\<^sup>2 + (x3*y2)\<^sup>2
                          \<ge> 2*(x1*y2)*(x2*y1) + 2*(x1*y3)*(x3*y1) + 2*(x2*y3)*(x3*y2)" \<comment> \<open>ostavljanje kvadrata na levoj str.\<close>
                          by auto
   then have "x1\<^sup>2*y2\<^sup>2 + x2\<^sup>2*y1\<^sup>2 + x1\<^sup>2*y3\<^sup>2 + x3\<^sup>2*y1\<^sup>2 + x2\<^sup>2*y3\<^sup>2 + x3\<^sup>2*y2\<^sup>2
                          \<ge> 2*x1*y1*x2*y2 +  2*x1*y1*x3*y3 +  2*x2*y2*x3*y3"
                          sledgehammer
                          using assms
                          by (metis (mono_tags, hide_lams) ab_semigroup_mult_class.mult_ac(1) add.commute mult.commute mult.left_commute power_mult_distrib)
  then have "x1\<^sup>2*y1\<^sup>2 + x2\<^sup>2*y2\<^sup>2 + x3\<^sup>2*y3\<^sup>2 + x1\<^sup>2*y2\<^sup>2 + x2\<^sup>2*y1\<^sup>2 + x1\<^sup>2*y3\<^sup>2 + x3\<^sup>2*y1\<^sup>2 + x2\<^sup>2*y3\<^sup>2 + x3\<^sup>2*y2\<^sup>2
             \<ge> x1\<^sup>2*y1\<^sup>2 + x2\<^sup>2*y2\<^sup>2 + x3\<^sup>2*y3\<^sup>2 + 2*x1*y1*x2*y2 +  2*x1*y1*x3*y3 +  2*x2*y2*x3*y3"  \<comment> \<open>dodavanje x1^2*y1^2 + x2^2*y2^2 +  x3^2*y3^2 na obe str. da dobijem ||x||*||y||\<close>                    
             by auto
  then have "(x1\<^sup>2 + x2\<^sup>2 + x3\<^sup>2) * (y1\<^sup>2 + y2\<^sup>2 + y3\<^sup>2) \<ge> 
              x1\<^sup>2*y1\<^sup>2 + x2\<^sup>2*y2\<^sup>2 + x3\<^sup>2*y3\<^sup>2 + 2*x1*y1*x2*y2 +  2*x1*y1*x3*y3 +  2*x2*y2*x3*y3"    \<comment> \<open>zamena leve str. sa mnozenjem trinoma jer je desna str. upravo (suma xk*yk)^2\<close>
              using proizvod_trinoma assms
              by auto
  then show ?thesis
 (*  find_theorems "(_ + _ + _)\<^sup>2" \<comment> \<open>vraca found nothing, tako da pisem pomocnu lemu za proizvod sa desne str.\<close> *)
   using pomocna_kosi assms
   by simp
qed


\<comment> \<open>Prvi korak u resenju je da se trazena nejednakost moze i drugacije zapisati\<close>

(* Od pocetne do izmenjene se stize tako sto je pocetna nejednacina pomozi sa 2 sa obe strane,
zatim se doda 3 sa obe strane (sa leve zapravo svakom razlomku po 1) i stize se do izmenjene *)


lemma ekvivalentan_zapis_nejednacine:
fixes x y z :: real
assumes "x + y + z = 0"
shows "(2*x+1)\<^sup>2 / (2*x\<^sup>2 +1) +(2*y+1)\<^sup>2 / (2*y\<^sup>2 +1) + (2*z+1)\<^sup>2 / (2*z\<^sup>2 +1) \<ge> 3 "
proof-
have "(x*(x+2)) / (2*x\<^sup>2 +1) + (y*(y+2)) / (2*y\<^sup>2 +1) + (z*(z+2)) / (2*z\<^sup>2 +1) \<ge> 0 "
  using assms 
  using nejednacina
  by blast
 then have "2 * ((x*(x+2)) / (2*x\<^sup>2 +1) + (y*(y+2)) / (2*y\<^sup>2 +1) + (z*(z+2)) / (2*z\<^sup>2 +1)) \<ge> 0"
  by auto
then have "2*(x\<^sup>2 + x*2) / (2*x\<^sup>2 +1) + 2*(y\<^sup>2 + y*2) / (2*y\<^sup>2 +1) + 2*(z\<^sup>2 + z*2) / (2*z\<^sup>2 +1) \<ge>  0"  
  by (simp add: distrib_left power2_eq_square)   
then have "(2*x\<^sup>2 + 4*x) / (2*x\<^sup>2 +1) + (2*y\<^sup>2 + 4*y) / (2*y\<^sup>2 +1) + (2*z\<^sup>2 + 4*z) / (2*z\<^sup>2 +1) \<ge>  0"
  by simp
then have "((2*x\<^sup>2 + 4*x) / (2*x\<^sup>2 +1)) + 1 + ((2*y\<^sup>2 + 4*y) / (2*y\<^sup>2 +1)) + 1 + ((2*z\<^sup>2 + 4*z) / (2*z\<^sup>2 +1)) + 1 \<ge>  0 + 1+1+1"
  by simp
then have "((2*x\<^sup>2 + 4*x) / (2*x\<^sup>2 +1)) + ((2*x\<^sup>2 +1) / (2*x\<^sup>2 +1)) 
          + ((2*y\<^sup>2 + 4*y) / (2*y\<^sup>2 +1)) +((2*y\<^sup>2 +1)/ (2*y\<^sup>2 +1))
          + ((2*z\<^sup>2 + 4*z) / (2*z\<^sup>2 +1)) + ((2*z\<^sup>2 +1)/(2*z\<^sup>2 +1)) \<ge> 3"
         by (smt divide_self sum_power2_ge_zero)
then have "((2*x\<^sup>2 + 4*x + 2*x\<^sup>2 +1 ) / (2*x\<^sup>2 +1)) 
          + ((2*y\<^sup>2 + 4*y + 2*y\<^sup>2 +1) / (2*y\<^sup>2 +1))
          + ((2*z\<^sup>2 + 4*z + 2*z\<^sup>2 +1) / (2*z\<^sup>2 +1)) \<ge> 3" 
          by (smt add_divide_distrib)
then have "((4*x\<^sup>2 + 4*x +1 ) / (2*x\<^sup>2 +1)) 
          + ((4*y\<^sup>2 + 4*y +1) / (2*y\<^sup>2 +1))
          + ((4*z\<^sup>2 + 4*z +1) / (2*z\<^sup>2 +1)) \<ge> 3"
          by simp
then show ?thesis
  by (simp add: power2_eq_square field_simps)
qed


\<comment> \<open>Da vazi za izmenjenu nejednakost\<close>
lemma izmenjena_nejednacina:
  fixes x y z :: real
  assumes "x + y + z = 0" "abs z = maksimum (abs x) (abs y) (abs z)"
  shows "(2*x+1)\<^sup>2 / (2*x\<^sup>2 +1) +
         (2*y+1)\<^sup>2 / (2*y\<^sup>2 +1) +
         (2*z+1)\<^sup>2 / (2*z\<^sup>2 +1) \<ge> 3"
         oops
(*         
proof-
have " (2*x+1)\<^sup>2 / (2*x\<^sup>2 +1) + (2*y+1)\<^sup>2 / (2*y\<^sup>2 +1) \<ge> (2* (x+y+1)\<^sup>2)/(x\<^sup>2 + y\<^sup>2 + 1)"
  using kosi_svarc 
  also have "... = 2*(1-z)\<^sup>2 / (x\<^sup>2 + y\<^sup>2 + 1)"
  also have "... \<ge> 2*(1-z)\<^sup>2/(2*z\<^sup>2 + 1)"
  also have "... = 3 - ((2*z + 1)\<^sup>2 / (2*z\<^sup>2 +1))"
qed
*)


\<comment> \<open>Na osnovu toga da moze da se zapise drugacije i da preko KS vazi da tu izmenjenu\<close>
lemma nejednacina_dokaz:
  fixes x y z :: real
  assumes "x + y + z = 0" "abs z = maksimum (abs x) (abs y) (abs z)" \<comment> \<open>Dodata pretpostavka, jer u resenju kazu: Neka je bez gubitka na opstosti |z|=max{|x|, |y|, |z|}\<close>
  shows "(x*(x+2)) / (2*x\<^sup>2 +1) +
         (y*(y+2)) / (2*y\<^sup>2 +1) +
         (z*(z+2)) / (2*z\<^sup>2 +1) \<ge> 0"
proof-
have "(2*x+1)\<^sup>2 / (2*x\<^sup>2 +1) +
         (2*y+1)\<^sup>2 / (2*y\<^sup>2 +1) +
         (2*z+1)\<^sup>2 / (2*z\<^sup>2 +1) \<ge> 3"
         oops
\<comment> \<open>using izmenjena_nejednacina ekvivalentan_zapis_nejednacine\<close>



(* II deo zadatka \<rightarrow> dokaz kada vazi jednacina *)
\<comment> \<open>Rasclanjeno u dokaz svake od kombinacija brojeva i oni dodati u simplifikator, pa odatle da vazi\<close>

lemma resenje_1_jednacina_dokaz[simp]:
fixes x y z :: real
assumes "x = 0" "y = 0" "z = 0"
shows "(x*(x+2)) / (2*x\<^sup>2 +1) +
      (y*(y+2)) / (2*y\<^sup>2 +1) +
      (z*(z+2)) / (2*z\<^sup>2 +1) = 0"
proof-
have " (x*(x+2)) / (2*x\<^sup>2 +1) + (y*(y+2)) / (2*y\<^sup>2 +1) + (z*(z+2)) / (2*z\<^sup>2 +1) 
      =(0*(0+2)) / (2*0\<^sup>2 +1) + (0*(0+2)) / (2*0\<^sup>2 +1) + (0*(0+2)) / (2*0\<^sup>2 +1)"
      using assms
      by simp
also have "... = (0*2)/(0+1) + (0*2)/(0+1) + (0*2)/(0+1)" 
  by simp
also have "... = 0/1 + 0/1 + 0/1"
  by simp
then have "... = 0" 
  by simp
then show ?thesis
  by (simp add: assms(1) assms(2) assms(3))
qed      

lemma resenje_jednacine_2[simp]:
fixes x y z :: real
assumes " (x,y,z) = (-1/2, -1/2, 1)"
shows "((x*(x+2)) / (2*x\<^sup>2 +1)) +
      ((y*(y+2)) / (2*y\<^sup>2 +1)) +
      ((z*(z+2)) / (2*z\<^sup>2 +1)) = 0"       
proof- 
  have "((x*(x+2)) / (2*x\<^sup>2 +1)) + ((y*(y+2)) / (2*y\<^sup>2 +1)) + ((z*(z+2)) / (2*z\<^sup>2 +1))
        =(((-1/2)*((-1/2)+2)) / (2*(-1/2)\<^sup>2+1)) + (((-1/2)*((-1/2)+2)) / (2*(-1/2)\<^sup>2+1)) + ((1*(1+2))/(2*1\<^sup>2+1))"
        using assms
        by simp
  also have "... =  ( ((-1/2) * (((-1)+2*2)/2)) / (2* (1/4) + 1) ) + ( ((-1/2) * (((-1)+2*2)/2)) / (2* (1/4) + 1) ) + ( (1*3)/(2*1+1) )"
        by (simp add: power_divide)
  also have "... = ( ((-1/2) * (3/2)) / (2* (1/4) + 1) ) + ( ((-1/2) * (3/2)) / (2* (1/4) + 1) ) + ( (1*3)/(2*1+1))" 
        by auto
  also have "... = ( (-3/4) / (2/4 +1) ) + ( (-3/4) / (2/4 +1) ) + (3/(2+1)) "
        by simp
  also have "... = ( (-3/4)/ (6/4) ) +  ( (-3/4)/ (6/4) ) + (3/3)"
        by simp
  also have "... = (-3/6) + (-3/6) + 1"
        by simp
  also have "... = -1 + 1"
        by simp
  then have "... = 0"
        by simp
  then show ?thesis
        by (simp add: calculation)
qed



lemma resenje_jednacine_3[simp]:
fixes x y z :: real
assumes " (x,y,z) = (-1/2, 1, -1/2)"
shows "((x*(x+2)) / (2*x\<^sup>2 +1)) +
      ((y*(y+2)) / (2*y\<^sup>2 +1)) +
      ((z*(z+2)) / (2*z\<^sup>2 +1)) = 0"       
proof- 
  have "((x*(x+2)) / (2*x\<^sup>2 +1)) + ((y*(y+2)) / (2*y\<^sup>2 +1)) + ((z*(z+2)) / (2*z\<^sup>2 +1))
        =(((-1/2)*((-1/2)+2)) / (2*(-1/2)\<^sup>2+1)) + ((1*(1+2))/(2*1\<^sup>2+1)) + (((-1/2)*((-1/2)+2)) / (2*(-1/2)\<^sup>2+1)) "
        using assms
        by simp
  also have "... =  ( ((-1/2) * (((-1)+2*2)/2)) / (2* (1/4) + 1) )+ ( (1*3)/(2*1+1) ) + ( ((-1/2) * (((-1)+2*2)/2)) / (2* (1/4) + 1) ) "
         by (simp add: power_divide)
  also have "... = ( ((-1/2) * (3/2)) / (2* (1/4) + 1) )+ ( (1*3)/(2*1+1) ) + ( ((-1/2) * (3/2)) / (2* (1/4) + 1) ) "
         by auto
  also have "... = ( (-3/4) / (2/4 +1) )+ (3/(2+1)) + ( (-3/4) / (2/4 +1) )  "
        by simp
  also have "... = ( (-3/4)/ (6/4) )  + (3/3)+  ( (-3/4)/ (6/4) )"
        by simp
  also have "... = (-3/6) + 1 + (-3/6)"
        by simp
  also have "... = -1 + 1"
        by simp
  then have "... = 0"
        by simp
  then show ?thesis
        by (simp add: calculation)
qed

        
lemma resenje_jednacine_4[simp]:
fixes x y z :: real
assumes " (x,y,z) = (1, -1/2, -1/2)"
shows "((x*(x+2)) / (2*x\<^sup>2 +1)) +
      ((y*(y+2)) / (2*y\<^sup>2 +1)) +
      ((z*(z+2)) / (2*z\<^sup>2 +1)) = 0"       
proof- 
  have "((x*(x+2)) / (2*x\<^sup>2 +1)) + ((y*(y+2)) / (2*y\<^sup>2 +1)) + ((z*(z+2)) / (2*z\<^sup>2 +1))
        = ((1*(1+2))/(2*1\<^sup>2+1)) + (((-1/2)*((-1/2)+2)) / (2*(-1/2)\<^sup>2+1)) + (((-1/2)*((-1/2)+2)) / (2*(-1/2)\<^sup>2+1)) "
        using assms
        by simp
  also have "... = ( (1*3)/(2*1+1) ) + ( ((-1/2) * (((-1)+2*2)/2)) / (2* (1/4) + 1) ) + ( ((-1/2) * (((-1)+2*2)/2)) / (2* (1/4) + 1) ) "
         by (simp add: power_divide)
  also have "... =  ( (1*3)/(2*1+1) ) + ( ((-1/2) * (3/2)) / (2* (1/4) + 1) ) + ( ((-1/2) * (3/2)) / (2* (1/4) + 1) ) "
    by (simp add: Fields.field_class.add_frac_num)
  also have "... =(3/(2+1)) + ( (-3/4) / (2/4 +1) ) + ( (-3/4) / (2/4 +1) )  "
        by simp
  also have "... =(3/3)+ ( (-3/4)/ (6/4) ) +  ( (-3/4)/ (6/4) ) "
        by simp
  also have "... = 1 + (-3/6) + (-3/6)"
        by simp
  also have "... = 1 +(-1)"
        by simp
  then have "... = 0"
        by simp
  then show ?thesis
        by (simp add: calculation)
qed


lemma resenja_jednacine_objedinjeno_dokaz:
fixes x y z :: real
assumes "(x, y, z) = (0,0,0) \<or> (x,y,z) = (-1/2, -1/2, 1)
                             \<or> (x,y,z) = (-1/2, 1, -1/2)
                             \<or> (x,y,z) = (1, -1/2, -1/2)"
shows "((x*(x+2)) / (2*x\<^sup>2 +1)) +
      ((y*(y+2)) / (2*y\<^sup>2 +1)) +
      ((z*(z+2)) / (2*z\<^sup>2 +1)) = 0"    
      using assms resenje_jednacine_4 resenje_jednacine_3 resenje_jednacine_2 resenje_1_jednacina_dokaz
      by auto

end