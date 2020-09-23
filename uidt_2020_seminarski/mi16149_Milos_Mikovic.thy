theory mi16149_Milos_Mikovic

imports Complex_Main


(* Prvi seminarski rad 

  zadatak (3. razred A kategorija 4. zadatak) : https://imomath.com/srb/zadaci/2005_republicko.pdf
  resenje (46. strana pdf-a) : https://imomath.com/srb/zadaci/bilten2005.pdf
  
  Zadatak : Neka za pozitivne realne brojeve x i y vazi x^2 + y^3 \<ge> x^3 + y^4 ,
             dokazati da vazi x^3 + y^3 \<le> 2. 
 
  Resenje : Kako vazi y^2 + y^4 \<ge> 2*y^3 (dokazuje se lemom l1) koristeci uslov zadatka tj.
  x^2 + y^3 \<ge> x^3 + y^4 imamo da x^2 - x^3 \<ge> y^4 - y^3 \<ge> y^3 - y^2
  Takodje odavde imamo da vazi x^2 + y^2 \<ge> x^3 + y^3 koristeci prvi i poslednji deo gornje 
  nejednakosti (pokazano lemom l2). 
  Na kraju jos je potrebno dokazati da 2^(1/3)*(x^3+y^3)^(2/3) \<ge> x^2 + y^2 cime smo 
  dokazali teoremu (pokazujemo lemom l3).
  l1,l2,l3 treba objediniti i dokazati polazno tvrdjenje lemom "treci_razred_a_kategorija_4_zadatak"
 *)

begin



lemma l1:
  fixes y::real
  assumes "x \<ge> 0"
  assumes "y \<ge> 0"
  shows "y^(2) + y^(4) \<ge> 2*y^(3)"
  sorry



lemma l2:
  fixes x ::real and y::real
  assumes "y^(2) + y^(4) \<ge> 2*y^(3)"
  assumes "x^(2) + y^(3) \<ge> x^(3) + y^(4)"
  assumes "x \<ge> 0"
  assumes "y \<ge> 0"
  shows "x^2 + y^2 \<ge> x^3 + y^3"
  sorry


lemma l3:
  fixes x :: real and y :: real
  assumes "x \<ge> 0"
  assumes "y \<ge> 0"
  shows "(root 3 2) * (root 3 ((x^3 + y^3) ^ 2)) \<ge> x^(2) + y^(2)"
  sorry



(* Glavno tvrdjenje zadatka *)

lemma treci_razred_a_kategorija_4_zadatak:
  fixes x::real and y::real
  assumes "x^(2) + y^(3) \<ge> x^(3) + y^(4)"
  assumes "x \<ge> 0"
  assumes "y \<ge> 0"
  shows "x^(3) + y^(3) \<le> 2"
  sorry




end