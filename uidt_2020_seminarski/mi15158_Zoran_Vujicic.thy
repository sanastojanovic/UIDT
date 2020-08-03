theory mi15158_Zoran_Vujicic
  imports Complex_Main
begin
                          
text \<open>
Prvi seminarski 
III razred - A, zadatak 5
Link zadatka  https://imomath.com/srb/zadaci/2019_okruzno.pdf
\<close>

(* Treba da dokazemo nejednakost: 
root 2 ((a + 2*b + 3*c) / (3*a + 2*b + c)) + root 2 ((b + 2*c + 3*a) / (3*b + 2c + a)) + root 2 ((c + 2*a + 3*b) / (3*c + 2*a + b)) \<ge> 3
uz sledece uslove:
a > 0, b > 0, c > 0 *)

(* Primenimo nejednakost izmedju aritmeticke i geometrijske sredine na root 2 ((a + 2*b + 3*c) / (3*a + 2*b + c)) *)
lemma aritmeticka_geometrijska_I:
  fixes a :: real
  fixes b :: real
  fixes c :: real
  assumes "a > 0" "b > 0" "c > 0"
  shows "(a + 2*b + 3*c) / (root 2 ((a + 2*b + 3*c)*(3*a + 2*b + c))) \<ge> (2*(a + 2*b + 3*c)) / ((a + 2*b + 3*c) + (3*a + 2*b + c))"
  sorry

(* Sredjivanjem desne strane nejednakosti  2*(a + 2*b + 3*c) / ((a + 2*b + 3*c) + (3*a + 2*b + c)) dobijemo (2*a + 4*b + 6*c) / (4*(a + b + c)) *)

(* Analogno prethodnom, opet primenimo nejednakost izmedju aritmeticke i geometrijske sredine na root 2 ((b + 2*c + 3*a) / (3*b + 2c + a)) *)
lemma aritmeticka_geometrijska_II:
  fixes a :: real
  fixes b :: real
  fixes c :: real
  assumes "a > 0" "b > 0" "c > 0"
  shows "(b + 2*c + 3*a) / (root 2 ((b + 2*c + 3*a)*(3*b + 2*c + a))) \<ge> (2*(b + 2*c + 3*a)) / ((b + 2*c + 3*a) + (3*b + 2*c + a))"
  sorry

(* Sredjivanjem desne strane nejednakosti (2*(b + 2*c + 3*a)) / ((b + 2*c + 3*a) + (3*b + 2*c + a)) dobijemo (2*b + 4*c + 6*a) / (4*(a + b + c)) *)

(* Analogno prethodnom, opet primenimo nejednakost izmedju aritmeticke i geometrijske sredine na root 2 ((c + 2*a + 3*b) / (3*c + 2*a + b)) *)
lemma aritmeticka_geometrijska_III:
  fixes a :: real
  fixes b :: real
  fixes c :: real
  assumes "a > 0" "b > 0" "c > 0"
  shows "(c + 2*a + 3*b) / (root 2 ((c + 2*a + 3*b)*(3*c + 2*a + b))) \<ge> (2*(c + 2*a + 3*b)) / ((c + 2*a + 3*b) + (3*c + 2*a + b))"
  sorry

(* Sredjivanjem desne strane nejednakosti (2*(c + 2*a + 3*b)) / ((c + 2*a + 3*b) + (3*c + 2*a + b)) dobijemo (2*c + 4*a + 6*b) / (4*(a + b + c)) *)

(* Saberemo leve strane nejednakosti a zatim i desne strane nejednakosti *)
lemma saberi:
  fixes a :: real
  fixes b :: real
  fixes c :: real
  assumes "a > 0" "b > 0" "c > 0"
  shows "root 2 ((a + 2*b + 3*c) / (3*a + 2*b + c)) + root 2 ((b + 2*c + 3*a) / (3*b + 2*c + a)) + root 2 ((c + 2*a + 3*b) / (3*c + 2*a + b)) \<ge> (2*a + 4*b + 6*c) / (4*(a + b + c)) + (2*b + 4*c + 6*a) / (4*(a + b + c)) + (2*c + 4*a + 6*b) / (4*(a + b + c))"
  sorry

(* Sredjivanjem desne strane nejednakosti (2*a + 4*b + 6*c) / (4*(a + b + c)) + (2*b + 4*c + 6*a) / (4*(a + b + c)) + (2*c + 4*a + 6*b) / (4*(a + b + c)) dobijemo da je jednaka 3, a to je ono sto smo trbali dokazati *)

(* Nejednakost koju dokazujemo: *)
lemma 
  fixes a :: real
  fixes b :: real
  fixes c :: real
  assumes "a > 0" "b > 0" "c > 0"
  shows "root 2 ((a + 2*b + 3*c) / (3*a + 2*b + c)) + root 2 ((b + 2*c + 3*a) / (3*b + 2*c + a)) + root 2 ((c + 2*a + 3*b) / (3*c + 2*a + b)) \<ge> 3"
  sorry

end