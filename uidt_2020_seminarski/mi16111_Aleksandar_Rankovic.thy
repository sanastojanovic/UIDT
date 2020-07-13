theory mi16111_Aleksandar_Rankovic
  imports Complex_Main
begin

(*Link na zadatak:  https://imomath.com/srb/zadaci/BIH_2012_bihmo_resenja.pdf zadatak I-2 *)

(* zelimo da pokazemo da vazi ovo:
a ^ 3 / (b ^ 2 + c) + b ^ 3 / (c ^ 2 + a) + c ^ 3 / (a ^ 2 + b) \<ge> (root 3) / (1 + root 3)
za date uslove:
a > 0, b > 0, c > 0, a ^ 2 + b ^ 2 + c ^ 2 = 1  *)

(*Prvo ustanovimo na osnovu kosijeve nejednakosti *)
lemma kosi_nejednakost_1:
  fixes a b c ::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows "(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b))*(a ^ 3 / (b ^ 2 + c) + b ^ 3 / (c ^ 2 + a) + c ^ 3 / (a ^ 2 + b)) \<ge> (a ^ 2 + b ^ 2 + c ^ 2) ^ 2"
  sorry

(*kako je a^2 + b^2 + c^2)^2 = 1 iz toga i kosi_nejednakosti_1
 uz pomoc malo pretumbavanja postane jasno da nam je dovoljno da dokazemo: *)
lemma preformulisan_pocetak:
  fixes a b c ::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows "a*b^2 + b*c^2 + c*a^2 + a*c + b*a + c*b \<le> (1 / (root 2 3)) + 1"
  sorry

(* pokazimo da je *)
lemma zbir_manji_od_kvadrata:
  fixes a b c ::real
  shows "a*b + b*c + c*a \<le> a^2 + b^2 + c^2"
  sorry
(* koristeci  a^2 + b^2 + c^2 = 1 ostaje nam samo a*b^2 + b*c^2 + c*a^2 \<le>  (1 / (root 3)) *)

(* primenimo kosijevu nejednakost opet *)
lemma kosi_nejednakost_2:
  fixes a b c ::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows "a*b^2 + b*c^2 + c*a^2 \<le> root 2 (( a^2 + b^2 + c^2 )*( a^2*b^2 + b^2*c^2 + c^2*a^2 ))"
  sorry

(* koristeci  a^2 + b^2 + c^2 = 1 desna strana prethodne lemme postaje root ( a^2*b^2 + b^2*c^2 + c^2*a^2) *)
(* a*b^2 + b*c^2 + c*a^2 \<le>  root ( a^2*b^2 + b^2*c^2 + c^2*a^2 *)
(* pa je dovoljno pokazati root (a^2*b^2 + b^2*c^2 + c^2*a^2) \<le>  (1 / (root 3)) *)

lemma dovoljna:
  fixes a b c ::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows  "a^2*b^2 + b^2*c^2 + c^2*a^2 \<le>  (1 / 3)"
  sorry

(* a to je tacno zato sto vazi sledece tvrdjenje *)

lemma vredi_ovo:
  fixes a b c ::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows  "3*a^2*b^2 + 3*b^2*c^2 + 3*c^2*a^2 \<le> (a ^ 2 + b ^ 2 + c ^ 2) ^ 2"
  sorry

(* Nejednakost koju pokusavamo da dokazemo *)
lemma 
  fixes a b c::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows "a ^ 3 / (b ^ 2 + c) + b ^ 3 / (c ^ 2 + a) + c ^ 3 / (a ^ 2 + b) \<ge> (root 2 3) / (1 + root 2 3)"
  sorry


end