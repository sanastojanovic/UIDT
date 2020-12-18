theory mi16138_Jelisaveta_Smiljanic
  imports Main Complex_Main
begin

(*
  Zadatak: https://imomath.com/srb/zadaci/RS_2017_republicko_resenja.pdf
  Prvi razred, zadatak 4

  Neka su a, b, c pozitivni brojevi takvi da je a * b * c \<le> 1. 
  Dokazati da je 1/a + 1/b + 1/c \<ge> 1 + 6/(a + b + c)

  Resenje: 
  Zapisujemo nejednakost u obliku: (1/a + 1/b + 1/c)*(a + b + c) \<ge> a + b + c + 6
  
  Na osnovu nejednakosti izmedju aritmeticke i geometrijske sredne:
  1/a + 1/b + 1/c \<ge> 3 / root 3 (a * b * c) \<ge> 3
  i  a + b + c \<ge> 3 * root 3 (a * b * c)
  
  Zbog toga je:
  1/3 * (1/a + 1/b + 1/c)*(a + b + c) \<ge> a + b + c
  i  2/3 * (1/a + 1/b + 1/c)*(a + b + c) \<ge> 2/3 * 3 / root 3(a * b * c)* 3 * root 3 (a * b * c) = 6

  Sabiranjem poslednje dve nejednakosti dobijamo:
  (1/a + 1/b + 1/c)*(a + b + c) \<ge> a + b + c + 6
*)


lemma pom2: 
  fixes a b c :: real
  assumes "a * b * c \<le> 1" "a > 0" "b > 0"  "c > 0"
  shows "3 / root 3 (a * b * c) \<ge> 3"
  sorry


lemma ag_nej_3:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0" 
  shows "root 3 (x * y * z) \<le> (x + y + z) / 3 "
  sorry

lemma pom1:
  fixes a b c :: real
  assumes "a * b * c \<le> 1" "a > 0" "b > 0"  "c > 0"
  shows "(1/a + 1/b + 1/c) \<ge> (3 / root 3 (a * b * c))"
  sorry

lemma leva_strana: 
  fixes a b c :: real
  assumes "a * b * c \<le> 1" "a > 0" "b > 0"  "c > 0"
  shows "1/3 * (1/a + 1/b + 1/c) * (a + b + c) \<ge> a + b + c"
  sorry

lemma d_pom:
  fixes a b c :: real
  assumes "a * b * c \<le> 1" "a > 0" "b > 0"  "c > 0"
  shows "(a + b + c) \<ge> 3 * root 3 (a * b * c)"
  sorry

lemma desna_strana: 
  fixes a b c :: real
  assumes "a * b * c \<le> 1" "a > 0" "b > 0"  "c > 0"
  shows "2/3 * (1/a + 1/b + 1/c) * (a + b + c) \<ge> 6"
  sorry

lemma glavna: 
  fixes a b c :: real
  assumes "a * b * c \<le> 1" "a > 0" "b > 0"  "c > 0"
  shows "(1/a + 1/b + 1/c) * (a + b + c) \<ge> a + b + c + 6"
  sorry

theorem
  fixes a b c :: real
  assumes "a * b * c \<le> 1" "a > 0" "b > 0"  "c > 0"
  shows "1/a + 1/b + 1/c \<ge> 1 + 6/(a + b + c)" 
  sorry

end
