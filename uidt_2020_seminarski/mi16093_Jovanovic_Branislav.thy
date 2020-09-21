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
 (* Prvi deo dokaza *)

(* Niz pomocnih lema za dokazivanje da je, kada prebacimo sve
na jednu stranu, S = a^3 + a*b^2 + b^2 + b − 2*a^2*b − a^2 zapravo
jednako (a^2 - a*b - b)*(a - b - 1) *)

(*Leme p_1, p_2, p_3 dokazuju redom svaki deo proizvoda sa (a - b - 1)*)

lemma p_1:
  fixes a b :: nat
  assumes "a > b"
  shows "a^3 - (a^2)*b-a^2 = a^2*(a - b -1)"
  by (simp add: power3_eq_cube right_diff_distrib' semiring_normalization_rules(29))

lemma p_2:
  fixes a b :: nat
  assumes "a > b"
  shows "(a^2)*b - a*(b^2) - a*b = a*b*(a - b -1)"
  by (simp add: diff_mult_distrib2 power2_eq_square semiring_normalization_rules(16))

lemma p_3:
  fixes a b :: nat
  assumes "a > b"
  shows "a*b - b^2 - b = b*(a - b -1)"
  by (simp add: diff_mult_distrib2 mult.commute semiring_normalization_rules(29))


(*Pomocna lema za medjukorak*)

lemma medjukorak_2_pomocna:
  fixes a b :: nat
  assumes "a > b"
  shows "a^2*(a - b -1) - a*b*(a - b - 1) - b*(a-b-1) = (a^2 - a*b - b) * (a -b -1)"
  using diff_mult_distrib by presburger

(*Leme koje dokazuju medjukorak izmedju 
a^3 - a^2*b - a^2 - a^2*b + a*b^2 + a*b - a*b + b^2 + b
i (a^2 - a*b - b) * (a -b -1)  *)


lemma medjukorak_1:
  fixes a b :: nat
  assumes "a>b"
  shows "a^3 + a*(b^2) + b^2 + b - 2*(a^2)*b - a^2 = (a^3 - (a^2)*b-a^2)-((a^2)*b - a*(b^2) - a*b) - (a*b - b^2 - b)"
proof-
  have "a^3 + a*(b^2) + b^2 + b - 2*(a^2)*b - a^2 = a^3 + a*(b^2) + b^2 + b - (a^2)*b -(a^2)*b - a^2" by auto
  also have "... = a^3 + a*(b^2) + b^2 + b - (a^2)*b - (a^2)*b - a^2 + a*b - a*b" by auto
  
  qed

lemma medjukorak_2:
  fixes a b :: nat
  assumes "a > b" p_1 p_2 p_3 medjukorak_2_pomocna
  shows  "(a^3 - (a^2)*b-a^2)-((a^2)*b - a*(b^2) - a*b) - (a*b - b^2 - b) = (a^2 - a*b -b) * (a -b -1)"
  
proof-
  have "(a^3 - (a^2)*b-a^2)-((a^2)*b - a*(b^2) - a*b) - (a*b - b^2 - b) = a^2*(a - b -1) - a*b*(a - b - 1) - b*(a-b-1)"
    using assms(1) p_1 p_2 p_3 by auto

  also have "... = (a^2 - a*b -b) * (a -b -1)"
    using assms(1) medjukorak_2_pomocna by blast

  finally show ?thesis by blast
  
qed


(*Drugi deo dokaza gde dokazujemo S≥0*)

(*Lema koja iz a>b, gde su a i b prirodni brojevi
dokazuje da je drugi clan proizvoda a - b -1 ≥0*)

lemma s_2:
  fixes a b :: nat
  assumes "a > b"
  shows "a - b - 1 ≥ 0"
  by blast

(*Pomocna lema pri dokazu da je prvi clan proizvoda S
(a^2 - a*b - b) veci od 0*)
lemma s_1_1:
  fixes a b :: nat 
  assumes "a>b"
  shows "a^2 - a*b - b = a*(a-b) - b "
  by (simp add: diff_mult_distrib2 semiring_normalization_rules(29))

lemma s_1_2:
  fixes a b :: nat
  assumes "a >b"
  shows "a*(a-b) - b ≥ a - b"
  by (simp add: Suc_leI assms diff_le_mono)

lemma s_1_3:
  fixes a b :: nat
  assumes "a > b"
  shows "a^2 - a*b - b ≥ a - b " 
  using assms s_1_1 s_1_2 by auto

lemma s_1_4:
  fixes a b :: nat 
  assumes "a > b" 
  shows "a - b > 0"
  using assms by simp

(*Zadatak*)
lemma zadatak:
  fixes a b :: nat
  assumes "a > b" 
  shows "a^3 + a*(b^2) + b^2 + b ≥ 2*(a^2)*b + a^2"
  sorry

end
