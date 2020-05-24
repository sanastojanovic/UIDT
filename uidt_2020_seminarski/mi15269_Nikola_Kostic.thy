theory mi15269_Nikola_Kostic
  imports Complex_Main
begin

text \<open>
Zadatak 3, cetvrti razred 
Link: https://imomath.com/srb/zadaci/RS_2016_republicko_resenja.pdf
Tekst zadatka:
Ako su m i n prirodni brojevi za koje vazi 7m^2 + 7m + 8 =n^2,
dokazati da je broj n/5 + 1 jednak zbiru kvadrata dva uzastopna prirodna broja.
\<close>

fun vrednost_izraza :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"vrednost_izraza m n =  n^2 - 7*m^2 + 7*m + 8"

value "vrednost_izraza 2 1"

lemma 
  fixes m n :: nat
  shows"7*(4*m^2+4*m+1)+25 = 4*n^2"
  sorry

lemma 
  fixes m n :: nat
  shows "7*(2*m+1)^2= 4*n^2-25"
  sorry

lemma 
  fixes m n :: nat
  shows "7*(2*m+1)^2= (2*n-5)*(2*n+5)"
  sorry

(* NZD za (2n-5, 2n+5) *)
lemma gcd_math1:
  fixes n :: nat
  shows "gcd (2*n-5) (2*n+5) = d"
  sorry

(* Uzajamno prosti *)
lemma prost:
  fixes a b :: nat
  shows "gcd a b = 1"
  sorry
 
(* Za cele neparne brojeve a i b *)
lemma d_1:
  fixes a b n :: int
  assumes "a mod 2 = 1" "b mod 2 = 1"
  shows "2*n - 5 = 7*a^2" "2*n + 5 = b^2"
  using assms
  sorry

(* Za neparne brojeve a i b *)
lemma d_2:
  fixes a b n :: int
  assumes "a mod 2 = 1" "b mod 2 = 1"
  shows "2*n - 5 = a^2" "2*n + 5 = 7*b^2"
  using assms
  sorry

(* Za cele neparne i uzajamno proste a i b *)
lemma d_3:
  fixes a b n :: int 
  assumes "a mod 2 = 1" "b mod 2 = 1" "prost"
  shows "2*n-5 = 5*a^2" "2*n-5 = 5*7*b^2"
  using assms
  sorry

(* Za neparne prirodne brojeve a i b *)
lemma d_4:
  fixes a b n :: nat
  assumes "a mod 2 = 1" "b mod 2 = 1"
  shows "2*n - 5 = 5*7*a^2" "2*n + 5 = 5*b^2"
  using assms
  sorry

(* Resenje koje trazimo *)
lemma 
  fixes n k :: nat
  assumes "n = d_4 "
  shows "n/5 + 1 = k^2 + (k + 1)^2"
  sorry

end