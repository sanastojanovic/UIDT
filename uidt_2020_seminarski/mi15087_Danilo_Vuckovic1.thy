theory mi15087_Danilo_Vuckovic1
  imports Complex_Main
begin

text \<open>
Zadatak 3, treci razred 
Link: https://imomath.com/srb/zadaci/RS_2016_republicko_resenja.pdf
Tekst zadatka:
Ako su m i n prirodni brojevi za koje vazi 7m^2 + 7m + 8 =n^2,
dokazati da je broj n/5 + 1 jednak zbiru kvadrata dva uzastopna prirodna broja.
\<close>

fun izraz1 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"izraz1 m n =  n^2 - 7*m^2 + 7*m + 8"

value "izraz1 2 1"

text \<open>
Posle mnozenja obe strane sa 4.
\<close>


lemma prva:
  fixes m n :: nat
  shows"7*(4*m^2+4*m+1)+25 = 4*n^2"
  sorry

lemma druga:
  fixes m n :: nat
  shows "7*(2*m+1)^2= 4*n^2-25"
  sorry

lemma treca:
  fixes m n :: nat
  shows "7*(2*m+1)^2= (2*n-5)*(2*n+5)"
  sorry

text \<open>
  NZD za (2n-5, 2n+5) = d
\<close>
lemma gcd_fja:
  fixes n :: nat
  shows "gcd (2*n-5) (2*n+5) = d"
  sorry


text \<open>
  za uzajamno proste brojeve
\<close>
lemma prost:
  fixes a b :: nat
  shows "gcd a b = 1"
  sorry

text \<open>
 Za cele neparne brojeve a i b
\<close>
lemma prvi_slucaj:
  fixes a b n :: int
  assumes "a mod 2 = 1" "b mod 2 = 1"
  shows "2*n - 5 = 7*a^2" "2*n + 5 = b^2"
  using assms
  sorry

text \<open>
  Za neparne brojeve a i b
\<close>
lemma drugi_slucaj:
  fixes a b n :: int
  assumes "a mod 2 = 1" "b mod 2 = 1"
  shows "2*n - 5 = a^2" "2*n + 5 = 7*b^2"
  using assms
  sorry

text \<open>
  Za cele neparne i uzajamno proste a i b
\<close>
lemma treci_slucaj:
  fixes a b n :: int 
  assumes "a mod 2 = 1" "b mod 2 = 1" "prost"
  shows "2*n-5 = 5*a^2" "2*n-5 = 5*7*b^2"
  using assms
  sorry

text \<open>
   Za neparne prirodne brojeve a i b
\<close>
lemma cetvrti_slucaj:
  fixes a b n :: nat
  assumes "a mod 2 = 1" "b mod 2 = 1" 
  shows "2*n - 5 = 5*7*a^2" "2*n + 5 = 5*b^2"
  using assms
  sorry


text \<open>
   Resenje
\<close>
lemma 
  fixes n k :: nat
  assumes "n = d_4 "
  shows "n/5 + 1 = k^2 + (k + 1)^2"
  sorry

end