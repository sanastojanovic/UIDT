theory mi18470_Uros_Vucicevic
  imports Complex_Main "HOL-Library.Code_Target_Nat"
begin

text \<open> 
  https://imomath.com/srb/zadaci/2018_bmo_shortlist.pdf , zadatak A3
------------------------------------------------------------------      
  Pokazati da za svaki pozitivan int n važi :

             k
     (2n+1-k)    n
  \<Sum> (------) \<le> 2   , k \<in> {0..n}   
     ( k+1  )
------------------------------------------------------------------
  Ideja dokaza :
    
    - za svaki član sume pokažemo da je manji ili jednak binomnom 
      koeficijentu za odgovarajuće n i k
    
    - kada originalne članove sume zamenimo odgovarajućim binomnim
      koeficijentima, dobijemo sumu binomnih za koju znamo da je jednaka 
      2^n pa dokaz sledi direktno    

\<close>



(*  Definišemo faktorijel primitivnom rekurzijom  *)
primrec fact :: "nat \<Rightarrow> nat" where
   "fact 0 = 1"
|  "fact (Suc n) = fact n * (Suc n)"

value "fact 4"


(*  Definišemo binomni koeficijent za odgovarajuće n i k  *)
definition binom_koef :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "binom_koef n k = fact n div (fact k * fact (n-k))"

value "binom_koef 5 2" 

(*  Dokazujemo jednu od osobina binomnih koeficijenata  *)
lemma simetrija_binomnih [simp]:
  assumes "n \<ge> k"
  shows "binom_koef n k = binom_koef n (n-k)"
  using assms
  unfolding binom_koef_def
  by (simp add: mult.commute)

(*  Dokazujemo sumu binomnih koeficijenata  *)
lemma suma_binomnih [simp]:
  fixes n :: nat
  shows "\<forall>n.(\<Sum> k \<in> {0..n} . binom_koef n k) = 2^n"
  by simp
 
(*  Dokazujemo pomoćnu lemu, koja je srž dokaza glavne leme  *)
lemma pomocna_lema [simp]:
  shows "\<forall>k \<in> {0..n}. (binom_koef n k \<ge> ((2*n+1-k) / (k+1))^k)"
  by simp
  
(*  Dokazujemo glavnu lemu  *)
lemma glavna_lema:
  fixes n :: int
  assumes "n>0"
  shows "\<forall>n. (\<Sum> k \<in> {0..n}. ((2*n+1-k) / (k+1))^k ) \<le> 2^n"
  using assms
  using pomocna_lema
  by simp


text \<open>
  Isabelle može dokazati ovo i bez ikakvih dodatnih tvrđenja, formulisanjem
  glavne leme i pozivanjem automatskog dokazivača metis.

  lemma
    fixes n :: int
    assumes "n>0"
    shows "\<forall>n. (\<Sum> k \<in> {0..n}. ((2*n+1-k) / (k+1))^k ) \<le> 2^n"
    using assms
    by metis

\<close>

end