theory mi18473_Jovan_Lezaja
  imports Main

begin

text \<open>
URL ka zadatku: https://imomath.com/srb/zadaci/2014_imac.pdf
Drugi dan, zadatak 5:
  Dat je prost broj p. Prirodni brojevi m i n se u sistemu sa osnovom p zapisuju kao
      n = a_0 + a_1*p + ... + a_k*p^k i m = b_0 + b_1*p + ... + b_k*p^k.
  Dokazati da je 
      binomni_koeficijent(n, m) \<equiv> \<Prod> i \<leftarrow> [0..<(k+1)]. binomni_koeficijent(a_i, b_i) (mod p)
  
  (a \<equiv> b (mod p) predstavlja kongruenciju po modulu, pri čemu je a ostatak, b je deljenik, a c je modulo)
\<close>

text\<open>
Za početak bi valjalo definisati funkciju koja izračunava binomni koeficijent.
Upotrebljena je formula za izračunavanje binomnnog koeficijenta korišćenjem proizvoda:
    C(n,k)=\<Prod> i\<leftarrow>[1..<(k+1)]. (n+1-i) / i
Funkcija bi mogla i rekurzivno da se definiše, korišćenjem rekurzivne formule za binomni koeficijent:
    C(n,0)=C(n,n)=1;
    C(n,k)=C(n-1,k-1) + C(n-1,k).
\<close>

definition binom_koef :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "binom_koef n k = foldl (\<lambda> z i. z * (n-i+1) div i) 1 [1..<(k+1)]"

text\<open>Funkcija koja proverava da li je broj prost.\<close>
definition prost :: "nat \<Rightarrow> bool" where
  "prost n = foldl (\<and>) True (map (\<lambda> x. (n mod x) \<noteq> 0) [2..<(n div 2)])"

value "binom_koef 5 4"

text\<open>Pomocna lema koja se koristi za dokaz zaustavljanja funkcije `u_osnovi`.\<close>
(*
TODO: zavrsiti dokaz 
      dokazivanje induktivnog koraka
*)
lemma div_div_lt_div:
  fixes n b :: nat
  assumes "n\<ge>b" "b>1"
  shows"n div b div b < n div b"
  using assms
proof (induction n rule: nat_induct_at_least)
  case base
  then have "b div b div b = 1 div b"
    by simp
  also have "... = 0"
    using \<open>b > 1\<close>
    by simp
  also have "... < 1"
    by simp
  also have "... = b div b"
    using \<open>b > 1\<close>
    by simp
  finally show ?case 
    .
next
  case (Suc n)
  then show ?case sorry
qed

text\<open>
  Funkcija `u_osnovi` prima dva argumenta n i b, pri cemu je n broj koji zelimo da izrazimo u 
  drugoj osnovi, a b je osnova u kojoj izrazavamo nas broj n.
  Rezultat je lista elemenata tipa nat (tip koji odgovara skupu prirodnih brojeva) koja sadrži 
  cifre broja n izraženog u osnovi b.
\<close>
(* TODO: dokaz nije zavrsen, treba dokazati lemu div_div_lt_div *)
function u_osnovi :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "u_osnovi n b = (if b \<le> 1 then
                      []
                    else if n<b then
                      [(n mod b)]
                    else 
                      (n mod b) # (u_osnovi (n div b) b)
)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda> (n,b). n div b)") (auto simp add: div_div_lt_div)

end