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
  "binom_koef n k = foldl (\<lambda> z i. z * (n+1-i) div i) 1 [1..<(k+1)]"

text\<open>Funkcija koja proverava da li je broj prost.\<close>
definition prost :: "nat \<Rightarrow> bool" where
  "prost n = foldl (\<and>) True (map (\<lambda> x. (n mod x) \<noteq> 0) [2..<(n div 2 + 1)])"

text\<open>Funkcija zip_sa_dopunom za dve zadate liste xs i ys vraca listu uredjenih parova (x,y), 
gde je x\<in>xs, y\<in>ys, pri cemu dodatno u listu dodaje uredjene parove (0,y), odnosno (x,0), ukoliko je
xs kraća od ys, odnosno ys kraća od xs.
\<close>
fun zip_sa_dopunom :: "nat list \<Rightarrow> nat list \<Rightarrow> (nat \<times> nat) list" where
  "zip_sa_dopunom [] [] = []"
| "zip_sa_dopunom [] (y#ys) = [(0,y)] @ zip_sa_dopunom [] ys"
| "zip_sa_dopunom (x#xs) [] = [(x,0)] @ zip_sa_dopunom xs []"
| "zip_sa_dopunom (x#xs) (y#ys) = (x,y) # zip_sa_dopunom xs ys"

value "zip_sa_dopunom [1,2,3,6,6] [1,2,3,4]"

text\<open>
  Funkcija `u_osnovi` prima dva argumenta n i b, pri cemu je n broj koji zelimo da izrazimo u 
  drugoj osnovi, a b je osnova u kojoj izrazavamo nas broj n.
  Rezultat je lista elemenata tipa nat (tip koji odgovara skupu prirodnih brojeva) koja sadrži 
  cifre broja n izraženog u osnovi b. Redosled cifara je u obrnutom redosledu, no to ne predstavlja
  problem za formulaciju leme.
\<close>
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
  by (relation "measure (\<lambda> (n, b). n)") auto

text\<open>Pomoćna funkcija radi kraćeg zapisa leme\<close>
definition proizvod_binom_koef :: "(nat \<times> nat) list \<Rightarrow> nat" where
  "proizvod_binom_koef xs = foldl (*) 1 (map (\<lambda> (m,n). binom_koef m n) xs)"

lemma zadatak:
  fixes p m n :: nat
  assumes "prost p" "p>1"
  shows "(binom_koef m n) mod p = 
         proizvod_binom_koef (zip_sa_dopunom (u_osnovi m p) (u_osnovi n p))"
  sorry

end