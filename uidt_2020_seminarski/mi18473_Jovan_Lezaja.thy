theory mi18473_Jovan_Lezaja
  imports Complex_Main

begin

text \<open>
URL ka zadatku: https://imomath.com/srb/zadaci/2014_imac.pdf
Drugi dan, zadatak 5:
  Dat je prost broj p. Prirodni brojevi m i n se u sistemu sa osnovom p zapisuju kao
      n = a_0 + a_1*p + ... + a_k*p^k i m = b_0 + b_1*p + ... + b_k*p^k.
  Dokazati da je 
      binomni_koeficijent(n, m) \<equiv> \<Prod> i \<leftarrow> [0..<(k+1)]. binomni_koeficijent(a_i, b_i) (mod p)
  
  (a \<equiv> b (mod p) predstavlja kongruenciju po modulu, pri čemu je a deljenik, b je ostatak, a c je modulo)
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

text\<open>
  Funkcija `u_osnovi` prima dva argumenta n i b, pri cemu je n broj koji zelimo da izrazimo u 
  drugoj osnovi, a b je osnova u kojoj izrazavamo nas broj n.
  Rezultat je lista elemenata tipa nat (tip koji odgovara skupu prirodnih brojeva) koja sadrži 
  cifre broja n izraženog u osnovi b. Redosled cifara je u obrnutom redosledu, no to ne predstavlja
  problem za formulaciju leme.
\<close>
fun u_osnovi :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "u_osnovi n b = (if b \<le> 1 then
                      []
                    else if n<b then
                      [(n mod b)]
                    else 
                      (n mod b) # (u_osnovi (n div b) b)
)"

text\<open>Pomoćna funkcija radi kraćeg zapisa leme\<close>
definition proizvod_binom_koef :: "(nat \<times> nat) list \<Rightarrow> nat" where
  "proizvod_binom_koef xs = foldl (*) 1 (map (\<lambda> (m,n). binom_koef m n) xs)"

text \<open> Postavka zadatka \<close>
lemma zadatak:
  fixes p m n :: nat
  assumes "prost p" "p>1"
  shows "(binom_koef m n) mod p = 
         proizvod_binom_koef (zip_sa_dopunom (u_osnovi m p) (u_osnovi n p))"
  sorry

text \<open> Drugi seminarski zadatak
      
       URL ka zadatku: https://www.imo-official.org/problems/IMO2011SL.pdf

       Tekst zadatka A7:
       Neka su a, b i c pozitivni realni brojevi koji zadovoljavaju uslove
       min{a+b, b+c, a+c} > sqrt(2) i a²+b²+c² = 3. Dokazati da važi sledeća
       nejednakost:

          a/(b+c-a)² + b/(c+a-b)² + c/(a+b-c)² >= 3/(a*b*c)²
     \<close>

text \<open> Naredne 3 leme predstavljaju pomoćne leme koje ćemo koristiti za dokazivanje 
       znaka \<close>

lemma kvadrat_koren:
  fixes a :: real
  assumes "a>0"
  shows "a = (root 2 a) ^ 2"
  using assms
  by simp

lemma pomocna_lema_1:
  fixes b c :: real
  assumes "b > 0" "c > 0"
  assumes "b + c > root 2 2"
  shows "b^2 + c^2 > 1"
  using assms
proof-
  have "root 2 2 < b + c" using assms(3) by simp
  hence "2 < (b+c)^2" using kvadrat_koren assms(1) assms(2)
    by (smt pos2 real_less_rsqrt real_root_pos_unique sqrt_def)
  also have "... = b^2 + c^2 + 2*b*c" by (auto simp add: power2_sum)
  also have "... \<le> b^2 + c^2 + b^2 + c^2" using kvadrat_koren
    by (smt sum_squares_bound)
  also have "... = 2*(b^2 + c^2)" by simp
  finally have "2 < 2*(b^2 + c^2)" by simp
  thus "1 < b^2 + c^2" by simp
qed

lemma pomocna_lema_2:
  fixes a b c :: real
  assumes "b > 0" "c > 0"
  assumes "b + c > root 2 2"
  assumes "a^2 + b^2 + c^2 = 3"
  shows "b+c-a > 0"
  using assms
proof-
  have 1:"b^2 + c^2 > 1" using pomocna_lema_1 assms(1-3) by simp
  have "a^2 = 3 - (b^2 + c^2)" using assms(4) by simp
  also have "... < 2" using 1 by simp
  finally have 2:"a < root 2 2" using real_less_rsqrt sqrt_def by auto
  thus "b+c-a > 0" using 2 assms(1-3) by simp
qed

abbreviation izraz1 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "izraz1 x y z \<equiv> (y*z)^2 - (x*(y+z-x))^2"

abbreviation izraz2 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "izraz2 x y z \<equiv> (x-y)*(x-z)"

abbreviation izraz3 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "izraz3 x y z \<equiv> y*z - x*(y+z-x)"

abbreviation izraz4 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "izraz4 x y z \<equiv> y*z + x*(y+z-x)"

lemma razlika_kvadrata[simp]:
  fixes x y :: real
  shows "(x+y)*(x-y) = x^2 - y^2"
proof-
  have "(x+y)*(x-y) = x*x - x*y + x*y - y*y"
    by (simp add: square_diff_square_factored)
  also have "... = x*x - y*y" by simp
  finally show ?thesis
    by (simp add: power2_eq_square)
qed

lemma jednakost_izraza_2_3 [simp]:
  fixes x y z :: real
  assumes "x\<ge>y" "y\<ge>z" "z\<ge>0"
  shows "izraz2 x y z = izraz3 x y z"
  using assms
proof-
  have "(x-y)*(x-z) = x*x - x*z - x*y + y*z"
    by (simp add: mult.commute right_diff_distrib')
  also have "... = y*z - x*(z-x) - x*y"
    by (simp add: right_diff_distrib')
  also have "... = y*z - x*(z-x+y)"
    by (simp add: linordered_field_class.sign_simps(36))
  finally show ?thesis by simp
qed

lemma izraz4_pozitivan [simp]:
  fixes x y z :: real
  assumes "x>0" "y>0" "z>0"
  assumes "x\<ge>y" "y\<ge>z"
  assumes "x+y-z>0" "y+z-x>0" "x+z-y>0"
  shows "izraz4 x y z > 0"
  using assms
proof-
  have "(y+z-x) > 0" using assms(7) by simp
  hence "x*(y+z-x) > 0" using assms(1) by simp
  thus ?thesis using assms(2-3)
    by (simp add: pos_add_strict) 
qed

lemma znak_izraza_3_i_4 [simp]:
  fixes x y z :: real
  assumes "x>0" "y>0" "z>0"
  assumes "x+y-z>0" "y+z-x>0" "x+z-y>0"
  assumes "x\<ge>y" "y\<ge>z"
  shows "sgn (izraz3 x y z) = sgn ((izraz3 x y z)*(izraz4 x y z))"
  using assms
proof (cases "sgn (izraz3 x y z) = -1")
  case True
  have "sgn (izraz4 x y z) = 1"
    using izraz4_pozitivan assms(5-8) by auto
  then have "sgn (izraz3 x y z) * sgn (izraz4 x y z) = -1"
    using True by auto
  from True this show ?thesis
    by (simp add: sgn_mult)
next
  case False
  then show ?thesis
  proof (cases "sgn (izraz3 x y z) = 1")
    case True
    have "sgn (izraz4 x y z) = 1"
      using izraz4_pozitivan assms(5-8) by auto
    then have "sgn (izraz3 x y z) * sgn (izraz4 x y z) = 1"
      using True by auto
    from True this show ?thesis
      by (simp add: sgn_mult)
  next
    case False
    then have *:"sgn (izraz3 x y z) = 0"
      using sgn_real_def[of "izraz3 x y z"] \<open>sgn (izraz3 x y z) \<noteq> -1\<close>
      by presburger
    have "sgn (izraz4 x y z) = 1"
      using izraz4_pozitivan assms(5-8) by auto
    then have "sgn (izraz3 x y z) * sgn (izraz4 x y z) = 0"
      using * by auto
    from * this show ?thesis
      by (simp add: sgn_mult)
  qed
qed

lemma jednakost_znaka_izraza_1_i_2 [simp]:
  fixes x y z :: real
  assumes "x>0" "y>0" "z>0"
  assumes "x\<ge>y" "y\<ge>z"
  assumes "x+y-z>0" "y+z-x>0" "x+z-y>0"
  shows "sgn (izraz1 x y z) = sgn (izraz2 x y z)"
  using assms
proof-
  have "sgn (izraz1 x y z) = sgn (izraz3 x y z)"
  proof-
    have "sgn (izraz1 x y z) = sgn ((izraz3 x y z) * (izraz4 x y z))"
      using razlika_kvadrata[of "y*z" "x*(y+z-x)"]
      by (simp add: mult.commute)
    thus ?thesis
      using znak_izraza_3_i_4 assms(1-8) by simp   
  qed
  thus ?thesis using jednakost_izraza_2_3 assms(3-5) by auto
qed

text \<open> Ova lema pokazuje da bez gubljenja opštosti možemo da pretpostavimo da je 
       a^5+b^5+c^5 >= 3 za dokazivanje date nejednakosti.
     \<close>
lemma
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  assumes "min_list [a+b, b+c, c+a] > root 2 2"
  assumes "a^2 + b^2 + c^2 = 3"
  assumes "a^5 + b^5 + c^5 \<ge> 3"
  shows "((a^5 + b^5 + c^5 \<ge> 3) \<longrightarrow> P) \<longrightarrow> ((a^2 + b^2 + c^2 = 3) \<longrightarrow> P)"
  using assms
  by auto

text \<open> Nejednakosti koje ćemo koristiti u narednoj lemi\<close>
abbreviation nejed_1 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "nejed_1 a b c \<equiv> a/(b+c-a)^2 + b/(c+a-b)^2 + c/(a+b-c)^2 \<ge> 3/(a*b*c)^2"

abbreviation nejed_2 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "nejed_2 a b c \<equiv> ((a^3*b^2*c^2)/(b+c-a)^2 + (a^2*b^3*c^2)/(c+a-b)^2 + (a^2*b^2*c^3)/(a+b-c)^2 
                       \<ge> a^5 + b^5 + c^5)"

abbreviation nejed_3 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "nejed_3 a b c \<equiv> ((a^3*b^2*c^2) - a^5*(b+c-a)^2)/(b+c-a)^2 +
        ((a^2*b^3*c^2) - b^5*(c+a-b)^2)/(c+a-b)^2 + 
        ((a^2*b^2*c^3) - c^5*(a+b-c)^2)/(a+b-c)^2   >= 0"

text \<open> Ova lema pokazuje da je za dokazivanje početne nejednakosti dovoljno dokazati sledeću 
       nejednakost:

          (a³*b²*c²)/(b+c-a)² + (b³*a²*c²)/(c+a-b)² + (c³*b²*a²)/(a+b-c)² \<ge> a^5 + b^5 + c^5
     \<close>
lemma pomocna:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "min_list [a+b, b+c, c+a] > root 2 2"
  assumes "a^2 + b^2 + c^2 = 3"
  assumes "a^5 + b^5 + c^5 \<ge> 3"
  shows "(nejed_2 a b c) \<longrightarrow> (nejed_1 a b c)"
  using assms
proof-
  have "(a*b*c)^2 > 0" using assms by simp
  hence "nejed_1 a b c \<equiv> (a*b*c)^2*(a/(b+c-a)^2 + b/(c+a-b)^2 + c/(a+b-c)^2) \<ge> 3"
    using assms(1-3)
    by (simp add: divide_le_eq mult.commute)
  also have "... \<equiv> ((a*b*c)^2*a)/(b+c-a)^2 + ((a*b*c)^2*b)/(c+a-b)^2 + ((a*b*c)^2*c)/(a+b-c)^2 \<ge> 3"
    by (simp add: distrib_left)
  also have "... \<equiv> ((a^2*b^2*c^2)*a)/(b+c-a)^2 + ((a^2*b^2*c^2)*b)/(c+a-b)^2 + ((a^2*b^2*c^2)*c)/(a+b-c)^2 \<ge> 3"
    by (simp add: power_mult_distrib)
  also have "... \<equiv> (a^3*b^2*c^2)/(b+c-a)^2 + (a^2*b^3*c^2)/(c+a-b)^2 + (a^2*b^2*c^3)/(a+b-c)^2 \<ge> 3"
    by (smt mult.assoc mult.commute power3_eq_cube semiring_normalization_rules(29))
  finally have 1:"nejed_1 a b c \<equiv> (a^3*b^2*c^2)/(b+c-a)^2 + (a^2*b^3*c^2)/(c+a-b)^2 + (a^2*b^2*c^3)/(a+b-c)^2 \<ge> 3"
    .
  thus ?thesis using assms(6)
    by auto
qed

text\<open> Bez gubljenja opstosti pored vec zadatih uslova
      mozemo da pretpostavimo da zbog simetrije vazi a >= b >= c.
      
      Ono sto treba da se dokaze sada mozemo da izrazimo i ovako

        (a³*b²*c²)/(b+c-a)² + (b³*a²*c²)/(c+a-b)² + (c³*b²*a²)/(a+b-c)² \<ge> a^5 + b^5 + c^5-
    \<close>

lemma
  fixes a b c :: real
  assumes "b\<noteq>0"
  shows "c+ c + a \<ge> 0 \<equiv> c + c + a*(b/b) \<ge> 0"
  by (simp add: assms)

lemma 
  fixes a b c d :: real
  assumes "a>0" "b>0" "c>0"
  shows "a^2*d/b - c/b = (a^2*d-c)/b"
  using assms
  by (simp add: diff_divide_distrib)

lemma 
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "min_list [a+b, b+c, c+a] > root 2 2"
  assumes "a^2 + b^2 + c^2 = 3"
  shows "nejed_2 a b c \<equiv> nejed_3 a b c"
  using assms
proof-
  have 1: "(b+a-c)^2 > 0" using pomocna_lema_2[of a b c] assms by simp
  have 2: "(b+c-a)^2 > 0" using pomocna_lema_2[of b c a]  assms by simp
  have 3: "(c+a-b)^2 > 0" using pomocna_lema_2[of c a b]  assms by simp
  have "nejed_2 a b c \<equiv> (a^3*b^2*c^2)/(b+c-a)^2 + (a^2*b^3*c^2)/(c+a-b)^2 + (a^2*b^2*c^3)/(a+b-c)^2
                         - a^5 - b^5 - c^5 \<ge> 0"
    by linarith
  also have "... \<equiv> (a^3*b^2*c^2)/(b+c-a)^2 + (a^2*b^3*c^2)/(c+a-b)^2 + (a^2*b^2*c^3)/(a+b-c)^2
                    - a^5*(b+c-a)^2/(b+c-a)^2 - b^5*(c+a-b)^2/(c+a-b)^2 - c^5*(a+b-c)^2/(a+b-c)^2 \<ge> 0"
    using 1 2 3 assms by simp
  also have "... \<equiv> (a^3*b^2*c^2)/(b+c-a)^2 - a^5*(b+c-a)^2/(b+c-a)^2
                 + (a^2*b^3*c^2)/(c+a-b)^2 - b^5*(c+a-b)^2/(c+a-b)^2
                 + (a^2*b^2*c^3)/(a+b-c)^2 - c^5*(a+b-c)^2/(a+b-c)^2 \<ge> 0"
    by linarith
  also have "... \<equiv> (a^3*b^2*c^2 - a^5*(b+c-a)^2)/(b+c-a)^2
                 + (a^2*b^3*c^2)/(c+a-b)^2 - b^5*(c+a-b)^2/(c+a-b)^2
                 + (a^2*b^2*c^3)/(a+b-c)^2 - c^5*(a+b-c)^2/(a+b-c)^2 \<ge> 0"
    by (simp add: diff_divide_distrib)
  also have "... \<equiv> (a^3*b^2*c^2 - a^5*(b+c-a)^2)/(b+c-a)^2
                 + (a^2*b^3*c^2)/(c+a-b)^2 - (b^5*(c+a-b)^2)/(c+a-b)^2
                 + (a^2*b^2*c^3- c^5*(a+b-c)^2)/(a+b-c)^2 \<ge> 0"
    sorry
qed

lemma glavna:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "min_list [a+b, b+c, c+a] > root 2 2"
  assumes "a^2 + b^2 + c^2 = 3"
  assumes "a^5 + b^5 + c^5 \<ge> 3"
  shows "a/(b+c-a)^2 + b/(c+a-b)^2 + c/(a+b-c)^2 >= 3/(a*b*c)^2"
  using assms
proof-
  have 1:"b+c-a > 0" using pomocna_lema_2 assms by simp
  have 2:"c+a-b > 0" using pomocna_lema_2 assms by simp
  have 3:"a+b-c > 0" using pomocna_lema_2 assms by simp
  show ?thesis sorry
qed

end