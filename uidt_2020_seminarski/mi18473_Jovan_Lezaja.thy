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

abbreviation izraz_1 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "izraz_1 x y z \<equiv> (y*z)^2 - (x*(y+z-x))^2"

abbreviation izraz_2 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "izraz_2 x y z \<equiv> (x-y)*(x-z)"

abbreviation izraz_3 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "izraz_3 x y z \<equiv> y*z - x*(y+z-x)"

abbreviation izraz_4 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "izraz_4 x y z \<equiv> y*z + x*(y+z-x)"

abbreviation izraz_5 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "izraz_5 x y z \<equiv> (x-y)*(x-z)*(y*z + x*(y+z-x))"

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
  shows "izraz_2 x y z = izraz_3 x y z"
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

lemma izraz_4_pozitivan [simp]:
  fixes x y z :: real
  assumes "x>0" "y>0" "z>0"
  assumes "x\<ge>y" "y\<ge>z"
  assumes "x+y-z>0" "y+z-x>0" "x+z-y>0"
  shows "izraz_4 x y z > 0"
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
  shows "sgn (izraz_3 x y z) = sgn ((izraz_3 x y z)*(izraz_4 x y z))"
  using assms
proof (cases "sgn (izraz_3 x y z) = -1")
  case True
  have "sgn (izraz_4 x y z) = 1"
    using izraz_4_pozitivan assms(5-8) by auto
  then have "sgn (izraz_3 x y z) * sgn (izraz_4 x y z) = -1"
    using True by auto
  from True this show ?thesis
    by (simp add: sgn_mult)
next
  case False
  then show ?thesis
  proof (cases "sgn (izraz_3 x y z) = 1")
    case True
    have "sgn (izraz_4 x y z) = 1"
      using izraz_4_pozitivan assms(5-8) by auto
    then have "sgn (izraz_3 x y z) * sgn (izraz_4 x y z) = 1"
      using True by auto
    from True this show ?thesis
      by (simp add: sgn_mult)
  next
    case False
    then have *:"sgn (izraz_3 x y z) = 0"
      using sgn_real_def[of "izraz_3 x y z"] \<open>sgn (izraz_3 x y z) \<noteq> -1\<close>
      by presburger
    have "sgn (izraz_4 x y z) = 1"
      using izraz_4_pozitivan assms(5-8) by auto
    then have "sgn (izraz_3 x y z) * sgn (izraz_4 x y z) = 0"
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
  shows "sgn (izraz_1 x y z) = sgn (izraz_2 x y z)"
  using assms
proof-
  have "sgn (izraz_1 x y z) = sgn (izraz_3 x y z)"
  proof-
    have "sgn (izraz_1 x y z) = sgn ((izraz_3 x y z) * (izraz_4 x y z))"
      using razlika_kvadrata[of "y*z" "x*(y+z-x)"]
      by (simp add: mult.commute)
    thus ?thesis
      using znak_izraza_3_i_4 assms(1-8) by simp   
  qed
  thus ?thesis using jednakost_izraza_2_3 assms(3-5) by auto
qed

lemma jednakost_izraza_1_i_5 [simp]:
  fixes x y z :: real
  assumes "x>0" "y>0" "z>0"
  assumes "x\<ge>y" "y\<ge>z"
  assumes "x+y-z>0" "y+z-x>0" "x+z-y>0"
  shows "izraz_1 x y z = izraz_5 x y z"
  using assms
proof-
  have "izraz_1 x y z = (izraz_3 x y z) * (izraz_4 x y z)"
    using assms by (metis mult.commute razlika_kvadrata)
  also have "... = (izraz_2 x y z) * (izraz_4 x y z)"
    using assms by simp
  also have "... = izraz_5 x y z" by simp
  finally show ?thesis 
    using assms
    using \<open>izraz_1 x y z = izraz_3 x y z * izraz_4 x y z\<close>
          \<open>izraz_3 x y z * izraz_4 x y z = izraz_5 x y z\<close> by linarith
qed

lemma [simp]:
  fixes x y z :: real
  assumes "x>0" "y>0" "z>0"
  assumes "x\<ge>y" "y\<ge>z"
  assumes "x+y-z>0" "y+z-x>0" "x+z-y>0"
  shows "(izraz_2 x y z)*(izraz_4 x y z) = izraz_5 x y z"
  by auto

lemma jednakost_izraz_1_i_24 [simp]:
  fixes x y z :: real
  assumes "x>0" "y>0" "z>0"
  assumes "x\<ge>y" "y\<ge>z"
  assumes "x+y-z>0" "y+z-x>0" "x+z-y>0"
  shows "izraz_1 x y z = (izraz_2 x y z)*(izraz_4 x y z)"
  using assms
  by simp

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
  "nejed_3 a b c \<equiv> (c^3 * ((a*b)^2 - (c*(a+b-c))^2))/(a+b-c)^2
                 + (b^3 * ((c*a)^2 - (b*(c+a-b))^2))/(c+a-b)^2
                 + (a^3 * ((b*c)^2 - (a*(b+c-a))^2))/(b+c-a)^2 \<ge> 0"

abbreviation nejed_4 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "nejed_4 a b c \<equiv> a^3*(a-b)*(a-c)*(b*c + a*(b+c-a))/(b+c-a)^2 
                 \<ge> b^3*(b-c)*(a-b)*(c*a + b*(c+a-b))/(c+a-b)^2"

abbreviation nejed_5 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "nejed_5 a b c \<equiv> (a*b + a*c + b*c - a^2)/(b+c-a) \<ge> (b*a + b*c + a*c - b^2)/(c+a-b)"

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
  have "(a*b*c)^2 > 0" using assms(1-3) by simp
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

lemma [simp]:
  fixes a b c d :: real
  shows "a*b + a*c*d = a*(b+c*d)"
  by (simp add: linordered_field_class.sign_simps(18))

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
  also have "... \<equiv> (a^2*b^3*c^2)/(c+a-b)^2 - b^5*(c+a-b)^2/(c+a-b)^2
                 + (a^3*b^2*c^2 - a^5*(b+c-a)^2)/(b+c-a)^2
                 + (a^2*b^2*c^3)/(a+b-c)^2 - c^5*(a+b-c)^2/(a+b-c)^2 \<ge> 0"
    by linarith
  also have "... \<equiv> (a^2*b^3*c^2 - b^5*(c+a-b)^2)/(c+a-b)^2
                 + (a^3*b^2*c^2 - a^5*(b+c-a)^2)/(b+c-a)^2
                 + (a^2*b^2*c^3)/(a+b-c)^2 - c^5*(a+b-c)^2/(a+b-c)^2 \<ge> 0"
    by (simp add: diff_divide_distrib)
  also have "... \<equiv> (a^2*b^2*c^3)/(a+b-c)^2 - c^5*(a+b-c)^2/(a+b-c)^2
                 + (a^2*b^3*c^2 - b^5*(c+a-b)^2)/(c+a-b)^2
                 + (a^3*b^2*c^2 - a^5*(b+c-a)^2)/(b+c-a)^2 \<ge> 0"
    by linarith
  also have "... \<equiv> (a^2*b^2*c^3 - c^5*(a+b-c)^2)/(a+b-c)^2
                 + (a^2*b^3*c^2 - b^5*(c+a-b)^2)/(c+a-b)^2
                 + (a^3*b^2*c^2 - a^5*(b+c-a)^2)/(b+c-a)^2 \<ge> 0"
    by (simp add: diff_divide_distrib)
  also have "... \<equiv> (c^3*a^2*b^2 - c^3*c^2*(a+b-c)^2)/(a+b-c)^2
                 + (b^3*a^2*c^2 - b^3*b^2*(c+a-b)^2)/(c+a-b)^2
                 + (a^3*b^2*c^2 - a^3*a^2*(b+c-a)^2)/(b+c-a)^2 \<ge> 0"
    by (simp add: Groups.mult_ac(2) Groups.mult_ac(3))
  also have "... \<equiv> (c^3 * (a^2*b^2 - c^2*(a+b-c)^2))/(a+b-c)^2
                 + (b^3 * (a^2*c^2 - b^2*(c+a-b)^2))/(c+a-b)^2
                 + (a^3 * (b^2*c^2 - a^2*(b+c-a)^2))/(b+c-a)^2 \<ge> 0"
    by (simp add: mult.assoc right_diff_distrib')
  also have "... \<equiv> (c^3 * ((a*b)^2 - c^2*(a+b-c)^2))/(a+b-c)^2
                 + (b^3 * ((a*c)^2 - b^2*(c+a-b)^2))/(c+a-b)^2
                 + (a^3 * ((b*c)^2 - a^2*(b+c-a)^2))/(b+c-a)^2 \<ge> 0"
    by (simp add: power_mult_distrib)
  finally show "nejed_2 a b c \<equiv> nejed_3 a b c" 
    by (simp add: mult.commute power_mult_distrib)
qed  

lemma
  fixes a b :: real
  assumes "a>0"
  shows "a*b>0 \<equiv> b>0"
  using assms
  thm zero_less_mult_pos
  by (smt mult_pos_pos zero_less_mult_pos)

text \<open> Ova lema pokazuje da je za dokazivanje početne nejednakosti dovoljno dokazati
       sledeću nejednakost:
  
        a³*(a-b)*(a-c)*(b*c + a*(b+c-a))/(b+c-a)² \<ge> b³*(b-c)*(a-b)*(c*a + b*(c+a-b))/(c+a-b)²
     \<close>
lemma
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a\<ge>b" "b\<ge>c"
  assumes "min_list [a+b, b+c, c+a] > root 2 2"
  assumes "a^2 + b^2 + c^2 = 3"
  shows "(nejed_4 a b c) \<longrightarrow> (nejed_3 a b c)"
  using assms
proof-
  have "b+c-a > 0" using pomocna_lema_2 assms(1-3) assms(6-7) by simp
  have "c+a-b > 0" using pomocna_lema_2 assms(1-3) assms(6-7) by simp
  have "a+b-c > 0" using pomocna_lema_2 assms(1-3) assms(6-7) by simp
  have 1:"c^3*(izraz_1 c a b) \<ge> 0"
  proof-
    have *:"c^3 \<ge> 0" using assms(3) by auto
    have **:"izraz_1 c a b \<ge> 0 \<equiv> (c-a)*(c-b) \<ge> 0" 
    proof-
      have "(izraz_1 c a b) \<ge> 0 \<equiv> (izraz_3 c a b)*(izraz_4 c a b) \<ge> 0"
        using \<open>0 < a + b - c\<close> assms(1-3)
        by (smt power2_le_imp_le zero_le_mult_iff)
      also have "... \<equiv> (izraz_3 c a b) \<ge> 0"
        using izraz_4_pozitivan[of c a b] \<open>0 < a + b - c\<close> assms(1-3)
        by (smt zero_le_mult_iff)
      also have "... \<equiv> (izraz_2 c a b) \<ge> 0"
      proof-
        have "izraz_3 c a b \<ge> 0 \<equiv> a*b - c*(a+b) + c*c \<ge> 0"
          using right_diff_distrib'[of "-c" "a+b" "c"]
          by linarith
        also have "... \<equiv> a*b - c*a - c*b + c*c \<ge> 0"
          by (simp add: diff_diff_add distrib_left)
        also have "... \<equiv> -a*(c-b) - c*b + c*c \<ge> 0"
          by (simp add: mult.commute right_diff_distrib)
        also have "... \<equiv> c*(c-b) - a*(c-b) \<ge> 0" 
          by (simp add: add.commute add_diff_eq diff_le_eq le_diff_eq right_diff_distrib)
        also have "... \<equiv> (c-a)*(c-b) \<ge> 0"
          by (simp add: left_diff_distrib)
        finally show "izraz_3 c a b \<ge> 0 \<equiv> izraz_2 c a b \<ge> 0" .
      qed
      thus "izraz_1 c a b \<ge> 0 \<equiv> (c-a)*(c-b) \<ge> 0"
        using calculation by auto
    qed
    from * have "c^3*(izraz_1 c a b) \<ge> 0 \<equiv> izraz_1 c a b \<ge> 0" 
      using assms(3) zero_less_mult_pos
      by (smt diff_diff_eq2 power_not_zero zero_le_mult_iff)
    also have "... \<equiv> (c-a)*(c-b) \<ge> 0"
      using "**" by linarith
    finally have 4:"c^3*(izraz_1 c a b) \<ge> 0 \<equiv> (c-a)*(c-b) \<ge> 0" .
    have ***: "(a+b-c)^2 \<ge> 0" using \<open>a+b-c>0\<close> by auto
    from * ** *** 4 assms(4) assms(5) show ?thesis
      by (smt divide_nonneg_nonneg mult_nonpos_nonpos)
  qed
  have 2:"a^3*(izraz_1 a b c) \<ge> 0"
  proof-
    have *:"a^3 \<ge> 0" using assms(1) by auto
    have **:"izraz_1 a b c \<ge> 0 \<equiv> (a - b)*(a - c) \<ge> 0" 
    proof-
      have "(izraz_1 a b c) \<ge> 0 \<equiv> (izraz_3 a b c)*(izraz_4 a b c) \<ge> 0"
        using \<open>0 < b+c-a\<close> assms(1-3)
        by (smt power2_le_imp_le zero_le_mult_iff)
      also have "... \<equiv> (izraz_3 a b c) \<ge> 0"
        using izraz_4_pozitivan[of a b c] \<open>0 < b+c-a\<close> assms(1-3)
        by (smt zero_le_mult_iff)
      also have "... \<equiv> (izraz_2 a b c) \<ge> 0"
        using jednakost_izraza_2_3[of a b c] assms(3-5)
      proof-
        have "izraz_3 a b c \<ge> 0 \<equiv> b*c - a*(b+c) + a*a \<ge> 0"
          using right_diff_distrib'[of "-a" "b+c" "a"]
          by linarith
        also have "... \<equiv> b*c - a*b - a*c + a*a \<ge> 0"
          by (simp add: diff_diff_add distrib_left)
        also have "... \<equiv> -b*(a-c) - a*c + a*a\<ge> 0"
          by (simp add: mult.commute right_diff_distrib)
        also have "... \<equiv> a*(a-c) - b*(a-c) \<ge> 0" 
          by (simp add: add.commute add_diff_eq diff_le_eq le_diff_eq right_diff_distrib)
        also have "... \<equiv> (a-b)*(a-c) \<ge> 0"
          by (simp add: left_diff_distrib)
        finally show "izraz_3 a b c \<ge> 0 \<equiv> izraz_2 a b c \<ge> 0" .
      qed
      thus "izraz_1 a b c \<ge> 0 \<equiv> (a-b)*(a-c) \<ge> 0"
        using calculation by auto
    qed
    from * have "a^3*(izraz_1 a b c) \<ge> 0 \<equiv> izraz_1 a b c \<ge> 0" 
      using assms(1) zero_less_mult_pos
      by (smt diff_diff_eq2 power_not_zero zero_le_mult_iff)
    also have "... \<equiv> (a-b)*(a-c) \<ge> 0"
      using "**" by linarith
    finally have 4:"a^3*(izraz_1 a b c) \<ge> 0 \<equiv> (a-b)*(a-c) \<ge> 0" .
    have ***: "(b+c-a)^2 \<ge> 0" using \<open>b+c-a>0\<close> by auto
    from * ** *** 4 show ?thesis
      using assms(4) assms(5) by auto
  qed
  have 3:"b^3*(izraz_1 b c a) \<le> 0"
  proof-
    have *: "b^3 \<ge> 0" using assms(2) by simp
    have **: "izraz_1 b c a \<le> 0 \<equiv> (b-c)*(b-a) \<le> 0"
    proof-
      have "(izraz_1 b c a) \<le> 0 \<equiv> (izraz_3 b c a)*(izraz_4 b c a) \<le> 0"
        using \<open>0 < c+a-b\<close> assms(1-3)
        by (smt mult_nonneg_nonpos2 mult_pos_pos power2_le_imp_le)
      also have "... \<equiv> (izraz_3 b c a) \<le> 0"
        using izraz_4_pozitivan[of b c a] \<open>0 < c+a-b\<close> assms(1-3)
        by (smt mult_nonneg_nonpos2 mult_pos_pos)
      also have "... \<equiv> (izraz_2 b c a) \<le> 0"
        using jednakost_izraza_2_3[of b c a] assms(3-5)
      proof-
        have "izraz_3 b c a \<le> 0 \<equiv> c*a - b*(c+a) + b*b \<le> 0"
          using right_diff_distrib'[of "-b" "c+a" "b"]
          by linarith
        also have "... \<equiv> c*a - b*c - b*a + b*b \<le> 0"
          by (simp add: diff_diff_add distrib_left)
        also have "... \<equiv> -c*(b-a) - b*a + b*b \<le> 0"
          by (simp add: mult.commute right_diff_distrib)
        also have "... \<equiv> b*(b-a) - c*(b-a) \<le> 0" 
          by (simp add: add.commute add_diff_eq diff_le_eq le_diff_eq right_diff_distrib)
        also have "... \<equiv> (b-c)*(b-a) \<le> 0"
          by (simp add: left_diff_distrib)
        finally show "izraz_3 b c a \<le> 0 \<equiv> izraz_2 b c a \<le> 0" .
      qed
      thus "izraz_1 b c a \<le> 0 \<equiv> (b-c)*(b-a) \<le> 0"
        using calculation by auto
    qed
    from * have "b^3*(izraz_1 b c a) \<le> 0 \<equiv> izraz_1 b c a \<le> 0" 
      using assms(1) zero_less_mult_pos "**" assms(4-5)
      by (smt mult_nonneg_nonpos)
    also have "... \<equiv> (b-c)*(b-a) \<le> 0"
      using "**" by linarith
    finally have 4:"b^3*(izraz_1 b c a) \<le> 0 \<equiv> (b-c)*(b-a) \<le> 0" .
    have ***: "(c+a-b)^2 \<ge> 0" using \<open>c+a-b>0\<close> by auto
    from * ** *** 4 show ?thesis
      using assms(4) assms(5)
      by (smt zero_less_mult_pos)
  qed
  have "nejed_4 a b c \<equiv> a^3*(a-b)*(a-c)*(b*c + a*(b+c-a))/(b+c-a)^2
                      -b^3*(b-c)*(a-b)*(c*a + b*(c+a-b))/(c+a-b)^2 \<ge> 0"
    by auto
  also have "... \<equiv> a^3*(a-b)*(a-c)*(b*c + a*(b+c-a))/(b+c-a)^2
                 + b^3*(b-c)*(b-a)*(c*a + b*(c+a-b))/(c+a-b)^2 \<ge> 0"
    by (smt divide_minus_left mult_minus_left mult_minus_right)
  finally have *:"nejed_4 a b c \<equiv> a^3*(a-b)*(a-c)*(b*c + a*(b+c-a))/(b+c-a)^2
                 + b^3*(b-c)*(b-a)*(c*a + b*(c+a-b))/(c+a-b)^2 \<ge> 0" .
  hence "nejed_4 a b c \<longrightarrow> (c^3 * (c-a)*(c-b)*(a*b + c*(a+b-c)))/(a+b-c)^2
                 + (a^3 * (a-b)*(a-c)*(b*c + a*(b+c-a)))/(b+c-a)^2
                 + (b^3 * (b-c)*(b-a)*(c*a + b*(c+a-b)))/(c+a-b)^2 \<ge> 0"
    using 1 * assms(3-5)
    by (smt divide_nonneg_pos mult_nonneg_nonneg mult_nonpos_nonpos zero_less_mult_pos zero_less_power)
  moreover
  have "(c^3 * (c-a)*(c-b)*(a*b + c*(a+b-c)))/(a+b-c)^2
      + (a^3 * (a-b)*(a-c)*(b*c + a*(b+c-a)))/(b+c-a)^2
      + (b^3 * (b-c)*(b-a)*(c*a + b*(c+a-b)))/(c+a-b)^2 \<ge> 0
      \<equiv> nejed_3 a b c"
  proof-
    have "... \<equiv>  (c^3 * ((c-a)*(c-b))*(a*b + c*(a+b-c)))/(a+b-c)^2
                 + (a^3 * ((a-b)*(a-c))*(b*c + a*(b+c-a)))/(b+c-a)^2
                 + (b^3 * ((b-c)*(b-a))*(c*a + b*(c+a-b)))/(c+a-b)^2 \<ge> 0"
      by (simp add: mult.assoc)
    also have "... \<equiv> (c^3 * ((c - a) * c - (c - a) * b)*(a*b + c*(a+b-c)))/(a+b-c)^2
                 + (a^3 * ((a - b) * a - (a - b) * c)*(b*c + a*(b+c-a)))/(b+c-a)^2
                 + (b^3 * ((b - c) * b - (b - c) * a)*(c*a + b*(c+a-b)))/(c+a-b)^2 \<ge> 0"
      using mult.commute
          right_diff_distrib'[of "c-a" "c" "b"]
          right_diff_distrib'[of "a-b" "a" "c"]
          right_diff_distrib'[of "b-c" "b" "a"]
      by simp
    also have "... \<equiv>  (c^3 * ((c*c - a*c)- (c*b - a*b))*(a*b + c*(a+b-c)))/(a+b-c)^2
                 + (a^3 * ((a*a - b*a)- (a*c - b*c))*(b*c + a*(b+c-a)))/(b+c-a)^2
                 + (b^3 * ((b*b - c*b) - (b*a - c*a))*(c*a + b*(c+a-b)))/(c+a-b)^2 \<ge> 0"
      using linordered_field_class.sign_simps(37)[of "c" "a" "c"]
            linordered_field_class.sign_simps(37)[of "c" "a" "b"]
            linordered_field_class.sign_simps(37)[of "a" "b" "a"]
            linordered_field_class.sign_simps(37)[of "a" "b" "c"]
            linordered_field_class.sign_simps(37)[of "b" "c" "b"]
            linordered_field_class.sign_simps(37)[of "b" "c" "a"]
      by presburger
    text\<open>y*z - x*(y+z-x)\<close>
    also have "... \<equiv> (c^3 * (c*c - (a*c + c*b) + a*b)*(a*b + c*(a+b-c)))/(a+b-c)^2
              + (a^3 * (a*a - (b*a + a*c) + b*c)*(b*c + a*(b+c-a)))/(b+c-a)^2
              + (b^3 * (b*b - (c*b + b*a) + c*a)*(c*a + b*(c+a-b)))/(c+a-b)^2 \<ge> 0"
      by smt
    also have "... \<equiv>  (c^3 * (c*c - c*(a+b) + a*b)*(a*b + c*(a+b-c)))/(a+b-c)^2
              + (a^3 * (a*a - a*(b+c) + b*c)*(b*c + a*(b+c-a)))/(b+c-a)^2
              + (b^3 * (b*b - b*(c+a) + c*a)*(c*a + b*(c+a-b)))/(c+a-b)^2 \<ge> 0"
      using distrib_left[of "-c" "a" "b"]
            distrib_left[of "-a" "b" "c"]
            distrib_left[of "-b" "c" "a"]
            add.commute mult.commute
      sorry   
    also have "... \<equiv> (c^3 * (a*b - c*(-c+a+b))*(a*b + c*(a+b-c)))/(a+b-c)^2
              + (a^3 * (b*c - a*(b+c-a))*(b*c + a*(b+c-a)))/(b+c-a)^2
              + (b^3 * (c*a - b*(c+a-b))*(c*a + b*(c+a-b)))/(c+a-b)^2 \<ge> 0"
      sorry
    also have "... \<equiv> (c^3 * ((a*b)^2 - (c*(a+b-c))^2))/(a+b-c)^2
                 + (a^3 * ((b*c)^2 - (a*(b+c-a))^2))/(b+c-a)^2 
                 + (b^3 * ((c*a)^2 - (b*(c+a-b))^2))/(c+a-b)^2\<ge> 0 "
      sorry
    finally show
      "0 \<le> c ^ 3 * (c - a) * (c - b) * izraz_4 c a b / (a + b - c)\<^sup>2 +
       a ^ 3 * (a - b) * (a - c) * izraz_4 a b c / (b + c - a)\<^sup>2 +
       b ^ 3 * (b - c) * (b - a) * izraz_4 b c a / (c + a - b)\<^sup>2 \<equiv> nejed_3 a b c" 
      using add.commute
      by linarith
  qed
  ultimately
  show ?thesis by auto
qed

lemma pomocna_pomocna[simp]:
  fixes a b c :: real
  assumes "a>0" "b>0" "c>0"
  shows "izraz_4 a b c = (a*b + a*c + b*c - a^2)"
  using assms
proof-
  have "izraz_4 a b c = b*c + a*b + a*(c-a)" 
    by (smt right_diff_distrib')
  also have "... = b*c + a*b + a*c - a^2"
    by (simp add: power2_eq_square right_diff_distrib')
  finally show ?thesis by auto
qed

text \<open> Ova lema pokazuje da je za dokazivanje početne nejednakosti dovoljno dokazati 
       sledeću nejednakost:
  
         (a*b + a*c + b*c - a²)/(b+c-a) \<ge> (a*b + a*c + b*c - b²)/(c+a-b)
     \<close>
lemma 
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a\<ge>b" "b\<ge>c"
  assumes "min_list [a+b, b+c, c+a] > root 2 2"
  assumes "b+c-a > 0" "c+a-b > 0" "a+b-c > 0"
  assumes "a^2 + b^2 + c^2 = 3"
  assumes "a^5 + b^5 + c^5 \<ge> 3"
  shows "(nejed_5 a b c) \<equiv> (nejed_4 a b c)"
  using assms
proof-
  from \<open>a>0\<close> \<open>b>0\<close> have 1:"a^3\<ge>0" "b^3\<ge>0" by auto
  from assms(8) assms(7) assms(1-4) have 2:"a+c-b \<ge> b+c-a" by auto
  from assms(1-5) have 3:"a-c \<ge> b-c" "b-c\<ge>0" by auto
  from assms(1-2) assms(4) have "a-b\<ge>0" by auto
  have "nejed_5 a b c \<equiv> (a*b + a*c + b*c - a^2)/(b+c-a)^2 
                      \<ge> (b*a + b*c + a*c - b^2)/(c+a-b)^2"
    using 2 frac_le[of "(b*a + b*c + a*c - b^2)/(c+a-b)"
                       "(a*b + a*c + b*c - a^2)/(b+c-a)" 
                       "b+c-a" "c+a-b"]
            power2_le_imp_le[of "b+c-a" "c+a-b"]
            power2_eq_square[of "b+c-a"]
            power2_eq_square[of "c+a-b"]
  proof-
    have "nejed_5 a b c \<equiv> (izraz_4 a b c)/(b+c-a)
                        \<ge> (izraz_4 b a c)/(c+a-b)"
      using pomocna_pomocna[of "a" "b" "c"]
            pomocna_pomocna[of "b" "a" "c"]
            assms(1-3) mult.commute add.commute
      by auto
    moreover 
    have "(izraz_4 b a c)/(c+a-b) \<ge> 0"
      using izraz_4_pozitivan[of "b" "a" "c"]
      by (smt assms(1) assms(2) assms(3) assms(8) divide_nonneg_pos mult_nonneg_nonneg)
    ultimately
    have "nejed_5 a b c \<equiv>  (izraz_4 a b c)/(b+c-a)^2
                         \<ge> (izraz_4 b a c)/(c+a-b)^2"
      using 2 frac_le[of "(izraz_4 b a c)/(c+a-b)"
                       "(izraz_4 a b c)/(b+c-a)" 
                       "b+c-a" "c+a-b"]
            power2_le_imp_le[of "b+c-a" "c+a-b"]
            power2_eq_square[of "b+c-a"]
            power2_eq_square[of "c+a-b"]
      sorry
    then show "nejed_5 a b c \<equiv> (a*b + a*c + b*c - a^2)/(b+c-a)^2 
                      \<ge> (b*a + b*c + a*c - b^2)/(c+a-b)^2"
      by (simp add: assms(1) assms(2) assms(3))
  qed
  show "(nejed_5 a b c) \<equiv> (nejed_4 a b c)"
    sorry
qed

lemma 
  fixes a b :: real
  assumes "a>0" "b>0"
  shows "a/b/b \<equiv> a/b^2"
  using assms
  by (simp add: power2_eq_square)

thm frac_le power2_le_imp_le zero_less_power power2_eq_square

lemma 
  fixes a b c d :: real
  assumes "a>0" "b>0" "c>0" "d>0" "b<d" "a\<ge>c"
  shows "a/b \<ge> c/d \<equiv> a/b^2 \<ge> c/d^2"
  using assms
  by (smt frac_le power2_le_imp_le zero_less_power)

lemma 
  fixes a b c d :: real
  assumes "a>0" "b>0" "c>0" "d>0"
  shows "a/b \<ge> c/b \<equiv> d*(a/b) \<ge> d*(c/b)"
  using assms
  by (smt real_mult_le_cancel_iff2)

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