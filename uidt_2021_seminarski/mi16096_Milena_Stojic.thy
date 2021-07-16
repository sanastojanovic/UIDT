theory mi16096_Milena_Stojic
  imports Complex_Main mi16096_Milena_Stojic_Binommial_coefficients

begin

text \<open>
Link ka seminarskom zadatku: https://imomath.com/srb/zadaci/2011_mmo.pdf

Formulacija seminarskog zadatka: 
   
   Neka je n prirodan broj. Date su terazije (uravnotežena vaga sa dva tasa) i n tegova,
   težina 2^0, 2^1, ..., 2^(n-1). Svih n tegova se stavljaju, jedan za drugim, na tasove
   terazija, odnosno u svakom od n koraka se bira jedan od tegova koji se već ne nalazi na
   tasovima i stavlja ili na levi ili na desni tas; pritom se tegovi postavljaju tako da 
   ni u jednom trenutku desni tas nije teži od levog. 
   Odrediti broj načina na koji se ovo postavljanje može izvršiti.


   Napomena: Plan u dogovoru sa profesorom je bio da definišem teoriju binomnih koeficijenata
   i u njoj dokažem neke od važnih identiteta sa njima. 
   Ovde će ta teorija biti u zasebnom fajlu mi16096_Milena_Stojic_Binommial_coefficients.thy koji
   je uključen u ovu teoriju.

   Nakon toga, plan je da kreirani izraz za funkciju od broja n (n-1 je najviši stepen dvojke
   tega najveće težine) transformišem u okviru dokaza. 
   Tokom rada, plan može biti podložan izmenama. 

   Ovde dokazujemo da je taj izraz za funkciju (koji će, kada ga budemo sastavljali
   biti rekurentno zadat) zapravo jednak proizvodu svih neparnih brojeva do (2n - 1), 
   tj. 1 * 3 * 5 * 7 * ... * (2n - 1) = (2n - 1) !!
   
\<close>




text 
\<open>
  Na početku ćemo prvo dokazati teoremu koja će nam posle opravdati
  korak kada budemo sastavljali formulu za funkciju od n.

  Naime, koristećemo činjenicu da je 2^(n-1) veći od sume svih stepena dvojke
  od nultog do (n-2). Pa je samim tim 2^(n-1) veće i od sume bilo koliko proizvoljno
  odabranih od ostalih stepena dvojke.

  Prvo ćemo formulisati i dokazati teoremu za a^n - 1. Zbog svojstava racionalnih brojeva
  koje ćemo koristiti pri dokazu, a (i kasnije dvojka) ćemo razmatrati kao racionalan
  broj. (to ne menja ništa suštinski, važno je samo da n posmatramo kao prirodan broj)
\<close>
lemma difference_between_degree_and_one:
  fixes a::rat and n::nat
  assumes "n \<ge> 1"
  shows "a^n - 1 = (a - 1) * (\<Sum> i::nat= 0..(n-1). a^i)" (is "?D = ?d * ?s")
  using assms
proof (induction n rule: nat_induct_at_least) \<comment> \<open>Koristimo indukciju koja počinje nekim prirodnim brojem. (većim od nule)\<close>
  case base
  then have "(\<Sum> i::nat= 0..(1-1). a^i) = 1" by simp
  then have "(a - 1) * (\<Sum> i::nat = 0..(1-1). a^i) = (a - 1)" by simp
  also have "\<dots> = a^1 - 1" by simp
  finally show ?case by simp
next
  case (Suc n)
  then have "(\<Sum> i::nat = 0..n. a^i) = (\<Sum> i::nat = 0..(n-1) . a^i)
                                         + a^n" 
    sledgehammer
    by (metis le_add_diff_inverse plus_1_eq_Suc sum.atLeast0_atMost_Suc)
  then have "(a - 1) * (\<Sum> i::nat = 0..n. a^i) 
           = (a - 1) * ((\<Sum> i::nat = 0..(n-1). a^i) + a^n)"
    by simp
  also have "\<dots> = (a - 1) * (\<Sum> i::nat = 0..(n-1). a^i) + 
                  (a - 1) * a^n"
     find_theorems "_*(_+_)"
     by (subst distrib_left, rule refl)
   also have "\<dots> = a^n - 1 + (a - 1) * a^n" 
     thm Suc
     using Suc
     by simp
   also have "\<dots> = a^n - 1 + (a * a^n - 1 * a^n)"
     by (subst left_diff_distrib, rule refl)
   also have "\<dots> = a^n - 1 + (a^(Suc n) - a^n)"
     by simp
   also have "\<dots> = a^n - 1 + a^(Suc n) - a^n"
     by simp
   also have "\<dots> = a^(Suc n) - 1" by simp
   finally show ?case by simp
 qed

 text
\<open>
  Sada iz prethodne teoreme izvlačimo direktnu posledicu: 
  Važi i za a = 2. Kako će nam izraz zapravo izgledati za a = 2?
\<close>
lemma difference_between_degree_two_and_one:
  fixes n::nat
  assumes "n \<ge> 1"
  shows "(2::rat)^n - 1 = (\<Sum> i::nat=0..(n-1). 2^i)"
  using assms
  by (auto simp add: difference_between_degree_and_one)

text
\<open>
  Za a = 2 zapravo dobijamo da je razlika 2^n - 1 upravo jednaka sumi svih
  stepena dvojki od 0 do (n-1). Sada, iz ove teoreme, možemo da izvedemo direktnu
  posledicu da je 2^n veće od sume svih stepena dvojki od 0 do (n-1).
\<close>
lemma the_highest_degree_greater_than_sum_of_others:
  fixes n::nat
  assumes "n \<ge> 1"
  shows "(2::rat)^n > (\<Sum> i::nat = 0..(n-1) . 2^i)" (is "_ > ?s")   
  using assms
proof-
  have "?s = (2::rat)^n - 1" 
    using assms difference_between_degree_two_and_one by auto
  also have "\<dots> < 2^n"
    by simp
  finally show ?thesis by auto
qed

text
\<open>
  Ovim koracima smo sada opravdali činjenicu da je 2^(n-1) veće od sume svih
  prethodnih stepena. Sada to možemo da koristimo pri formiranju rekurentne formule.

  Tas na koji stavimo teg težine 2^(n-1) će uvek biti veće težine od drugog tasa,
  koje god i koliko god ostalih tegova budemo stavljali na drugi tas (čak i u slučaju da
  stavimo samo taj teg na levi tas i sve ostale na desni, zbog čega smo i dokazali
  prethodnu teoremu; kod ostalih slučajeva razlika između tog i preostalih tasova može biti 
  samo veća). 
  Prema tome, kada smo stavili tas težine 2^(n-1) (njega zbog ovoga uvek moramo 
  stavljati na levi tas koji nikada ne sme biti lakši), ostale tegove možemo proizvoljno stavljati
  na levi i desni tas, kako god želimo.

  **TODO: Objasni sastavljanje rekurentne formule. Možda i još jedno
  dopunsko tvrđenje da dokažem.**

  Bazni slučaj nam je za n = 0. Tada imamo samo jedan moguć raspored: 2^0 na levi tas.
  U skladu sa tim definišemo rekurentnu formulu.
\<close>
fun f :: "nat \<Rightarrow> nat" where
"f 0 = 1" |
"f n = (\<Sum> i::nat = 1..n. ((binomm (n - 1) (i - 1)) * (f (i - 1)) * (fact (n - i)) * ((2::nat)^(n - i))))"

value "f 1"
value "f 2"
value "f 3"
end