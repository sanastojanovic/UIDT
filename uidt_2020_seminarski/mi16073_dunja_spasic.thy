theory mi16073_dunja_spasic
  imports Main

begin

text\<open>
https://imomath.com/srb/zadaci/2017_egmo.pdf

Zadatak: Dat je prirodan broj n\<ge>1, kao i prirodni brojevi t1 < t2 < ... < tn.
U grupi od tn + 1 ljudi odigran je neki broj partija šaha.
Svake dve osobe su međusobno odigrale najviše jednu partiju.
Dokazati da je moguće da su sledeća dva uslova istovremeno zadovoljena:

(i) Broj partija koju je odigrala svaka od osoba je jedan od brojeva t1, t2, . . . , tn.
(ii) Za svako i za koje važi 1 \<le> i \<le> n, bar jedna osoba je odigrala tačno ti partija.

\<close>


fun uredj :: "nat list \<Rightarrow> bool" where
"uredj [] \<longleftrightarrow> True"
| "uredj (x # Nil) \<longleftrightarrow> True"      
| "uredj (x # (y # l)) \<longleftrightarrow> (x < y) \<and> uredj (y # l)"

fun posl :: "nat list \<Rightarrow> nat" where
"posl [] = 0"
| "posl (x # Nil) = x"
| "posl (x # l) = posl l"


lemma "\<exists> (n :: nat). n \<ge> 1 \<and>
      (\<exists> (turniri :: nat list). (length turniri = n \<and> uredj turniri \<and>
      (\<exists> (p :: nat list). length p = 1 + posl turniri \<and>
      (\<forall> osoba. (osoba \<in> set p \<and> (\<exists> ti. osoba = ti)) \<and>
     ( \<forall> ti. (ti \<in> set turniri \<and> (\<exists> osoba. osoba \<in> set p))
)))))"
  sorry
end