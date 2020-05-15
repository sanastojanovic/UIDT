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


type_synonym b_list = "bool list"
type_synonym b_mat = "b_list list"

fun uredj :: "nat list \<Rightarrow> bool" where
"uredj [] \<longleftrightarrow> True"
| "uredj (x # Nil) \<longleftrightarrow> True"      
| "uredj (x # (y # l)) \<longleftrightarrow> (x < y) \<and> uredj (y # l)"

fun posl :: "nat list \<Rightarrow> nat" where
"posl [] = 0"
| "posl (x # Nil) = x"
| "posl (x # l) = posl l"

fun partija :: "b_list \<Rightarrow> nat" where
"partija [] = 0"
| "partija (Cons True l) = 1 + partija l"
| "partija (Cons False l) = partija l"

fun partije_l :: "b_mat \<Rightarrow> nat list" where
"partije_l [] = []"
| "partije_l (Cons x l) = Cons (partija x) (partije_l l)"

value "partije_l [[True, False, True, True], [True, False], [False], []]"

lemma
  fixes n::nat
  fixes t::"nat list"
  assumes "n \<ge> 1" "length t = n" "uredj t"
  shows "\<exists> (p::b_mat). length p = 1 + posl t \<and>
  (\<forall> osoba. (osoba \<in> set p \<and> 1 + posl t = length osoba) \<and>
  (\<forall> br_part. (br_part \<in> set (partije_l p)  \<and> (\<exists> t_i. br_part = t_i \<and> t_i \<in> set t)) \<and>
  (\<forall> ti. (ti \<in> set t \<and> (\<exists> igrac. igrac \<in> set (partije_l p))))
  ))"
  sorry

end