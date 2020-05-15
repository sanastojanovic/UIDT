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

(*U bool matrici tn+1 x tn+1 se čuva ko je sa kim odigrao partiju šaha.
Matrica je zadata tipom b_mat, a red u matrici tipom b_list.*)

type_synonym b_list = "bool list"
type_synonym b_mat = "b_list list"

(*Funkcija uredj vraća True ako je lista prirodnih brojeva strogo rastuća, a False u suprotnom.*)

fun uredj :: "nat list \<Rightarrow> bool" where
"uredj [] \<longleftrightarrow> True"
| "uredj (x # Nil) \<longleftrightarrow> True"      
| "uredj (x # (y # l)) \<longleftrightarrow> (x < y) \<and> uredj (y # l)"

(*Funkcija posl vraća poslednji element u listi prirodnih brojeva.*)

fun posl :: "nat list \<Rightarrow> nat" where
"posl [] = 0"
| "posl (x # Nil) = x"
| "posl (x # l) = posl l"

(*Funkcija partija vraća broj partija koje je odigrala jedna osoba, tj.
prebrojava vrednosti True u bool listi.*)

fun partija :: "b_list \<Rightarrow> nat" where
"partija [] = 0"
| "partija (Cons True l) = 1 + partija l"
| "partija (Cons False l) = partija l"

(*Funkcija partije_l od bool matrice pravi listu koja čuva koliko je svaki igrač odigrao partija.*)

fun partije_l :: "b_mat \<Rightarrow> nat list" where
"partije_l [] = []"
| "partije_l (Cons x l) = Cons (partija x) (partije_l l)"

(*Provera da li partije_l ispravno radi.*)

value "partije_l [[True, False, True, True], [True, False], [False], []]"

(*Lema fiksira n i listu od t1 do tn. Pokazuje da postoji takva bool matrica p,
za koju istovremeno mogu da važe uslovi (i) i (ii) iz zadatka.*)

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