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

(*Funkcija b_kv proverava da li je bool matrica kvadratna.*)

definition b_kv :: "b_mat \<Rightarrow> bool" where
"b_kv a = (size_list length a =(length a)*(1+length a))"

value "b_kv [[True, False], [True, True]]"

(*Funkcija prvi vraca prvi element bool liste.*)

fun prvi :: "bool list \<Rightarrow> bool" where
"prvi [] = False"
|"prvi (x # l) = x"

value "prvi [True, False, True]"

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

(*I ideja za proveru da li je matrica simetricna: Napraviti funkciju koja od matrice pravi gornje, trougaonu matricu,
i drugu koja pravi donje trougaonu matricu. Zatim napraviti funkciju koja proverava da li gornje trougaona matrica na
glavnoj dijagonali ima False. Onda proveriti da li su gornje trougaona matrica i reverse donje trougaona matrica jednake
i da li za gornje trougaonu vazi da ima False na glavnoj dijagonali.*)


(*bez_pr je funkcija koja brise prvi element u listi.*)

fun bez_pr :: "'a list \<Rightarrow>'a list" where
"bez_pr [] = []"
| "bez_pr (Cons x l) = l"

(*bez_posl je funkcija koja brise poslednji element u listi.*)

fun bez_posl :: "'a list \<Rightarrow> 'a list" where
"bez_posl [] = [] "
| "bez_posl (x # []) = []"
| "bez_posl (x # l) = x # (bez_posl l)"

(*obr_prve brise prve elemente svakog reda u bool matrici.*)

fun obr_prve :: "b_mat \<Rightarrow> b_mat" where
"obr_prve [] = []"
| "obr_prve ([] # l) = obr_prve l"
| "obr_prve ((x # y) # l) = y # (obr_prve l)"

(*obr_posl brise u svakom redu u bool matrici poslednji element.*)

fun obr_posl :: "b_mat \<Rightarrow> b_mat" where
"obr_posl [] = [] "
| "obr_posl (x # l) = (bez_posl x) # (obr_posl l)"

value "obr_prve [[True, False],[True],[True, False, False]]"
value "obr_posl [[True, False],[True],[True, False, False]]"
value "size_list length (obr_prve [[True, False],[True],[True, False, False]])"
value "obr_posl [[True, False],[True],[True, False, False]]"

(*Funkcija koja od zadate bool matrice nalazi njenu gornje trougaonu matricu.*)

fun gore_tr :: "b_mat \<Rightarrow> b_mat" where
"gore_tr [] = []"
| "gore_tr (x # l) = x # obr_prve ( gore_tr l)"

value "gore_tr [[True, False, True], [False, True, False], [False, False, True]]"

(*na_kraj funkcija stavlja prosledjeni element na kraj zadate liste*)

primrec na_kraj:: "'a \<Rightarrow>'a list \<Rightarrow> 'a list" where
 "na_kraj x [] = x # []"
| "na_kraj x (y # l) = y # (na_kraj x l)"

value "na_kraj True [False, False]"

value "[False, False, False, True] # [[True]]"

(*Funkcija dole_tr proverava da li je matrica dole trougaona.*)
fun dole_tr :: "b_mat \<Rightarrow> b_mat" where
"dole_tr [] = []"
| "dole_tr (x # l) = na_kraj (last l) (dole_tr (bez_posl (x #(obr_posl l))))"

value "gore_tr [[True, False, False],[True, False, True],[True, False, False]]"
value "dole_tr [[True, False, False],[True, False, True],[True, False, False]]"


(*Funkcija koja vraca da li je matrica trougaona, sa glavnom dijagonalom false.*)

fun troug :: "b_mat \<Rightarrow> bool" where
"troug [] \<longleftrightarrow> True"
|"troug (Cons x l) \<longleftrightarrow> (troug l) \<and> (1 + length l = length x) \<and> (\<not> prvi x)"


(*Provera da li ispravno radi trougaona matrica.*)
value "troug [[False, True, True],[False, True], [False]]"
value "size_list length [[],[[]]]"

(*Lema fiksira n i listu od t1 do tn. Pokazuje da postoji takva trougaona bool matrica p,
sa False na glavnoj dijagonali, za koju istovremeno mogu da važe uslovi (i) i (ii) iz zadatka.*)

(*Funkcija pocetni izdvaja sve pocetne elemente redova bool matrice u bool listu.*)

fun pocetni :: "b_mat \<Rightarrow> b_list" where
"pocetni [] = []"
| "pocetni (x # l) = (prvi x) # (pocetni l)"

value "pocetni [[True, False],[True, False],[]]"

value "size_list length[[True,False,True],[True,True,False],[False,False,False]]"


(*II ideja provere da li je matrica simetricna: Direktno proveriti u jednoj funkciji, tako sto se
proverava da li je simetricna matrica kojoj se obrise prva kolona i prvi red i a li su prva kolona i
prvi red jednaki, a onda rekurzivno to primeniti da ostatak matrice.*)
(*Funkcija sim_mat*)

fun sim_mat :: "b_mat \<Rightarrow> bool" where
"sim_mat [] \<longleftrightarrow> True"
| "sim_mat ([] # l) \<longleftrightarrow> False"
| "sim_mat ((x # y) # l) \<longleftrightarrow> b_kv (obr_prve l) \<and> (length y = length l) \<and> (y = (pocetni l)) \<and> sim_mat (obr_prve l) "


lemma
  fixes n::nat
  fixes t::"nat list"
  assumes "n \<ge> 1" "length t = n" "sorted t"
  shows "\<exists> (p::b_mat). length p = 1 + last t \<and> troug p \<and>
  (\<forall> osoba. (osoba \<in> set p \<and> 1 + last t = length osoba) \<and> (set t) = set (partije_l p))"
  sorry

end