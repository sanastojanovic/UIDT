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


(*bez_pr je funkcija koja brise prvi element u listi.*)

fun bez_pr :: "'a list \<Rightarrow>'a list" where
"bez_pr [] = []"
| "bez_pr (Cons x l) = l"

(*obr_prve brise prve elemente svakog reda u bool matrici.*)

fun obr_prve :: "b_mat \<Rightarrow> b_mat" where
"obr_prve [] = []"
| "obr_prve ([] # l) = obr_prve l"
| "obr_prve ((x # y) # l) = y # (obr_prve l)"

lemma pom:
  fixes a::bool and x::b_list and xs::b_mat
  shows "length (x # xs) = length ((a # x) # xs)"
  by simp

lemma smanjivanje [simp]:
  shows "length (obr_prve l) < Suc (length l)"
proof (induction l)
  case Nil
  show ?case
    by auto
next
  case (Cons x l)
  show ?case
  proof (induction x)
    case Nil
    show ?case
      using Cons by simp
  next
    case (Cons a x)
    show ?case
    proof -
      have "obr_prve ((a # x) # l) =  x # (obr_prve l)"
        by auto
      then have "length (obr_prve ((a # x) # l)) = length (x # (obr_prve l))"
        by auto
      also have "length (obr_prve ((a # x) # l)) = Suc (length (obr_prve l))"
        by auto
      also have "length (obr_prve ((a # x) # l)) = 1 + length (obr_prve l)"
        by auto
     note ih = `length (obr_prve l) < Suc (length l)`
      then have "length (obr_prve ((a # x) # l)) \<le> Suc (length l)"
      using ih by simp
    also have "Suc (length l) < Suc (length (x # l))"
      by simp
    also have  "Suc (length (x # l)) = Suc (length ((a # x) # l))"
      using pom by auto
    from this `Suc (length l) < Suc (length (x # l))` have "Suc (length l) < Suc (length ((a # x) # l))"
      by simp
    from this `length (obr_prve ((a # x) # l)) \<le> Suc (length l)`
    show ?thesis
      by simp
  qed
qed
qed


value "obr_prve [[True, False],[True],[True, False, False]]"
value "size_list length (obr_prve [[True, False],[True],[True, False, False]])"

(*Funkcija koja od zadate bool matrice nalazi njenu gornje trougaonu matricu.*)

fun gore_tr :: "b_mat \<Rightarrow> b_mat" where
"gore_tr [] = []"
| "gore_tr (x # l) = x # obr_prve ( gore_tr l)"

value "gore_tr [[True, False, True], [False, True, False], [False, False, True]]"

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


(*Provera da li je matrica simetricna: Direktno proveriti u jednoj funkciji, tako sto se
proverava da li je simetricna matrica kojoj se obrise prva kolona i prvi red i a li su prva kolona i
prvi red jednaki, a onda rekurzivno to primeniti da ostatak matrice.*)
(*Funkcija sim_mat*)

function sim_mat :: "b_mat \<Rightarrow> bool" where
"sim_mat [] \<longleftrightarrow> True"
| "sim_mat ([] # l) \<longleftrightarrow> False"
| "sim_mat ((x # y) # l) \<longleftrightarrow> b_kv (obr_prve l) \<and> (length y = length l) \<and> (y = (pocetni l)) \<and> sim_mat (obr_prve l) "
  by pat_completeness auto
termination 
  apply (relation "measure (\<lambda> m. length m)")
   apply auto
  done

value "sim_mat [[True, True, False], [True, False, False], [False, False, False]]"
value " troug (gore_tr [[True, True, False], [True, False, False], [False, False, False]])"
value " troug (gore_tr [[False, True, False], [True, False, False], [False, False, False]])"


lemma
  fixes n::nat
  fixes t::"nat list"
  assumes "n \<ge> 1" "length t = n" "sorted t"
  shows "\<exists> (p::b_mat). sim_mat b \<and> troug (gore_tr p) \<and> length p = 1 + last t \<and> troug p \<and>
  (\<forall> osoba. (osoba \<in> set p \<and> 1 + last t = length osoba) \<and> (set t) = set (partije_l p))"
  sorry

end