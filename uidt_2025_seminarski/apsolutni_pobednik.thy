theory apsolutni_pobednik
  imports Main
begin

(*
Apsolutni pobednik izbora je onaj ko osvoji vise od polovine glasova izaslih biraca. Ako su
poznati svi glasacki listici, odredi da li postoji apsolutni pobednik izbora i koji je to kandidat
(naglasimo da je apsolutni pobednik, ako postoji, jedinstven tj. da nije moguce da postoje dva
razlicita apsolutna pobednika).

Ulaz: Sa stndardnog ulaza se unosi broj glasaca n, a zatim i glasovi (svaki glas predstavlja sifru
nekog kandidata - ceo broj iz intervala [0, 10^9]).

Izlaz: Na standardni izlaz ispisati broj pobednika ako postoji apsolutni pobednik, tj. 'nema'
u suprotnom.

Primer 1:
342 123 342 756 123 756 123 756 756 756   \<rightarrow>   nema
Primer 2:
342 123 342 756 123 756 123 756 756 756 342 756 756   \<rightarrow>   756
*)

(*
Odbaceni pokusaji:
  Prebrojavanje glasova za svakog kandidata koriscenjem asocijativnih kontejnera [O(n) do O(nlogn)]
  Sortiranje niza glasova i brojanje uzastopnih jednakih elemenata [O(nlogn)]
  Trazenje kandidata za apsolutnog pobednika odredjivanjem sredisnjeg elementa niza glasova
                                                                (npr. QuickSelect algoritmom) [O(n)]

Prihvacena metoda:
  Bojer-Murov algoritam [O(n)]
*)

(* Lema: Ako iz nekog skupa koji ima apsolutnog pobednika izbacimo bilo koja dva razlicita glasa,
  onda ce i manji skup imati istog apsolutnog pobednika. *)

term count_list

definition kandidat :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "kandidat x xs \<equiv> count_list xs x > length xs div 2"

fun ima_aps_pobednika :: "nat list \<Rightarrow> bool" where
  "ima_aps_pobednika xs \<longleftrightarrow> (\<exists>x. kandidat x xs)"

term find
term remove1

fun izbaci_dva_razlicita :: "nat list \<Rightarrow> nat list" where
  "izbaci_dva_razlicita [] = []"
| "izbaci_dva_razlicita (x # xs) = (case find (\<lambda>y. y \<noteq> x) xs of Some y \<Rightarrow> remove1 x (remove1 y (x # xs))
                                                               | None \<Rightarrow> x # (izbaci_dva_razlicita xs))"

lemma length_remove1_leq[simp]: "length (remove1 x xs) \<le> length xs"
  by (induction xs) auto

lemma nova_duzina[simp]:
  shows "length (izbaci_dva_razlicita xs) \<le> length xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "find (\<lambda>y. y \<noteq> x) xs")
    case (Some y)
    then have "izbaci_dva_razlicita (x # xs) = remove1 x (remove1 y (x # xs))"
      by simp
    then have "length (izbaci_dva_razlicita (x # xs)) = length (remove1 x (remove1 y (x # xs)))"
      by simp
    moreover have "length (remove1 x (remove1 y (x # xs))) \<le> length (x # xs)"
      by (meson le_trans length_remove1_leq)
    ultimately show ?thesis by simp
  next
    case None
    then have "izbaci_dva_razlicita (x # xs) = x # (izbaci_dva_razlicita xs)"
      by simp
    then have "length (izbaci_dva_razlicita (x # xs)) = 1 + (length (izbaci_dva_razlicita xs))"
      by simp
    also with \<open>length (izbaci_dva_razlicita xs) \<le> length xs\<close> have "... \<le> 1 + (length xs)"
      by simp
    finally show ?thesis by simp
  qed
qed

lemma
  assumes "ima_aps_pobednika xs"
  shows "ima_aps_pobednika (izbaci_dva_razlicita xs)"
  oops

(* kada se izbace 2 razlicita glasa postoji dva slucaja:
    da su oba bila razlicita od kandidata i da je tacno jedan bio za kandidata *)

(* 1. oba su bila razlicita od kandidata *)

(* 2. tacno jedan je bio za kandidata *)
lemma tacno_jedan_kand_izbacen:
  assumes "x_count > n div 2"
  and "x_count' \<ge> x_count - 1"
  and "n' = n - 2"
shows "x_count' > n' div 2"
  using assms
  oops

lemma izbaci_dva_razlicita_ostaje_isti_kandidat:
  assumes "kandidat x xs"
  shows "kandidat x (izbaci_dva_razlicita xs)"
  oops

