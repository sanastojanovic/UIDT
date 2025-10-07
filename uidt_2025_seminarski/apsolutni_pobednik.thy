theory apsolutni_pobednik
  imports Main
begin

(*
Apsolutni pobednik izbora je onaj ko osvoji vise od polovine glasova izaslih biraca. Ako su
poznati svi glasacki listici, odredi da li postoji apsolutni pobednik izbora i koji je to kandidat
(naglasimo da je apsolutni pobednik, ako postoji, jedinstven tj. da nije moguce da postoje dva
razlicita apsolutna pobednika).

Ulaz: Sa standardnog ulaza se unosi broj glasaca n, a zatim i glasovi (svaki glas predstavlja sifru
nekog kandidata - ceo broj iz intervala [0, 10^9]).

Izlaz: Na standardni izlaz ispisati broj pobednika ako postoji apsolutni pobednik, tj. 'nema'
u suprotnom.

Primer 1:
342 123 342 756 123 756 123 756 756 756   →   nema
Primer 2:
342 123 342 756 123 756 123 756 756 756 342 756 756   →   756
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

definition kandidat :: "nat ⇒ nat list ⇒ bool" where
  "kandidat x xs ≡ count_list xs x > length xs div 2"

fun ima_aps_pobednika :: "nat list ⇒ bool" where
  "ima_aps_pobednika xs ⟷ (∃x. kandidat x xs)"

term find
term remove1

fun izbaci_dva_razlicita :: "nat list ⇒ nat list" where
  "izbaci_dva_razlicita [] = []"
| "izbaci_dva_razlicita (x # xs) = (case find (λy. y ≠ x) xs of Some y ⇒ remove1 x (remove1 y (x # xs))
                                                               | None ⇒ x # (izbaci_dva_razlicita xs))"

lemma length_remove1_leq[simp]: "length (remove1 x xs) ≤ length xs"
  by (induction xs) auto

lemma nova_duzina[simp]:
  shows "length (izbaci_dva_razlicita xs) ≤ length xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "find (λy. y ≠ x) xs")
    case (Some y)
    then have "izbaci_dva_razlicita (x # xs) = remove1 x (remove1 y (x # xs))"
      by simp
    then have "length (izbaci_dva_razlicita (x # xs)) = length (remove1 x (remove1 y (x # xs)))"
      by simp
    moreover have "length (remove1 x (remove1 y (x # xs))) ≤ length (x # xs)"
      by (meson le_trans length_remove1_leq)
    ultimately show ?thesis by simp
  next
    case None
    then have "izbaci_dva_razlicita (x # xs) = x # (izbaci_dva_razlicita xs)"
      by simp
    then have "length (izbaci_dva_razlicita (x # xs)) = 1 + (length (izbaci_dva_razlicita xs))"
      by simp
    also with ‹length (izbaci_dva_razlicita xs) ≤ length xs› have "... ≤ 1 + (length xs)"
      by simp
    finally show ?thesis by simp
  qed
qed

lemma tacno_jedan_kand_izbacen[simp]:
  assumes "count_list xs x > length (xs) div 2"   (* x_count > n/2 *)
  and "length (xs) ≥ 2"                           (* n ≥ 2 *)
  and "x_count' = count_list xs x - 1"            (* x_count' = x_count - 1 *)
  and "n' = length (xs) - 2"                      (* n' = n - 2 *)
shows "x_count' > n' div 2"
  using assms
  by simp

lemma[simp]:
  assumes "kandidat x (x # xs)"
  and "length xs > 0"
  and "∀y ∈ set xs. y = x"
shows "kandidat x xs"
  sorry


(*fun izbaci_dva_razlicita :: "nat list ⇒ nat list" where
  "izbaci_dva_razlicita [] = []"
| "izbaci_dva_razlicita (x # xs) = (case find (λy. y ≠ x) xs of Some y ⇒ remove1 x (remove1 y (x # xs))
                                                               | None ⇒ x # (izbaci_dva_razlicita xs))"*)
lemma aps_pobednik_ostaje:
  assumes "ima_aps_pobednika xs"
  shows "ima_aps_pobednika (izbaci_dva_razlicita xs)"
  using assms
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x1 xs)
  then obtain x where "kandidat x (x1 # xs)"
    using Cons.prems
    unfolding ima_aps_pobednika.simps
    by auto
  then have "count_list (x1 # xs) x > length (x1 # xs) div 2"
    unfolding kandidat_def by auto
  then show ?case
  proof auto
      fix x
      assume all_same: "∀y∈set xs. y = x1" and kandidat_Cons: "kandidat x (x1 # xs)"
      from kandidat_Cons have "length (x1 # xs) div 2 < count_list (x1 # xs) x"
        unfolding kandidat_def .
      with all_same have Suc_length_div_le: "Suc (length xs) div 2 < Suc (count_list xs x)"
        by (auto simp add: if_splits)
      from all_same have "∀y∈set (x1 # xs). y = x1"
        by simp
      with kandidat_Cons have "x1 = x"
        by (metis ‹length (x1 # xs) div 2 < count_list (x1 # xs) x› count_notin not_less0)
      with all_same have "count_list xs x = count_list xs x1"
        by simp
      with all_same have count_length: "count_list xs x = length xs"
        by (induction xs) (auto, metis ‹∀y∈set (x1 # xs). y = x1› ‹length (x1 # xs) div 2 < count_list (x1 # xs) x› count_list_0_iff less_zeroE)
      show "∃x. kandidat x xs"
      proof (rule_tac x="x" in exI)
        show "kandidat x xs"
          unfolding kandidat_def
        proof -
          have "length xs div 2 < length xs"
          proof (cases "length xs = 0")
            case True
            then show ?thesis
              sorry (* treba dodati negde pretpostavku da xs nije prazna, mozda u ovaj lemi ili definiciji *)
          next
            case False
            then show ?thesis
              by simp
          qed
          also have "... = count_list xs x"
            by (simp only: count_length)
          finally show "length xs div 2 < count_list xs x" .
        qed
      qed
    qed
  next
    case (Some x2)  (* mozemo da izbacimo x1 i x2 *)
    then show ?thesis
      unfolding izbaci_dva_razlicita.simps
    proof auto
      assume "find (λy. y ≠ x1) xs = Some x1" "x2 = x1"
      show "∃x. kandidat x (remove1 x1 xs)"
        sorry (* ovde mislim da treba da se izvuce kontradikcija *)
    next
      assume "find (λy. y ≠ x1) xs = Some x2" "x2 ≠ x1"
      show "∃x. kandidat x (remove1 x2 xs)" (* x1 je vec izbacen *)
        sorry
    qed
  qed
qed

lemma izbaci_dva_razlicita_ostaje_isti_kandidat:
  assumes "kandidat x xs"
  shows "kandidat x (izbaci_dva_razlicita xs)"
  oops

