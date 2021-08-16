theory mi17039_Vladimir_Arsenijevic
  imports Main
begin

text‹
  https://www.imo-official.org/problems/IMO2018SL.pdf

  Zadatak C4
  Antipaskalov trougaoje tablica u obliku jednakostraniqnog trouglakoja se sastoji od brojeva tako da, osim za brojeve u poslednjem redu, vazi da je svakibroj jednak apsolutnoj vrednosti razlike dva broja koja su neposredno ispod njega. Da li postoji antipaskalov trougao sa 2018 redova koji se sastoji od svih prirodnihbrojeva od 1 do 1 + 2 +···+ 2018?
›

(*
   1
  3 2
 2 5 3
2 4 9 6

1 | 3 2 | 2 5 3 | 2 4 9 6
2 4 9 6 2 5 3 3 2 1
*)


primrec sublist_pom :: "'a list ⇒ int ⇒ int ⇒ int ⇒ 'a list" where
"sublist_pom [] n m i = []" |
"sublist_pom (x#xs) n m i = (if i<n then (sublist_pom xs n m (i+1)) else (
  if i>m then [] else (x#sublist_pom xs n m (i+1))))"

definition sublist:: "'a list ⇒ int ⇒ int ⇒ 'a list" where
"sublist l n m = sublist_pom l n m 0"

lemma len_vrednost_manje_len_x:
  shows "length (red_gore x) < length x"
  apply(induction x)
  sorry

fun red_gore :: "int list⇒int list" where
"red_gore [x,y] = [abs(x-y)]" |
"red_gore (x#y#xs) = red_gore (y#xs) @ [abs(x-y)]"

function trougao' :: "int list ⇒ int list ⇒ int list" where
"trougao' l1 l2 =
  (if l2 = [] then []
  else if (length l2) = 1 then l2
  else l1@((trougao' (rev (red_gore l2)) (rev (red_gore l2)))))"
  by pat_completeness auto
  termination
  apply (relation "measure (λ (a, b). length b)")
    apply(auto simp add: len_vrednost_manje_len_x)
    done

fun trougao :: "int list ⇒ int list" where
"trougao x = x@(trougao' [] x)"

value "length []"
value "red_gore [2::int,4,9,6]"
value "red_gore [3::int,5,2]"
value "red_gore [3::int,2]"
value "trougao' [] [2::int,4,9,6]"
value "trougao [2::int,4,9,6]"

(*function trougao_levo :: "int list ⇒ int ⇒ int list" where (*TODO Greska sa l!0 .. l!an, daje los niz*)
"trougao_levo l an = trougao [(l!0)::int..(l!an)]"
  using len_vrednost_manje_len_x apply fastforce
  by simp

function trougao_desno :: "int list ⇒ int ⇒ int list" where
"trougao_desno l an = trougao [(l!an)::int..(l!(length l))]"
  using len_vrednost_manje_len_x apply fastforce
  by simp*)

(*definition je_resenje :: "int list ⇒ bool" where
"je_resenje l ≡ (sum_list l = sum_list[1..2037171]) ∧ (length l = 2037171)"

value "foldr (λx y. x-y) (sort [5::nat,1,2,3,4]) 0"
value "fold (λx y. x+y) [5::nat,6,7] 0"
value "sum_list [1..2018]"*)

definition je_resenje2 :: "int list ⇒ bool" where
"je_resenje2 l ≡ (sum_list l = sum_list[1..55]) ∧ (length l = 55)"

definition je_resenje :: "int list ⇒ bool" where (*Treba mset ali prijavljuje gresku*)
"je_resenje l = (set(trougao l) = set([1..55]))"

(*n sirina trenutnog reda, m el koji se trazi iz pocetne liste*)
function cikcak:: "int list ⇒ nat ⇒ nat ⇒ int list" where
"cikcak l 1 m = [l!0]" |
"cikcak l n m = (if m = 0 then l!(m+1) # (cikcak (sublist l (n+1) (length l)) (n-1) m) 
else l!(m-1) # (cikcak (sublist l (n+1) (length l)) (n-1) (m-1)))"
     apply auto[1]
    apply fastforce
  apply (metis len_vrednost_manje_len_x less_numeral_extra(3) list.sel(2) list.size(3))
  by force
 termination
   apply (relation "measure (λ (a, b, c). b)")
     apply simp
    apply (metis len_vrednost_manje_len_x less_numeral_extra(3) list.sel(2) list.size(3))
   by (metis len_vrednost_manje_len_x less_numeral_extra(3) list.sel(2) list.size(3))

definition sabirci_n :: "int list ⇒ nat ⇒ int list" where
"sabirci_n l n = cikcak (trougao l) (length(l)::nat) n"

lemma an_mora_da_bude_suma_1_do_n:
  assumes "je_resenje (trougao l)"
  assumes "length l = 10"
  assumes "n ≤ length(l)"
  assumes "sum_list (sabirci_n l n) = sum_list [1..10]"
  shows "False"
proof-
  obtain "an" where "an ∈ set l ∧ an > 10"
    by (metis len_vrednost_manje_len_x less_numeral_extra(3) list.sel(2) list.size(3))
  from ‹je_resenje (trougao l)› have "(set(trougao l) = set([1..55]))"
    by (metis len_vrednost_manje_len_x list.sel(2) list.size(3) rel_simps(70))
  from this and ‹an ∈ set l ∧ an > 10› show ?thesis
    by (metis len_vrednost_manje_len_x list.sel(2) list.size(3) rel_simps(70))
qed

value "trougao [2::int,4,9,6]"
value "sabirci_n (trougao [2::int,4,9,6]) 2" (*Nije dobra def nacrtaj ovo daje 4 5 2 3 2*)

(*lemma svaki_broj_je_permutacija_brojeva_iznad_njega: (*NOTE ovo vazi samo za poslednji red zbog 2. arg*)
  assumes "je_resenje (trougao l)"
  shows "(∀ n::nat. n≤length(l) ⟹ l!n = (∑ x ← sabirci_n l n. x))"
  sorry*)

lemma resenje:
  assumes "je_resenje (trougao l)"
  assumes "length l = 10"
  shows "False"
proof -
  fix an::nat
  fix bn::nat
  fix i j
  fix l' :: "nat list"
  fix l'' :: "nat list"
  obtain "i" where "i<length l - 1 ∧ i>0"
    by (metis len_vrednost_manje_len_x less_numeral_extra(3) list.sel(2) list.size(3))
  obtain "j" where "j = i+1" by auto
  obtain "an" where "an = l!i" by auto
  obtain "bn" where "bn = l!j" by auto
  obtain "l'" where "l' = sublist l 0 (an-1)" by auto
  obtain "l''" where "l'' = sublist l (bn+1) (length l - 1)" by auto
  obtain "lp" where "lp = (if length l' > length l'' then l' else l'')" by auto (*length lp > n-2/2*)

  fix ak::nat
  fix bk::nat
  fix i'::nat
  fix j'::nat
  obtain "i'" where "i'<i ∧ i'≥0"
    using ‹i < length l - 1 ∧ 0 < i› by blast
  obtain "j'" where "j' = i'+1" by auto
  obtain "ak" where "ak = l!i'" by auto
  obtain "bk" where "bk = l!j'" by auto
  have "length lp ≥ (length l - 2) / 2"
    by (metis len_vrednost_manje_len_x less_numeral_extra(3) list.sel(2) list.size(3))
  with this and an_mora_da_bude_suma_1_do_n have "bk ≥ sum_list [(length l)+1..(length l)+(length lp)]"
    by (metis len_vrednost_manje_len_x less_numeral_extra(3) list.sel(2) list.size(3))

  then have "bk = (length lp)*(2*(length l) + (length lp) + 1) / 2"
    by (metis add.right_neutral add_leD2 assms(2) discrete len_vrednost_manje_len_x length_append linorder_not_less list.size(3))
  then have "bk ≥ ((length l)-2) / 4 * (2*(length l) + ((length l)-2)/2 + 1)"
    by (metis len_vrednost_manje_len_x length_append not_add_less2)
  then have "bk = 5*(length l)*((length l)-2)/8"
    by (metis len_vrednost_manje_len_x length_append not_add_less2)
  then have "bk ≥ sum_list [1..10]"
    by (metis len_vrednost_manje_len_x list.sel(2) list.size(3) rel_simps(70))
  then show ?thesis
    by (metis len_vrednost_manje_len_x list.sel(2) list.size(3) rel_simps(70))
qed

end
