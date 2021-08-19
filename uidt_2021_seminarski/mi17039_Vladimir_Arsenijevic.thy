theory mi17039_Vladimir_Arsenijevic
  imports Main Complex_Main
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


primrec sublist_pom :: "'a list ⇒ nat ⇒ nat ⇒ nat ⇒ 'a list" where
"sublist_pom [] n m i = []" |
"sublist_pom (x#xs) n m i = (if i<n then (sublist_pom xs n m (i+1)) else (
  if i>m then [] else (x#sublist_pom xs n m (i+1))))"

definition sublist:: "'a list ⇒ nat ⇒ nat ⇒ 'a list" where
"sublist l n m = sublist_pom l n m 0"

fun red_gore :: "int list⇒int list" where
"red_gore [x] = []" |
"red_gore [x,y] = [abs(x-y)]" |
"red_gore (x#y#xs) = red_gore (y#xs) @ [abs(x-y)]"

lemma len_vrednost_manje_len_x:
  assumes "x≠[]"
  shows "length (red_gore x) < length x"
proof(induction x)
  case Nil
  then show ?case sorry
next
  case (Cons a x)
  have "length (red_gore (a # x)) = length (red_gore x) + 1"
    (*by (smt (z3) Cons.IH One_nat_def add.right_neutral add_Suc_right length_Cons length_append_singleton list.discI list.sel(3) list.size(3) not_less_zero red_gore.elims)*) sorry
  from this and ‹length (red_gore x) < length x› have "length (red_gore (a # x)) < length x +1" by auto
  then show ?case by simp
qed
(*proof(cases x)
  case Nil
  from this and ‹x≠[]›show ?thesis by auto
next
  case (Cons a list)
  then show ?thesis
  proof(cases list)
    case Nil
then show ?thesis
  by (simp add: local.Cons)
next
  case (Cons a' list')
  from ‹x = a#list› and ‹list = a' # list'› have "x = a#a'#list'" by auto
  then have "red_gore (a#a'#list') = red_gore (a'#list') @ [abs(a-a')]" sorry
  then show ?thesis sorry
qed
qed*)

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

(*definition je_resenje :: "int list ⇒ bool" where
"je_resenje l ≡ (sum_list l = sum_list[1..2037171]) ∧ (length l = 2037171)"
*)

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
  sorry
 termination
   apply (relation "measure (λ (a, b, c). b)")
     apply simp
   sorry

definition sabirci_n :: "int list ⇒ nat ⇒ int list" where
"sabirci_n l n = cikcak (trougao l) (length(l)::nat) n"

lemma an_mora_da_bude_suma_1_do_n:
  assumes "je_resenje l"
  assumes "length l = 10"
  assumes "n ≤ length(l)"
  assumes "sum_list (sabirci_n l n) = sum_list [1..10]"
  assumes "an ∈ set l"
  assumes "an > 10"
  shows "False"
proof-
  from ‹je_resenje l› have "(set(trougao l) = set([1..55]))"
    using assms(1) je_resenje_def by blast
  from this and ‹an ∈ set l› have "an ∈ set (trougao l)" sorry (*ako je u l treba da je i u trougao l*)
  from this and ‹(set(trougao l) = set([1..55]))› have "an ∈ set [1..55]" by blast
  from this and ‹an > 10› show ?thesis sorry (*Ne zna da se svaki broj pojavljuje jednom*)
qed

value "trougao [2::int,4,9,6]"
value "sabirci_n (trougao [2::int,4,9,6]) 2"

lemma duzina_manje_je_bar_pola:
  assumes "length l = 10"
  assumes "i < length l-1"
  assumes "i>0"
  assumes "j = i+1"
  assumes "l' = sublist l 0 (i-1)"
  assumes "l'' = sublist l (j+1) (length l-1)"
  assumes "lp = (if length l' > length l'' then l' else l'')"
  shows "length lp ≥ (length l - 2) / 2"
  sorry

lemma resenje:
  assumes "je_resenje (trougao l)"
  assumes "length l = 10"
  shows "False"
proof -
  from ‹length l = 10› obtain "i" where "i<length l - 1 ∧ i>0"
    by (metis One_nat_def Suc_pred discrete le_Suc_eq less_numeral_extra(1) nat_1_add_1 numeral_eq_iff one_less_numeral_iff semiring_norm(76) semiring_norm(86) semiring_norm(87) zero_less_numeral)
  obtain "j" where "j = i+1" by auto
  obtain "an" where "an = l!i" by auto
  obtain "bn" where "bn = l!j" by auto
  obtain "l'" where "l' = sublist l 0 (i-1)" by auto
  obtain "l''" where "l'' = sublist l (j+1) (length l - 1)" by auto
  obtain "lp" where "lp = (if length l' > length l'' then l' else l'')" by auto (*length lp > n-2/2*)

  obtain "i'" where "i'<i ∧ i'≥0"
    using ‹i < length l - 1 ∧ 0 < i› by blast
  obtain "j'" where "j' = i'+1" by auto
  obtain "ak" where "ak = l!i'" by auto
  obtain "bk" where "bk = l!j'" by auto
  with duzina_manje_je_bar_pola have "length lp ≥ (length l - 2) / 2"
    using ‹i < length l - 1 ∧ 0 < i› ‹j = i + 1› ‹l' = sublist l 0 (i - 1)› ‹l'' = sublist l (j + 1) (length l - 1)› ‹lp = (if length l'' < length l' then l' else l'')› assms(2) by blast
  with this and an_mora_da_bude_suma_1_do_n have "bk ≥ sum_list [(length l)+1..(length l)+(length lp)]"
    sorry

  then have "bk = (length lp)*(2*(length l) + (length lp) + 1) / 2" sorry
  then have "bk ≥ ((length l)-2) / 4 * (2*(length l) + ((length l)-2)/2 + 1)" sorry
  then have "bk = 5*(length l)*((length l)-2)/8" sorry
  then have "bk ≥ sum_list [1..10]" sorry
  then show ?thesis sorry
qed

end
