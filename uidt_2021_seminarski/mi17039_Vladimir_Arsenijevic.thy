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

function trougao_levo :: "int list ⇒ int ⇒ int list" where (*TODO Greska sa l!0 .. l!an, daje los niz*)
"trougao_levo l an = trougao [(l!0)::int..(l!an)]"
  using len_vrednost_manje_len_x apply fastforce
  by simp

function trougao_desno :: "int list ⇒ int ⇒ int list" where
"trougao_desno l an = trougao [(l!an)::int..(l!(length l))]"
  using len_vrednost_manje_len_x apply fastforce
  by simp

(*definition je_resenje :: "int list ⇒ bool" where
"je_resenje l ≡ (sum_list l = sum_list[1..2037171]) ∧ (length l = 2037171)"

value "foldr (λx y. x-y) (sort [5::nat,1,2,3,4]) 0"
value "fold (λx y. x+y) [5::nat,6,7] 0"
value "sum_list [1..2018]"*)

definition je_resenje :: "int list ⇒ bool" where
"je_resenje l ≡ (sum_list l = sum_list[1..55]) ∧ (length l = 55)"

definition je_resenje2 :: "int list ⇒ bool" where
"je_resenje2 l = ((set(trougao l) ⊆ set([1..55])) ∧ (set(trougao l) ⊇  set([1..55])))"

fun cikcak:: "int list ⇒ nat ⇒ nat ⇒ nat ⇒ int list" where
"cikcak l n 0 offset = [l!0]"|
"cikcak l n m offset = l!(m-1 + offset) # l!(m-1+n + offset) # (cikcak l (n-1) (m-1) ((offset::nat)+n))" (*Ista greska*)

definition sabirci_n :: "int list ⇒ nat ⇒ int list" where
"sabirci_n l n = cikcak (trougao l) (length(l)::nat) n 0"

lemma an_mora_da_bude_suma_1_do_n:
  assumes "je_resenje (trougao l)"
  assumes "n ≤ length(l)"
  shows "set (sabirci_n l n) = set [1..10]"
  sorry

value "trougao [2::int,4,9,6]"
value "cikcak (trougao [2::int,4,9,6]) (length(l)::nat) 2 0" (*Nije dobra def nacrtaj ovo daje 4 5 2 3 2*)

lemma svaki_broj_je_permutacija_brojeva_iznad_njega: (*NOTE ovo vazi samo za poslednji red zbog 2. arg*)
  assumes "je_resenje (trougao l)"
  shows "(∀ n::nat. n≤length(l) ⟹ l!n = (∑ x ← sabirci_n l n. x))"
  sorry

lemma resenje:
  assumes "je_resenje (trougao l)"
  shows "False"
proof -
  fix xs::int
  fix ys::int
  fix i j
  fix T' :: "int list"
  fix T'' :: "int list"
  obtain "i" where "i<length l - 1"
    by (metis add_leD2 discrete le_add_diff_inverse2 len_vrednost_manje_len_x less_diff_conv2)
  obtain "j" where "j = i+1" by auto
  obtain "xs" where "xs = l!i" by auto
  obtain "ys" where "ys = l!j" by auto
  obtain "T'" where "T' = trougao_levo l an" by auto
  obtain "T''" where "T'' = trougao_desno l bn" by auto
  obtain "T" where "T = (if length T' > length T'' then T' else T'')" by auto (*Valjalo bi izvuci listu samo i pokazati da je l≥n-2/2*)

  fix a'k::int
  fix b'k::int
  fix i' j'
  obtain "i'" where "i'<an" by (smt (z3))
  obtain "j'" where "j' = i'+1" by auto
  obtain "a'k" where "a'k = l!i" by auto (*Fali ' prijavljuje ERROR u ovoj liniji*)
  obtain "b'k" where "b'k = l!j" by auto
  with svaki_broj_je_permutacija_brojeva_iznad_njega
  have "xs = sum_list (sabirci_n l i)" sorry (*Treba i' j'*)
  then have "b'k = sum_list (sabirci_n l j)" sorry


  (*Kraj dokaza iz resenja iz pdf-a*)
  then have "b'k ≥ sum_list [n+1..n+l]" sorry
  then have "b'k = l*(2*n + l + 1) / 2" sorry
  then have "b'k ≥ (n-2) / 4 * (2*n + (n-2)/2 + 1)" sorry
  then have "b'k = 5*n*(n-2)/8" sorry
  then have "b'k ≥ sum_list [1..10]" sorry
  then show ?thesis sorry


end
