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

fun sublist:: "'a list ⇒ nat ⇒ nat ⇒ 'a list" where
"sublist l n m = sublist_pom l n m 0"

fun red_gore :: "int list⇒int list" where
"red_gore [x] = []" |
"red_gore [x,y] = [abs(x-y)]" |
"red_gore (x#y#xs) = red_gore (y#xs) @ [abs(x-y)]"

value "red_gore [8::nat,3,10,9]"

lemma len_vrednost_manje_len_x:
  assumes "x≠[]"
  shows "length (red_gore x) < length x"
using assms proof(induction x rule: red_gore.induct)
  case (1 x)
  then show ?case
    by simp
next
  case (2 x y)
  then show ?case by simp
next
  case (3 x y v va)
  then show ?case by simp
next
  case 4
  then show ?case by simp
qed

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
"cikcak l (Suc 0) 0 = [l!0]" |
"cikcak l n 0 = l!1 # (cikcak (sublist l (n) (length l)) (n-1) 0)" |
"cikcak l n m = l!(m-1) # (cikcak (sublist l (n) (length l)) (n-1) (m-1))"
     apply auto[1]
       apply fastforce
  sorry
 termination
   apply (relation "measure (λ (a, b, c). c)")
        apply simp
   sorry

(*
ncikcak l 1 m znak = if znak then [-l!!0] else [l!!0]
ncikcak l n 0 znak = if l!!(0) < l!!1 then (if znak then (-l!!1 : (ncikcak (sublist l (n) (length l)) (n-1) 0 False)) else (l!!1 : (ncikcak (sublist l (n) (length l)) (n-1) 0 True)))
else (if znak then (-l!!1 : (ncikcak (sublist l (n) (length l)) (n-1) 0 True)) else (l!!1 : (ncikcak (sublist l (n) (length l)) (n-1) 0 False)))

ncikcak l n m znak = if l!!(m-1) < l!!m then (if znak then (-l!!(m-1) : (ncikcak (sublist l (n) (length l)) (n-1) (m-1) True)) else (l!!(m-1) : (ncikcak (sublist l (n) (length l)) (n-1) (m-1) False)))
else (if znak then (-l!!(m-1) : (ncikcak (sublist l (n) (length l)) (n-1) (m-1) False)) else (l!!(m-1) : (ncikcak (sublist l (n) (length l)) (n-1) (m-1) True)))
*)

function(sequential) ncikcak::"int list ⇒ nat⇒ nat ⇒ bool ⇒ int list" where
"ncikcak l (Suc 0) m znak = (if znak then [-l!0] else [l!0])" |
"ncikcak l n 0 znak = (if l!(0) < l!1 then (if znak then (-l!1 # (ncikcak (sublist l (n) (length l)) (n-1) 0 False)) else (l!1 # (ncikcak (sublist l (n) (length l)) (n-1) 0 True)))
else (if znak then (-(l!1) # (ncikcak (sublist l (n) (length l)) (n-1) 0 True)) else (l!1 # (ncikcak (sublist l (n) (length l)) (n-1) 0 False))))" |
"ncikcak l n m znak = (if l!(m-1) < l!m then (if znak then (-l!(m-1) # (ncikcak (sublist l (n) (length l)) (n-1) (m-1) True)) else (l!(m-1) # (ncikcak (sublist l (n) (length l)) (n-1) (m-1) False)))
else (if znak then (-l!(m-1) # (ncikcak (sublist l (n) (length l)) (n-1) (m-1) False)) else (l!(m-1) # (ncikcak (sublist l (n) (length l)) (n-1) (m-1) True))))"
  sorry
termination
  apply (relation "measure (λ (a, b, c, d). c)")
          apply blast
  apply (smt (z3) One_nat_def cikcak.simps(2) cikcak.simps(3) diff_0_eq_0 diff_Suc_Suc gr0I less_numeral_extra(3) list.inject zero_less_diff)
        apply (smt (z3) cikcak.simps(2) cikcak.simps(3) diff_0_eq_0 list.inject)
  sorry

(*
cc l n m 5 = if l!!m > l!!(m+1) then (l!!(m+1) : [l!!(m)]) else (l!!m : [l!!(m+1)])
cc l n m i = if l!!m > l!!(m+1) then (l!!(m+1) : cc (sublist l n (length l)) (n+1) m (i+1)) else (l!!m : cc (sublist l n (length l)) (n+1) (m+1) (i+1))
ccc l = (reverse l)!!0 : (cc (drop 1 (reverse l)) 2 0 1)*)

function cc::"int list ⇒ nat ⇒ nat ⇒ nat ⇒ int list" where
"cc l n m (Suc (Suc (Suc 0))) = (if l!m > l!(m+1) then (l!(m+1) # [l!(m)]) else (l!m # [l!(m+1)]))" |
"cc l n m i = (if l!m > l!(m+1) then (l!(m+1) # cc (sublist l n (length l)) (n+1) m (i+1)) else (l!m # cc (sublist l n (length l)) (n+1) (m+1) (i+1)))"
  sorry
termination
  sorry

definition ccc::"int list ⇒ int list" where
"ccc l = (rev l)!0 # (cc (drop 1 (rev l)) 2 0 1)"

value "trougao [2::nat,4,9,6]"
value "trougao [8::nat,3,10,9]"
value "trougao [1::nat,2,3,4]"

(*
   1
  3 2 
 2 5 3
2 4 9 6

   4
  2 6 
 5 7  1
8 3 10 9
*)

value "ncikcak [2, 4, 9, 6, 2, 5, 3, 3, 2, 1] 4 0 False"
value "ncikcak [2, 4, 9, 6, 2, 5, 3, 3, 2, 1] 4 1 False"
value "ncikcak [2, 4, 9, 6, 2, 5, 3, 3, 2, 1] 4 2 False"
value "ncikcak [2, 4, 9, 6, 2, 5, 3, 3, 2, 1] 4 3 False"

value "ncikcak [8, 3, 10, 9, 5, 7, 1, 2, 6, 4] 4 0 False"
value "ncikcak [8, 3, 10, 9, 5, 7, 1, 2, 6, 4] 4 1 False"
value "ncikcak [8, 3, 10, 9, 5, 7, 1, 2, 6, 4] 4 2 False"
value "ncikcak [8, 3, 10, 9, 5, 7, 1, 2, 6, 4] 4 3 False"

value "ncikcak [1, 2, 3, 4, 1, 1, 1, 0, 0, 0] 4 0 False"

value "ccc [2, 4, 9, 6, 2, 5, 3, 3, 2, 1]"
value "ccc [8, 3, 10, 9, 5, 7, 1, 2, 6, 4]"
value "ccc [1, 2, 3, 4, 1, 1, 1, 0, 0, 0]"


definition sabirci_n :: "int list ⇒ nat ⇒ int list" where
"sabirci_n l n = cikcak (trougao l) (length(l)::nat) n"

value "sabirci_n [2::nat,4,9,6] 1"

(*   1
    3 2
   2 5 3
  2 4 9 6
*)
lemma an_mora_da_bude_suma_1_do_n:
  assumes "je_resenje l"
  assumes "length l = 10"
  assumes "n < length(l)-1"
  shows "sum_list (sabirci_n l n) = sum_list [1..10]"
  sorry

(*lemma an_mora_da_bude_suma_1_do_n:
  assumes "je_resenje l"
  assumes "length l = 10"
  assumes "n ≤ length(l)"
  assumes "sum_list (sabirci_n l n) = sum_list [1..10]"
  assumes "an ∈ set l"
  assumes "an > 55"
  shows "False"
proof-
  from ‹je_resenje l› have "(set(trougao l) = set([1..55]))"
    using assms(1) je_resenje_def by blast
  from this and ‹an ∈ set l› have "an ∈ set (trougao l)" sorry (*ako je u l treba da je i u trougao l*)
  from this and ‹(set(trougao l) = set([1..55]))› have "an ∈ set [1..55]" by blast
  from this and ‹an > 55› show ?thesis sorry (*Ne zna da se svaki broj pojavljuje jednom*)
qed*)

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
  shows "length lp ≥ ⌈(length l - 2) / 2⌉"
  sorry

primrec suma' :: "nat ⇒ nat" where
"suma' 0 = 0" |
"suma' (Suc n) = suma' n + (Suc n)"

lemma suma_n_n_1_2: "suma' n = n * (n + 1) div 2"
  apply (induction n)
   apply simp +
  done

definition suma:: "nat⇒nat⇒nat" where
"suma n m = suma' m - suma' (n-1)"

lemma ako_je_jedan_veci_od_sum_1_n_false:
  assumes "x>55"
  assumes "je_resenje l"
  assumes "length l = 10"
  assumes "n < length(l)-1"
  shows "False"
  sorry


lemma pom1:
  fixes n::nat
  assumes "2*l≥ (n-2)"
  assumes "n>0"
  shows "2 * suma (n+1) (n+l) = l*(2*n + l + 1)"
proof(induction n)
  case 0
  then show ?case
  proof-
    have "2 * suma (0 + 1) (0 + l) = 2*suma 1 l" by auto
    then have "... = 2 * (suma' l - suma' 0)" by (simp add: suma_def)
    then have "... = 2 * ((l * (l+1) div 2) + 0)" by (simp add: suma_n_n_1_2)
    then have "... = 2 * (l * (l+1) div 2)" by auto
    then have "... = l * (l+1)" by auto
    then show ?case using ‹2 * (suma' l - suma' 0) = 2 * (l * (l + 1) div 2 + 0)› ‹2 * suma 1 l = 2 * (suma' l - suma' 0)› by auto
  qed
next
  case (Suc n)
  then show ?case
  proof-
    have "2 * suma (Suc n + 1) (Suc n + l) = 2 * suma (n + 2) (n + l + 1)" by auto
    then have "... = 2* (suma' (n+l+1) - suma' (n+1))" by (metis Suc_1 Suc_eq_plus1 add_Suc_shift add_diff_cancel_right' suma_def)
    then have "... = 2 * (suma' (n+l) + (n+l+1) - suma' (n+1))" using Suc_eq_plus1 suma'.simps(2) by presburger
    then have "... = 2 * (suma' (n+l) + n+l+1 - (suma' n + n+1))" using Suc_eq_plus1 suma'.simps(2) by presburger
    then have "... = 2 * (suma' (n+l) + n+l+1 - suma' n - (n+1))" using diff_diff_left by presburger
    then have "... = 2* (suma' (n+l) - suma' n + n+l+1 - (n+1))" sorry
    then have "... = 2*(suma (n+1) (n+l) + n+l+1 - (n+1))" by (metis add_diff_cancel_right' suma_def)
    then have "... = 2*(suma (n+1) (n+l) + n+l+1 - n -1)" using diff_diff_left by presburger
    then have "... = 2*(suma (n+1) (n+l) + l)" by auto
    then have "... = 2* suma (n+1) (n+l) + 2*l" by auto
    then have "... = l * (2 * n + l + 1) + 2*l" using Suc.IH by presburger
    then have "... = l * (2*n + l + 3)" by (metis One_nat_def Suc_1 add.commute add_Suc_shift add_mult_distrib2 mult.commute numeral_3_eq_3 plus_1_eq_Suc)
    then have "... = l*(2*n+2 + l+ 1)" by (metis One_nat_def Suc_1 Suc_eq_plus1 add.commute group_cancel.add1 numeral_3_eq_3)
    then have "... = l*(2*(n+1) + l+1)" by simp
    then show ?case using Suc_eq_plus1 ‹2 * (suma (n + 1) (n + l) + l) = 2 * suma (n + 1) (n + l) + 2 * l› ‹2 * (suma (n + 1) (n + l) + n + l + 1 - (n + 1)) = 2 * (suma (n + 1) (n + l) + n + l + 1 - n - 1)› ‹2 * (suma (n + 1) (n + l) + n + l + 1 - n - 1) = 2 * (suma (n + 1) (n + l) + l)› ‹2 * (suma' (n + l + 1) - suma' (n + 1)) = 2 * (suma' (n + l) + (n + l + 1) - suma' (n + 1))› ‹2 * (suma' (n + l) + (n + l + 1) - suma' (n + 1)) = 2 * (suma' (n + l) + n + l + 1 - (suma' n + n + 1))› ‹2 * (suma' (n + l) + n + l + 1 - (suma' n + n + 1)) = 2 * (suma' (n + l) + n + l + 1 - suma' n - (n + 1))› ‹2 * (suma' (n + l) + n + l + 1 - suma' n - (n + 1)) = 2 * (suma' (n + l) - suma' n + n + l + 1 - (n + 1))› ‹2 * (suma' (n + l) - suma' n + n + l + 1 - (n + 1)) = 2 * (suma (n + 1) (n + l) + n + l + 1 - (n + 1))› ‹2 * suma (Suc n + 1) (Suc n + l) = 2 * suma (n + 2) (n + l + 1)› ‹2 * suma (n + 1) (n + l) + 2 * l = l * (2 * n + l + 1) + 2 * l› ‹2 * suma (n + 2) (n + l + 1) = 2 * (suma' (n + l + 1) - suma' (n + 1))› ‹l * (2 * n + l + 1) + 2 * l = l * (2 * n + l + 3)› ‹l * (2 * n + l + 3) = l * (2 * n + 2 + l + 1)› by presburger
  qed
qed

lemma pom2_1:
  shows "(10 * n - 4) / 2 + 2 ≠ 5 * n ⟹ n = 2"
  sorry
(*proof-
  have "(10 * n - 4) / 2 = (10 * n) / 2 - 4 / 2" using diff_divide_distrib sorry
qed*)

lemma pom2_2:
  shows "5 * (n * (n - 2)) = n * (5 * n) - 10 * n"
  sorry
(*proof-
  have "5 * (n * (n - 2)) = 5 * n * (n-2)" by auto*)

lemma pom2_3:
  shows "16 * n + n * (n - 2) * 8 = 8 * (n * n)"
  sorry
(*proof-
  have "16 * n + n * (n - 2) * 8 = 16 * n + 8*n*(n-2)" by auto*)

lemma pom2:
  fixes n :: real
  assumes "n>0"
  shows "(n - 2) / 2 * (2 * n + (n - 2) / 2 + 1) / 2 =  5*n*(n-2)/8"
proof-
  have "(n - 2) / 2 * (2 * n + (n - 2) / 2 + 1) / 2 = (n - 2) * (2 * n + (n - 2) / 2 + 1) / 4" by auto
  then have "... = (n - 2) * ((4 * n + (n - 2)) / 2 + 1) / 4" by auto
  then have "... = (n - 2) * ((4 * n + (n - 2) + 2) / 2) / 4" using pom2_1 by auto
  then have "... = (n - 2) * (4 * n + (n - 2) + 2) / 8" by auto
  then have "... = (n * (4 * n + (n - 2) + 2) - 2 * (4 * n + (n - 2) + 2)) / 8" using int_distrib(3) diff_mult_distrib mult.commute pom2_2 by auto
  then have "... = ((n * 4 * n + n * (n - 2) + n*2) - 2 * (4 * n + (n - 2) + 2)) / 8" by auto
  then have "... = ((n * 4 * n + n * (n - 2) + n*2) - (2*4 * n + 2*(n - 2) + 4)) / 8" by auto
  then have "... = (n * 4 * n + n * (n - 2) + n*2 - 2*4 * n - 2*(n - 2) - 4) / 8" by auto
  then have "... = (n*4*n + n*n - 2*n + n*2 - 2*4 * n - 2*n + 2*2 - 4) / 8" using pom2_3 by auto
  then have "... = (4*n*n + n*n - 2*n + 2*n - 8 * n - 2*n + 4 - 4) / 8" by auto
  then have "... = (5*n*n - 10*n)/8" by auto
  then show ?thesis by (smt (z3) ‹(n - 2) * ((4 * n + (n - 2) + 2) / 2) / 4 = (n - 2) * (4 * n + (n - 2) + 2) / 8› ‹(n - 2) * ((4 * n + (n - 2)) / 2 + 1) / 4 = (n - 2) * ((4 * n + (n - 2) + 2) / 2) / 4› ‹(n - 2) * (2 * n + (n - 2) / 2 + 1) / 4 = (n - 2) * ((4 * n + (n - 2)) / 2 + 1) / 4› ‹(n - 2) / 2 * (2 * n + (n - 2) / 2 + 1) / 2 = (n - 2) * (2 * n + (n - 2) / 2 + 1) / 4› mult.commute)
qed

lemma resenje:
  assumes "je_resenje l"
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
  obtain "lp" where "lp = (if length l' > length l'' then l' else l'')" by auto

  obtain "i'" where "i'<i ∧ i'≥0"
    using ‹i < length l - 1 ∧ 0 < i› by blast
  obtain "j'" where "j' = i'+1" by auto
  obtain "ak" where "ak = l!i'" by auto
  obtain "bk" where "bk = l!j'" by auto
  with duzina_manje_je_bar_pola have "length lp ≥ ⌈(length l - 2) / 2⌉"
    using ‹i < length l - 1 ∧ 0 < i› ‹j = i + 1› ‹l' = sublist l 0 (i - 1)› ‹l'' = sublist l (j + 1) (length l - 1)› ‹lp = (if length l'' < length l' then l' else l'')› assms(2) by blast
  with this and an_mora_da_bude_suma_1_do_n have "bk ≥ suma ((length l)+1) ((length l)+(length lp))"
    sorry
  from ‹length lp ≥⌈(length l - 2) / 2⌉› have "2 * length lp ≥ (length l - 2)" by linarith

  have "2 * suma ((length l)+1) ((length l)+(length lp)) = (length lp)*(2*(length l) + (length lp) + 1)" using ‹length l = 10› ‹2 * length lp ≥ (length l - 2)› pom1
    by (metis zero_less_numeral)
  then have "suma (length l + 1) (length l + length lp) = ((length lp)*(2*(length l) + (length lp) + 1)) / 2" by linarith
  then have "bk≥((length lp)*(2*(length l) + (length lp) + 1)) / 2"
    using ‹int (suma (length l + 1) (length l + length lp)) ≤ bk› by linarith
  then have "... ≥ (length l - 2) / 2 *  (2 * length l + (length l - 2) / 2 + 1) div 2" using ‹length lp ≥ ⌈(length l - 2) / 2⌉› sorry
  then have "(length l - 2) / 2 *  (2 * length l + (length l - 2) / 2 + 1) / 2 =  5*(length l)*((length l)-2)/8" using pom2 by auto
  then have "... > 55" using ‹length l = 10› sorry (*ne vazi za 10 ali vazi za 2018*)

  have "bk≥ (length l - 2) / 2 *  (2 * length l + (length l - 2) / 2 + 1) div 2"
    using ‹real (length l - 2) / 2 * (real (2 * length l) + real (length l - 2) / 2 + 1) / 2 ≤ real_of_int bk› by blast
  then have "bk≥ 5*(length l)*((length l)-2)/8"
    using ‹real (length l - 2) / 2 * (real (2 * length l) + real (length l - 2) / 2 + 1) / 2 = real (5 * length l * (length l - 2)) / 8› sorry (*by presburger nalazi resenje sledgehammer ali ne prolazi*)
  then have "bk>55" using ‹length l = 10› ‹55 < real (5 * length l * (length l - 2)) / 8› by auto
  have "i<length l - 1" using ‹i<length l - 1 ∧ i>0› by auto
  then show ?thesis using ako_je_jedan_veci_od_sum_1_n_false ‹bk>55› ‹je_resenje l› ‹length l = 10› ‹i<length l - 1›
    by blast
qed

end