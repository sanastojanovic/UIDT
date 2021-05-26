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

fun red_gore :: "int list\<Rightarrow>int list" where
"red_gore [x,y] = [abs(x-y)]" |
"red_gore (x#y#xs) = red_gore (y#xs) @ [abs(x-y)]"

lemma len_vrednost_manje_len_x:
  shows "length (red_gore x) < length x"
  apply(induction x)
  sorry

(*function vrednost' :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"vrednost' x [] = []" |
"vrednost' x [y] = [y]" |
"vrednost' x y = x@(vrednost' (vrednost y) (vrednost y))"*)

function trougao' :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"trougao' l1 l2 =
  (if l2 = [] then []
  else if (length l2) = 1 then l2
  else l1@((trougao' (rev (red_gore l2)) (rev (red_gore l2)))))"
  by pat_completeness auto
  termination
  apply (relation "measure (\<lambda> (a, b). length b)")
    apply(auto simp add: len_vrednost_manje_len_x)
    done

fun trougao :: "int list \<Rightarrow>int list" where
"trougao x = x@(trougao' [] x)"

value "length []"
value "red_gore [2::int,4,9,6]"
value "red_gore [3::int,5,2]"
value "red_gore [3::int,2]"
value "trougao' [] [2::int,4,9,6]"
value "trougao [2::int,4,9,6]"


end
